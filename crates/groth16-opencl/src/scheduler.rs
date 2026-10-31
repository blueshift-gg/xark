use std::collections::HashMap;
use std::sync::{Arc, Condvar, Mutex, OnceLock, Weak};

const DEFAULT_ACTIVE_JOBS: usize = 1;
const DEFAULT_QUEUED_JOBS: usize = 8;
const DEFAULT_MEMORY_PERCENT: usize = 75;
const DEFAULT_HOST_MEMORY_BYTES: usize = 256 * 1024 * 1024;

#[derive(Clone, Copy, Debug)]
struct SchedulerConfig {
    active_jobs: usize,
    queued_jobs: usize,
    memory_percent: usize,
    host_memory_bytes: usize,
}

impl SchedulerConfig {
    fn from_environment() -> Option<Self> {
        let active_jobs = parse_limit("XARK_OPENCL_MAX_ACTIVE_JOBS", DEFAULT_ACTIVE_JOBS, 64)?;
        let queued_jobs = parse_limit("XARK_OPENCL_MAX_QUEUED_JOBS", DEFAULT_QUEUED_JOBS, 1024)?;
        let memory_percent =
            parse_limit("XARK_OPENCL_MEMORY_PERCENT", DEFAULT_MEMORY_PERCENT, 100)?;
        let host_memory_bytes = parse_limit(
            "XARK_OPENCL_MAX_RESERVED_HOST_BYTES",
            DEFAULT_HOST_MEMORY_BYTES,
            usize::MAX,
        )?;
        if active_jobs == 0 || memory_percent == 0 || host_memory_bytes == 0 {
            return None;
        }
        Some(Self {
            active_jobs,
            queued_jobs,
            memory_percent,
            host_memory_bytes,
        })
    }
}

fn parse_limit(name: &str, default: usize, max: usize) -> Option<usize> {
    let value = std::env::var_os(name);
    parse_limit_value(
        value.as_deref().and_then(|value| value.to_str()),
        default,
        max,
    )
}

fn parse_limit_value(value: Option<&str>, default: usize, max: usize) -> Option<usize> {
    let Some(value) = value else {
        return Some(default);
    };
    let value = value.parse::<usize>().ok()?;
    (value <= max).then_some(value)
}

#[derive(Default)]
struct State {
    active_jobs: usize,
    active_bytes: usize,
    reserved_host_bytes: usize,
    queued_jobs: usize,
    next_ticket: u64,
    serving_ticket: u64,
}

pub(super) struct DeviceScheduler {
    max_active_jobs: usize,
    max_queued_jobs: usize,
    memory_budget_bytes: usize,
    host_memory_budget_bytes: usize,
    state: Mutex<State>,
    changed: Condvar,
}

impl DeviceScheduler {
    fn new(global_memory_bytes: usize, config: SchedulerConfig) -> Option<Self> {
        let memory_budget_bytes = global_memory_bytes
            .checked_div(100)?
            .checked_mul(config.memory_percent)?;
        (memory_budget_bytes > 0).then_some(Self {
            max_active_jobs: config.active_jobs,
            max_queued_jobs: config.queued_jobs,
            memory_budget_bytes,
            host_memory_budget_bytes: config.host_memory_bytes,
            state: Mutex::new(State::default()),
            changed: Condvar::new(),
        })
    }

    pub(super) fn memory_budget_bytes(&self) -> usize {
        self.memory_budget_bytes
    }

    pub(super) fn acquire(
        self: &Arc<Self>,
        device_bytes: usize,
        host_bytes: usize,
    ) -> Option<DevicePermit> {
        if device_bytes == 0
            || device_bytes > self.memory_budget_bytes
            || host_bytes > self.host_memory_budget_bytes
        {
            return None;
        }
        let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
        let reserved_host_bytes = state.reserved_host_bytes.checked_add(host_bytes)?;
        if reserved_host_bytes > self.host_memory_budget_bytes {
            return None;
        }
        if state.active_jobs < self.max_active_jobs
            && state.active_bytes.checked_add(device_bytes)? <= self.memory_budget_bytes
            && state.queued_jobs == 0
        {
            state.active_jobs += 1;
            state.active_bytes += device_bytes;
            state.reserved_host_bytes = reserved_host_bytes;
            return Some(DevicePermit {
                scheduler: Arc::clone(self),
                device_bytes,
                host_bytes,
            });
        }
        if state.queued_jobs >= self.max_queued_jobs {
            return None;
        }
        let ticket = state.next_ticket;
        state.next_ticket = state.next_ticket.wrapping_add(1);
        state.queued_jobs += 1;
        state.reserved_host_bytes = reserved_host_bytes;
        loop {
            if ticket == state.serving_ticket
                && state.active_jobs < self.max_active_jobs
                && state
                    .active_bytes
                    .checked_add(device_bytes)
                    .is_some_and(|total| total <= self.memory_budget_bytes)
            {
                state.queued_jobs -= 1;
                state.serving_ticket = state.serving_ticket.wrapping_add(1);
                state.active_jobs += 1;
                state.active_bytes += device_bytes;
                self.changed.notify_all();
                return Some(DevicePermit {
                    scheduler: Arc::clone(self),
                    device_bytes,
                    host_bytes,
                });
            }
            state = self
                .changed
                .wait(state)
                .unwrap_or_else(|error| error.into_inner());
        }
    }
}

pub(super) struct DevicePermit {
    scheduler: Arc<DeviceScheduler>,
    device_bytes: usize,
    host_bytes: usize,
}

impl Drop for DevicePermit {
    fn drop(&mut self) {
        let mut state = self
            .scheduler
            .state
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        state.active_jobs -= 1;
        state.active_bytes -= self.device_bytes;
        state.reserved_host_bytes -= self.host_bytes;
        self.scheduler.changed.notify_all();
    }
}

static SCHEDULERS: OnceLock<Mutex<HashMap<usize, Weak<DeviceScheduler>>>> = OnceLock::new();

pub(super) fn for_device(
    device_id: usize,
    global_memory_bytes: usize,
) -> Option<Arc<DeviceScheduler>> {
    let config = SchedulerConfig::from_environment()?;
    let schedulers = SCHEDULERS.get_or_init(|| Mutex::new(HashMap::new()));
    let mut schedulers = schedulers.lock().unwrap_or_else(|error| error.into_inner());
    if let Some(scheduler) = schedulers.get(&device_id).and_then(Weak::upgrade) {
        return Some(scheduler);
    }
    let scheduler = Arc::new(DeviceScheduler::new(global_memory_bytes, config)?);
    schedulers.insert(device_id, Arc::downgrade(&scheduler));
    Some(scheduler)
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc;
    use std::time::Duration;

    use super::*;

    fn scheduler(
        active_jobs: usize,
        queued_jobs: usize,
        device_budget: usize,
        host_budget: usize,
    ) -> Arc<DeviceScheduler> {
        Arc::new(DeviceScheduler {
            max_active_jobs: active_jobs,
            max_queued_jobs: queued_jobs,
            memory_budget_bytes: device_budget,
            host_memory_budget_bytes: host_budget,
            state: Mutex::new(State::default()),
            changed: Condvar::new(),
        })
    }

    #[test]
    fn rejects_chunks_that_exceed_the_device_memory_budget() {
        let scheduler = scheduler(1, 2, 1024, 2048);
        assert!(scheduler.acquire(1025, 1).is_none());
        assert!(scheduler.acquire(1024, 2049).is_none());
        let permit = scheduler.acquire(1024, 1024).unwrap();
        drop(permit);
        let state = scheduler.state.lock().unwrap();
        assert_eq!(state.active_bytes, 0);
        assert_eq!(state.reserved_host_bytes, 0);
    }

    #[test]
    fn serializes_jobs_and_releases_the_next_fifo_waiter() {
        let scheduler = scheduler(1, 1, 4096, 4096);
        let first = scheduler.acquire(1024, 1024).unwrap();
        let worker_scheduler = Arc::clone(&scheduler);
        let (started, started_rx) = mpsc::channel();
        let (acquired, acquired_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            started.send(()).unwrap();
            let permit = worker_scheduler.acquire(1024, 1024).unwrap();
            acquired.send(()).unwrap();
            drop(permit);
        });
        started_rx.recv_timeout(Duration::from_secs(1)).unwrap();
        let deadline = std::time::Instant::now() + Duration::from_secs(1);
        while scheduler.state.lock().unwrap().queued_jobs == 0 {
            assert!(std::time::Instant::now() < deadline, "waiter did not queue");
            std::thread::yield_now();
        }
        assert!(acquired_rx.try_recv().is_err());
        assert!(scheduler.acquire(512, 512).is_none());
        drop(first);
        acquired_rx.recv_timeout(Duration::from_secs(1)).unwrap();
        worker.join().unwrap();
        let state = scheduler.state.lock().unwrap();
        assert_eq!(state.active_jobs, 0);
        assert_eq!(state.active_bytes, 0);
        assert_eq!(state.reserved_host_bytes, 0);
        assert_eq!(state.queued_jobs, 0);
    }

    #[test]
    fn declines_when_the_bounded_wait_queue_has_no_capacity() {
        let scheduler = scheduler(1, 0, 4096, 4096);
        let _permit = scheduler.acquire(1024, 1024).unwrap();
        assert!(scheduler.acquire(1024, 1024).is_none());
    }

    #[test]
    fn parses_scheduler_limits_and_rejects_invalid_values() {
        assert_eq!(parse_limit_value(None, 8, 1024), Some(8));
        assert_eq!(parse_limit_value(Some("16"), 8, 1024), Some(16));
        assert_eq!(parse_limit_value(Some("0"), 8, 1024), Some(0));
        assert_eq!(parse_limit_value(Some("1025"), 8, 1024), None);
        assert_eq!(parse_limit_value(Some("many"), 8, 1024), None);
    }

    #[test]
    fn host_reservation_caps_active_and_waiting_chunks_together() {
        let scheduler = scheduler(1, 1, 4096, 2048);
        let _first = scheduler.acquire(512, 1024).unwrap();
        assert!(scheduler.acquire(512, 1025).is_none());
        assert_eq!(scheduler.state.lock().unwrap().reserved_host_bytes, 1024);
    }
}
