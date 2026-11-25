//! A one-line spinner for a long, normally silent step (the quiet `cargo`
//! builds of a circuit or its client functions). One glyph, its color running
//! through the brand's gradient.

use std::io::{self, IsTerminal, Write};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// The rotating glyphs: braille, which monospace fonts have.
const GLYPHS: [&str; 10] = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];

const CLEAR_LINE: &str = "\r\x1b[2K";

/// The gradient's ends: the brand's neon green, and the dark green it dims to
/// and comes back from.
const BRAND: (u8, u8, u8) = (153, 255, 0);
const DARK: (u8, u8, u8) = (46, 110, 0);

/// The color breathes over two glyph rotations, so it is a slow pulse rather
/// than a flicker tied to the glyph.
const COLOR_FRAMES: usize = GLYPHS.len() * 2;

/// A spinner saying `message`; silent when stderr isn't a terminal, or is a dumb
/// one.
pub struct Spinner {
    stop: Arc<AtomicBool>,
    handle: Option<JoinHandle<()>>,
}

impl Spinner {
    pub fn start(message: impl Into<String>) -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let dumb = console::is_dumb();
        if !io::stderr().is_terminal() || dumb {
            return Self { stop, handle: None };
        }
        let message = crate::style::brand(&message.into());
        let stop_thread = Arc::clone(&stop);
        let handle = thread::Builder::new()
            .name("xark-spinner".into())
            .spawn(move || {
                // A cache-hit build finishes in a blink: don't flash a line for it.
                thread::park_timeout(Duration::from_millis(120));
                let mut frame = 0;
                let mut drew = false;
                while !stop_thread.load(Ordering::Relaxed) {
                    {
                        let mut err = io::stderr().lock();
                        let _ = write!(err, "{CLEAR_LINE}  {}", line(frame, &message));
                        let _ = err.flush();
                    }
                    drew = true;
                    frame += 1;
                    thread::park_timeout(Duration::from_millis(50));
                }
                // A step that ended inside the grace period drew nothing: clearing
                // the line would erase whatever another writer printed meanwhile.
                if drew {
                    let mut err = io::stderr().lock();
                    let _ = write!(err, "{CLEAR_LINE}");
                    let _ = err.flush();
                }
            })
            .ok();
        Self { stop, handle }
    }
}

impl Drop for Spinner {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        if let Some(handle) = &self.handle {
            // Wake it from `park_timeout` so a finished step doesn't wait out
            // the frame interval before its next line prints.
            handle.thread().unpark();
        }
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }
}

/// One frame: `frame`'s glyph tinted with its place on the gradient, then the
/// message (already styled). Without color it is the plain glyph.
fn line(frame: usize, message: &str) -> String {
    let glyph = GLYPHS[frame % GLYPHS.len()];
    if !crate::style::enabled() {
        return format!("{glyph} {message}");
    }
    let (r, g, b) = color(frame);
    format!("\x1b[38;2;{r};{g};{b}m{glyph}\x1b[0m {message}")
}

/// The frame's color: a cosine dim from the brand down to the dark green and
/// back, so the ends meet where the cycle repeats.
fn color(frame: usize) -> (u8, u8, u8) {
    let phase = (frame % COLOR_FRAMES) as f32 / COLOR_FRAMES as f32 * std::f32::consts::TAU;
    let t = (1.0 - phase.cos()) / 2.0;
    let channel = |a: u8, b: u8| (a as f32 + (b as f32 - a as f32) * t).round() as u8;
    (
        channel(BRAND.0, DARK.0),
        channel(BRAND.1, DARK.1),
        channel(BRAND.2, DARK.2),
    )
}

#[cfg(test)]
mod tests {
    use super::{BRAND, COLOR_FRAMES, DARK, color, line};

    #[test]
    fn the_color_dims_from_the_brand_to_dark_green_and_back() {
        assert_eq!(color(0), BRAND);
        assert_eq!(color(COLOR_FRAMES / 2), DARK);
        assert_eq!(color(COLOR_FRAMES), BRAND);
        let frame = line(0, "working");
        assert!(frame.contains("working"));
        if crate::style::enabled() {
            assert!(frame.contains("\x1b[38;2;153;255;0m"), "{frame:?}");
        }
    }
}
