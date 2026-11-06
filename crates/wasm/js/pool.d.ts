export interface PoolOptions {
  /** Worker count (default: hardware concurrency). */
  threads?: number;
  /** FFT column-block width (default 4, the fastest measured). */
  tile?: number;
  /** Node: path to the nodejs glue; browser: URL of the web glue module. */
  wasm?: string;
}
export interface WorkerPool {
  readonly threads: number;
  readonly stats: { fftCalls: number; msmCalls: number; fftMs: number; msmMs: number };
  terminate(): Promise<void>;
}
/** SharedArrayBuffer + Atomics available (browsers: cross-origin isolated). */
export function parallelSupported(): boolean;
export function createPool(options?: PoolOptions): Promise<WorkerPool>;
