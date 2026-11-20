/** The project `from` is in: the nearest directory with a `xark.toml`. */
export function projectRoot(from?: string): string;

/** A circuit's build output, as a prover takes it. */
export interface Artifacts {
  circuit: Uint8Array;
  provingKey: Uint8Array;
  verifyingKey: Uint8Array;
  sources: string;
  /** `client.wasm`: the circuit's Rust functions, when it has some. */
  client?: Uint8Array;
}

/** A build output directory (`target/xark/<name>/`), with the keys in `keys` (by default the same directory). */
export function artifacts(dir: string, keys?: string): Artifacts;

/** Circuit `name`'s build output (`circuits/<name>/target/xark/<name>/`) and keys (`keys/<name>/`) in the project. */
export function circuit(name: string, root?: string): Artifacts;

/** Options for locating a program artifact. */
export interface ProgramOptions {
  /** Project root. Default: `projectRoot()`. */
  root?: string;
  /** Directory under the root. Default: `target/deploy`. */
  dir?: string;
  /** Artifact file name. Default: `<name>_program.so`. */
  file?: string;
}

/** Program `name`'s artifact: `target/deploy/<name>_program.so` in the project. */
export function program(name: string, root?: string): string;
export function program(name: string, options?: ProgramOptions): string;
