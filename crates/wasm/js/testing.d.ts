import type { Address, Instruction, KeyPairSigner } from "@solana/kit";
import type { LiteSVM, TransactionMetadata } from "litesvm";

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

/** A build output directory (`target/xark/<name>/`). */
export function artifacts(dir: string): Artifacts;

/** Circuit `name`'s build output: `circuits/<name>/target/xark/<name>/` in the project. */
export function circuit(name: string, root?: string): Artifacts;

/** Program `name`'s build: `target/deploy/<name>_program.so` in the project. */
export function program(name: string, root?: string): string;

/** A fresh LiteSVM with each program (a `.so` path) at its address. */
export function vm(programs: Record<Address, string>): LiteSVM;

/** A new keypair holding `sol` SOL. */
export function funded(svm: LiteSVM, sol?: bigint): Promise<KeyPairSigner>;

/**
 * Sign `instructions` with `payer` (and any signers they name) and send them. Throws
 * with the program's logs if the transaction fails.
 */
export function send(svm: LiteSVM, payer: KeyPairSigner, ...instructions: Instruction[]): Promise<TransactionMetadata>;
