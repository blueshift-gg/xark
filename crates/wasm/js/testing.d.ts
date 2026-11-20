import type { Address, Instruction, KeyPairSigner } from "@solana/kit";
import type { LiteSVM, TransactionMetadata } from "litesvm";

export * from "./testing/paths";

/** A fresh LiteSVM with each program (a `.so` path) at its address. */
export function vm(programs: Record<Address, string>): LiteSVM;

/** A new keypair holding `sol` SOL. */
export function funded(svm: LiteSVM, sol?: bigint): Promise<KeyPairSigner>;

/**
 * Sign `instructions` with `payer` (and any signers they name) and send them. Throws
 * with the program's logs if the transaction fails.
 */
export function send(svm: LiteSVM, payer: KeyPairSigner, ...instructions: Instruction[]): Promise<TransactionMetadata>;
