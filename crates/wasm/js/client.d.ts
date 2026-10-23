/** This package's version. A client's `schema.json` must come from the same release. */
export const VERSION: string;

/**
 * A BN254 field element, checked when it's made: `new Field(x)` takes a `bigint`,
 * a safe integer, a decimal or `0x`-hex string, little-endian bytes (a `Uint8Array`
 * of at most 32, as proofs and Rust's `Field::from_le_bytes` have them), or another
 * `Field`, and throws unless it's an integer in [0, p).
 */
export class Field {
  /** The field's modulus, p (BN254's scalar field). */
  static readonly MODULUS: bigint;
  /** The element, in [0, p). */
  readonly value: bigint;
  constructor(x: Field | bigint | number | string | Uint8Array);
  /** From big-endian bytes (at most 32), as some outside formats have them. */
  static fromBeBytes(bytes: Uint8Array): Field;
  /** Whether `other` is the same element. */
  equals(other: Field | bigint | number | string | Uint8Array): boolean;
  /** The element as 32 little-endian bytes, as proofs have it. */
  toBytes(): Uint8Array;
  /** Decimal. */
  toString(): string;
  toJSON(): string;
}

/**
 * A value as JSON from xark-wasm or `client.wasm`: a `Field`, `bigint`, `Date` or
 * bytes as a string (decimal, `YYYY-MM-DD`, `0x`-hex), the rest as they are.
 */
export type Json<T> = T extends Field | bigint | Date | Uint8Array
  ? string
  : T extends readonly unknown[]
    ? { [K in keyof T]: Json<T[K]> }
    : T extends object
      ? { [K in keyof T as T[K] extends (...args: never[]) => unknown ? never : K]: Json<T[K]> }
      : T;

/** An input value the circuit's types refuse. */
export class InputError extends Error {
  /** The input at fault (`id.document`), or empty for the inputs as a whole. */
  readonly path: string;
  constructor(message: string, path: string);
}

/** Where a check is in the circuit's source. */
export interface Site {
  /** `src/lib.rs`. */
  file: string;
  line: number;
  col: number;
  /** The statement, trimmed. */
  text: string;
  /** The functions it called into, outermost first. */
  chain: string[];
}

/** Inputs that fail one of the circuit's checks (when the prover has `sources`). */
export class CheckFailed extends Error {
  readonly site: Site;
  constructor(message: string, site: Site);
}

/**
 * A calendar day: the `Date`'s UTC day, as `toISOString()` shows it
 * (`new Date("1990-01-01")` is 1990-01-01 anywhere). xark's `Date`.
 */
export type Day = Date;
/** A string of at most 31 UTF-8 bytes. xark's `Text`. */
export type Text = string;
/** An integer in [0, 2^8): Rust's `u8`. */
export type U8 = number;
/** An integer in [0, 2^16): Rust's `u16`. */
export type U16 = number;
/** An integer in [0, 2^32): Rust's `u32`. */
export type U32 = number;
/** An integer in [0, 2^64): Rust's `u64`. A `number` must be a safe integer. */
export type U64 = bigint | number;
/** An integer in [0, 2^128): Rust's `u128`. A `number` must be a safe integer. */
export type U128 = bigint | number;

/**
 * A field input: a `Field`, or a plain integer (a `bigint`, a safe integer, a
 * decimal or `0x`-hex string), checked as `new Field(x)` checks it.
 */
export type FieldInput = Field | bigint | number | string;

/**
 * A proof and the public inputs it proves. Send `toBytes()` (or the smaller
 * `toBytesCompressed()`) with the public inputs a verifier checks it against;
 * an exported Solana verifier reads `toBytes()` as it is.
 */
export class Proof<PublicValues> {
  /** The Groth16 proof, compressed (`toBytesCompressed()`). */
  readonly proofBytes: Uint8Array;
  /** The public inputs, decoded. */
  readonly publicInputs: PublicValues;
  /** The public inputs as their canonical bytes (`public_inputs.bin`). */
  readonly publicInputBytes: Uint8Array;
  constructor(proofBytes: Uint8Array, publicInputs: PublicValues, publicInputBytes: Uint8Array);
  /**
   * The proof as an exported Solana verifier (`xark export`) reads it, e.g. with
   * `Proof::from_le_bytes`: 256 bytes, little-endian, `A` negated. A `Verifier`
   * reads it too. Throws for a `Proof` not made by a prover.
   */
  toBytes(): Uint8Array;
  /** The proof compressed, 128 bytes (each point by `x` and a sign bit): a `Verifier` reads it. */
  toBytesCompressed(): Uint8Array;
}

/** The parts of `@blueshift-gg/xark-wasm` a client uses (any of its builds). */
export interface Wasm {
  prove(circuit: Uint8Array, provingKey: Uint8Array, inputs: Record<string, string>, sources?: string): { proof: Uint8Array; publicInputs: Uint8Array };
  /** A circuit and its proving key, decoded once, for many proofs (`Prover.preload`). */
  ProvingSession: new (circuit: Uint8Array, provingKey: Uint8Array, sources?: string) => {
    prove(inputs: Record<string, string>): { proof: Uint8Array; publicInputs: Uint8Array };
  };
  /** A circuit's `schema.json`, parsed once. */
  Schema: new (schema: string) => {
    encodeInputs(inputs: string): Record<string, string>;
    encodePublicInputs(publicInputs: string): Uint8Array;
    decodePublicValues(publicInputs: Uint8Array): string;
    valueFields(typeName: string, value: string): string[];
  };
  /** `vk.bin`, decoded once (throws if malformed). */
  VerifyingKey: new (bytes: Uint8Array) => {
    verify(proof: Uint8Array, publicInputs: Uint8Array): boolean;
  };
  poseidon2(inputs: string[]): string;
  /** The circuit digest of a `circuit.xbc` (what `xark build` prints). */
  circuitDigest(circuit: Uint8Array): string;
  /** A proof (either form) as an exported Solana verifier reads it (256 bytes). */
  solanaProof(proof: Uint8Array): Uint8Array;
  /** Lowercase hex SHA-256 of `bytes`. */
  sha256Hex(bytes: Uint8Array): string;
}

/** `client.wasm`, the circuit's Rust functions: its bytes, or the compiled module. */
export type ClientWasm = BufferSource | WebAssembly.Module;

/** The build output proving needs (`target/xark/<circuit>/`). */
export interface ProverArtifacts {
  /** `circuit.xbc`. */
  circuit: Uint8Array;
  /** `pk.bin`. */
  provingKey: Uint8Array;
  /** `sources.json`, as text: inputs that fail a check name its source line. */
  sources?: string;
  /** `client.wasm`, for the circuit's Rust functions. */
  client?: ClientWasm;
}

/** The build output verifying needs. */
export interface VerifierArtifacts {
  /** `vk.bin`. */
  verifyingKey: Uint8Array;
  /** `client.wasm`, for the circuit's Rust functions. */
  client?: ClientWasm;
}

export interface LoadOptions {
  /** Passed to each `fetch`. */
  request?: RequestInit;
  /**
   * The xark-wasm module to use, initialized. By default it's this package's
   * build for the platform (node, web, workerd), loaded the first time.
   */
  wasm?: Wasm;
  /**
   * A prover only: the circuit digest its `circuit.xbc` must have (what `xark build`
   * prints; the generated client's `digest` is the one it was generated from).
   * Another circuit is refused, so a deployment can't swap the circuit under an app.
   * Every build of one circuit has the same digest, whichever Rust compiled it.
   * Checking costs one pass over the circuit when the prover is made (about 2 s for
   * Ed25519 in node), not per proof.
   */
  digest?: string;
  /**
   * A verifier only: the sha256 its `vk.bin` must have (`xark setup` prints it, and
   * `metadata.json` records it as `verifying_key_sha256`). Another key is refused,
   * so a deployment can't swap the key under an app.
   */
  keyHash?: string;
}

/** What provers and verifiers share. */
export class Session<PublicInputs, PublicValues, Structs> {
  /** The public inputs as their canonical bytes (`public_inputs.bin`). */
  encodePublicInputs(publicInputs: PublicInputs): Uint8Array;
  /** Canonical public-input bytes, decoded. */
  decodePublicInputs(bytes: Uint8Array): PublicValues;
  /**
   * A value's field elements in input order, as `to_fields()` gives them in Rust:
   * hash them as the circuit does with `poseidon2`.
   */
  fields<K extends keyof Structs & string>(type: K, value: Structs[K]): Field[];
  /** `xark_poseidon2::hash`, as the circuit computes it. */
  poseidon2(fields: readonly Field[]): Field;
}

/** Proves a circuit: from `circuit.prover(…)`. */
export class Prover<Inputs, PublicInputs, PublicValues, Structs = {}> extends Session<PublicInputs, PublicValues, Structs> {
  private constructor();
  /**
   * Decode the proving key now and keep it, so each proof skips decoding it (about
   * half a small circuit's proving time). It takes about 2.2× `pk.bin` in memory:
   * without it, a proof streams the key and needs far less. Calling it again does nothing.
   */
  preload(): void;
  /**
   * Prove `inputs`. Throws an `InputError` if one is malformed (its `path` naming
   * it), or a `CheckFailed` if they fail a check (its `site` the statement, when
   * `sources` was given).
   */
  prove(inputs: Inputs): Proof<PublicValues>;
}

/** Verifies a circuit's proofs: from `circuit.verifier(…)`. */
export class Verifier<PublicInputs, PublicValues, Structs = {}> extends Session<PublicInputs, PublicValues, Structs> {
  private constructor();
  /**
   * Whether `proof` proves `publicInputs`: pass the ones you require (a policy, a
   * root). A proof's bytes (`toBytes()` or `toBytesCompressed()`) need them; a
   * `Proof` defaults to its own. A malformed or invalid proof is `false`;
   * `publicInputs` that don't fit the circuit's types throw an `InputError` (a
   * mistake in the caller, not a bad proof).
   */
  verify(proof: Proof<PublicValues>, publicInputs?: PublicInputs | Uint8Array): boolean;
  verify(proof: Uint8Array, publicInputs: PublicInputs | Uint8Array): boolean;
}

/** A circuit as its generated client describes it. */
export interface CircuitSpec<PublicValues> {
  /** The circuit's name (`zkyc`). */
  name: string;
  /** Its `schema.json`: the parsed object (as the generated client imports it), or its text. */
  schema: object | string;
  /** Revives decoded public inputs (dates, fields, bytes) from xark-wasm's JSON. */
  decodePublic(json: Json<PublicValues>): PublicValues;
  /** Whether it has Rust functions (`client.wasm`). */
  client: boolean;
  /** The digest of the circuit it was generated from (`xark build` prints it). */
  digest?: string;
}

/**
 * One circuit: makes its provers and verifiers. Throws if its schema was written by
 * another xark release than this runtime's (another minor version before 1.0).
 *
 * Makes them from a URL serving a copy of its
 * build output (`target/xark/<circuit>/`, relative to the page in a browser) or
 * from the bytes. Made from a URL, either also loads `client.wasm` when the
 * circuit has Rust functions; a missing `sources.json` or `client.wasm` is skipped.
 */
export class Circuit<Inputs, PublicInputs, PublicValues, Structs = {}> {
  constructor(spec: CircuitSpec<PublicValues>);
  /** The circuit's name. */
  readonly name: string;
  /** The circuit's `schema.json`, as text. */
  readonly schema: string;
  /**
   * The digest of the circuit this client was generated from: pin a prover to it
   * with `prover(from, { digest: Circuit.digest })`.
   */
  readonly digest: string | undefined;
  prover(
    from: string | URL | ProverArtifacts,
    options?: LoadOptions,
  ): Promise<Prover<Inputs, PublicInputs, PublicValues, Structs>>;
  /** `from` may also be `vk.bin`'s bytes. */
  verifier(
    from: string | URL | Uint8Array | VerifierArtifacts,
    options?: LoadOptions,
  ): Promise<Verifier<PublicInputs, PublicValues, Structs>>;
  /**
   * Load `client.wasm`, the circuit's Rust functions, from a URL serving the build
   * output or from its bytes. Making a prover or verifier from a URL does it; call
   * this to use the functions before, or without, either.
   */
  ready(from: string | URL | ClientWasm, options?: LoadOptions): Promise<void>;
  /**
   * Run one of the circuit's Rust functions (the generated client calls it): its
   * result as JSON, `R` being the `Json<…>` of the function's return type.
   */
  call<R>(name: string, args: unknown[]): R;
}

/** JSON for xark-wasm (the generated client calls it). */
export function toJson(value: unknown): string;
/** Hex (`0x` optional) to bytes, for a byte input given as hex. Throws on anything else. */
export function fromHex(s: string): Uint8Array;
/** Bytes as `0x`-hex. */
export function toHex(bytes: Uint8Array): string;
