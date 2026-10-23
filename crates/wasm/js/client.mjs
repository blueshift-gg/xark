// What every client `xark client` generates shares: the `Field` type, `Proof`, and
// making a prover or verifier from a circuit's build output. A generated client
// adds its circuit's types and schema:
//
//   import { Zkyc } from "./zkyc"; // generated
//   const prover = await Zkyc.prover("/circuits/zkyc/");
//   const proof = prover.prove(inputs);
//   send(proof.toBytes());
//   // elsewhere
//   const verifier = await Zkyc.verifier(vkBytes);
//   verifier.verify(body, required); // true
//
// xark-wasm itself is this package's main module, loaded (and initialized, for the
// web build) the first time a prover or verifier is made.

const MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

/** This package's version. A client's `schema.json` must come from the same release. */
export const VERSION = "0.3.0";

/** Whether versions `a` and `b` are the same release: the same minor before 1.0, major after. */
function sameRelease(a, b) {
  const [am, an] = a.split(".").map(Number);
  const [bm, bn] = b.split(".").map(Number);
  return am === bm && (am > 0 || an === bn);
}

/**
 * A BN254 field element, checked when it's made: an integer in [0, p) from a
 * `bigint`, a safe integer, a decimal or `0x`-hex string, little-endian bytes, or
 * another `Field`.
 */
export class Field {
  static MODULUS = MODULUS;

  /** @param {Field | bigint | number | string | Uint8Array} x */
  constructor(x) {
    const v = fieldValue(x);
    if (v < 0n) throw new RangeError(`Field: ${v} is negative`);
    if (v >= MODULUS) throw new RangeError(`Field: ${v} is not below the field's modulus`);
    /** @readonly */
    this.value = v;
  }

  /** @param {Uint8Array} bytes  big-endian, at most 32 */
  static fromBeBytes(bytes) {
    return new Field(bytes.slice().reverse());
  }

  equals(other) {
    return this.value === new Field(other).value;
  }

  /** 32 little-endian bytes, as proofs have it. */
  toBytes() {
    const out = new Uint8Array(32);
    for (let i = 0, v = this.value; i < 32; i++, v >>= 8n) out[i] = Number(v & 0xffn);
    return out;
  }

  toString() {
    return this.value.toString();
  }

  toJSON() {
    return this.value.toString();
  }
}

function fieldValue(x) {
  if (typeof x === "bigint") return x;
  if (typeof x === "number") {
    if (!Number.isInteger(x)) throw new RangeError(`Field: ${x} is not an integer`);
    if (!Number.isSafeInteger(x)) throw new RangeError(`Field: ${x} is not a safe integer (pass a bigint)`);
    return BigInt(x);
  }
  if (typeof x === "string") {
    const s = x.trim();
    // As the Rust codec reads it: decimal, or 0x/0X hex.
    if (!/^(\d+|0[xX][0-9a-fA-F]+)$/.test(s)) {
      throw new SyntaxError(`Field: ${JSON.stringify(x)} is not a decimal or 0x-hex integer`);
    }
    return BigInt(s);
  }
  if (x instanceof Uint8Array) {
    if (x.length > 32) throw new RangeError(`Field: ${x.length} bytes; at most 32`);
    return x.reduceRight((v, b) => (v << 8n) | BigInt(b), 0n);
  }
  // A `Field`, from this module or another copy of it.
  if (typeof x === "object" && x !== null && typeof x.value === "bigint") return x.value;
  throw new TypeError(`Field: can't make a field element from ${x === null ? "null" : typeof x}`);
}

/** An input value the circuit's types refuse; `path` names it (`id.document`). */
export class InputError extends Error {
  constructor(message, path) {
    super(message);
    this.name = "InputError";
    this.path = path;
  }
}

/** Inputs that fail one of the circuit's checks; `site` is the statement. */
export class CheckFailed extends Error {
  constructor(message, site) {
    super(message);
    this.name = "CheckFailed";
    this.site = site;
  }
}

/** Run `f`, turning xark-wasm's named errors into the classes above. */
function typed(f) {
  try {
    return f();
  } catch (e) {
    if (e instanceof Error && e.name === "InputError") throw new InputError(e.message, e.path ?? "");
    if (e instanceof Error && e.name === "CheckFailed") throw new CheckFailed(e.message, e.site);
    throw e;
  }
}

/**
 * A proof and the public inputs it proves. `toBytes()` is the proof as an exported
 * Solana verifier (`xark export`) reads it; `toBytesCompressed()` is half the size.
 * A verifier takes either, with the public inputs it requires.
 */
export class Proof {
  #wasm;
  constructor(proofBytes, publicInputs, publicInputBytes, wasm) {
    /** The proof, compressed (`toBytesCompressed()`). */
    this.proofBytes = proofBytes;
    this.publicInputs = publicInputs;
    this.publicInputBytes = publicInputBytes;
    this.#wasm = wasm;
  }

  /** The proof in the on-chain format: 256 bytes, little-endian, `A` negated. */
  toBytes() {
    if (!this.#wasm) throw new Error("this Proof wasn't made by a prover: make it with one");
    return this.#wasm.solanaProof(this.proofBytes);
  }

  /** The proof compressed: 128 bytes (each point by `x` and a sign bit). */
  toBytesCompressed() {
    return this.proofBytes.slice();
  }
}

/**
 * JSON for xark-wasm: `bigint`s and `Field`s as decimal, a `Date` as its UTC day,
 * a `Uint8Array` as its list of bytes (little-endian, where it's an integer), a `Set`
 * as a list. A value that can't be sent (an invalid `Date`, a number past 2^53, a
 * `Map`) throws an `InputError` naming where it is.
 */
export function toJson(value) {
  return JSON.stringify(plain(value, ""));
}

/** `v`, at input path `path`, as plain JSON values. */
function plain(v, path) {
  const refuse = (why) => {
    throw new InputError(path ? `input \`${path}\`: ${why}` : why, path);
  };
  if (v instanceof Date) {
    if (Number.isNaN(v.getTime())) refuse("invalid Date");
    return v.toISOString().slice(0, 10);
  }
  if (typeof v === "bigint") return v.toString();
  // A number past 2^53 has already lost digits: refuse it rather than prove another.
  if (typeof v === "number" && !Number.isInteger(v)) refuse(`${v} is not an integer`);
  if (typeof v === "number" && !Number.isSafeInteger(v)) refuse(`${v} is not a safe integer (pass a bigint)`);
  if (v instanceof Uint8Array) return Array.from(v);
  if (v !== null && typeof v === "object" && typeof v.toJSON === "function") return v.toJSON();
  // A `Set` is a list (`new Set(["US", "GB"])` for a set of countries).
  if (Array.isArray(v) || v instanceof Set) return Array.from(v, (x, i) => plain(x, `${path}[${i}]`));
  // Objects that would otherwise go as `{}` (or as `{"0": …}`), not as what they hold.
  if (
    v instanceof Map ||
    v instanceof WeakMap ||
    v instanceof WeakSet ||
    v instanceof Promise ||
    v instanceof RegExp ||
    v instanceof ArrayBuffer ||
    ArrayBuffer.isView(v)
  ) {
    refuse(`a ${v.constructor.name} can't be sent${ArrayBuffer.isView(v) ? " (bytes are a Uint8Array)" : ""}`);
  }
  if (v !== null && typeof v === "object") {
    const out = {};
    for (const [k, x] of Object.entries(v)) {
      if (x !== undefined && typeof x !== "function") out[k] = plain(x, path ? `${path}.${k}` : k);
    }
    return out;
  }
  return v;
}

/** Hex (`0x` optional, as xark-wasm writes bytes) to bytes. Throws on anything else. */
export function fromHex(s) {
  if (typeof s !== "string") throw new TypeError(`fromHex: expected a string, got ${s === null ? "null" : typeof s}`);
  const h = s.startsWith("0x") || s.startsWith("0X") ? s.slice(2) : s;
  if (h.length % 2 !== 0 || !/^[0-9a-fA-F]*$/.test(h)) {
    throw new SyntaxError(`fromHex: ${JSON.stringify(s)} is not hex bytes`);
  }
  return Uint8Array.from({ length: h.length / 2 }, (_, i) => parseInt(h.slice(2 * i, 2 * i + 2), 16));
}

/** Bytes as `0x`-hex. */
export function toHex(bytes) {
  if (!(bytes instanceof Uint8Array)) throw new TypeError("toHex: expected a Uint8Array");
  return "0x" + Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

/** Each part of the build output as `xark build`, `xark setup` and `xark client` name its file. */
const FILES = {
  circuit: "circuit.xbc",
  provingKey: "pk.bin",
  verifyingKey: "vk.bin",
  sources: "sources.json",
  client: "client.wasm",
};
/** Parts a deployment may leave out. */
const OPTIONAL = new Set(["sources", "client"]);

/** Fetch `parts` of a build output served at `base`. */
async function fetchParts(base, parts, options = {}) {
  const page = globalThis.location?.href;
  if (!page && !URL.canParse(base)) {
    throw new Error(`${base} is relative, and there's no page to resolve it against; pass an absolute URL`);
  }
  const root = new URL(base, page);
  if (!root.pathname.endsWith("/")) root.pathname += "/";
  const out = {};
  await Promise.all(
    parts.map(async (part) => {
      const url = new URL(FILES[part], root);
      const res = await fetch(url, options.request);
      if (!res.ok) {
        if (OPTIONAL.has(part) && res.status === 404) return;
        throw new Error(`fetching ${url}: ${res.status} ${res.statusText}`);
      }
      out[part] = part === "sources" ? await res.text() : new Uint8Array(await res.arrayBuffer());
    }),
  );
  return out;
}

const isLocation = (x) => typeof x === "string" || x instanceof URL;

let loaded;
/** xark-wasm: `options.wasm`, or this package's build for the platform, initialized. */
function xarkWasm(options = {}) {
  if (options.wasm) return Promise.resolve(options.wasm);
  loaded ??= import("@blueshift-gg/xark-wasm").then(async (m) => {
    // The web build exports its `init` as the default; node and workerd need none.
    if (typeof m.default === "function") await m.default();
    return m;
  });
  return loaded;
}

/**
 * One circuit, as its generated client describes it: makes its provers and
 * verifiers, and runs its Rust functions (`client.wasm`).
 */
export class Circuit {
  /** @param {{ name: string, schema: object | string, decodePublic: (json: any) => any, client: boolean }} spec */
  constructor(spec) {
    // The xark that wrote the schema (from 0.3 on): this runtime must be its release.
    const made = (typeof spec.schema === "string" ? JSON.parse(spec.schema) : spec.schema).xark;
    if (typeof made === "string" && !sameRelease(made, VERSION)) {
      const release = made.split(".").slice(0, made.startsWith("0.") ? 2 : 1).join(".");
      throw new Error(
        `the ${spec.name} client was generated by xark ${made}, but @blueshift-gg/xark-wasm is ${VERSION}: ` +
          `install @blueshift-gg/xark-wasm@${release}, or regenerate the client with this xark's \`xark client\``,
      );
    }
    this.name = spec.name;
    // xark-wasm takes the schema as text: serialized once, here.
    this.schema = typeof spec.schema === "string" ? spec.schema : JSON.stringify(spec.schema);
    this.decodePublic = spec.decodePublic;
    this.hasClient = spec.client;
    /** The digest of the circuit the client was generated from (`xark build` prints it). */
    this.digest = spec.digest;
    this.rust = undefined;
    /** A URL a prover or verifier was made from that had no `client.wasm`. */
    this.missingAt = undefined;
  }

  async prover(from, options) {
    const wasm = await xarkWasm(options);
    const [parts] = await Promise.all([
      isLocation(from) ? fetchParts(from, ["circuit", "provingKey", "sources"], options) : from,
      isLocation(from) && clientFrom(this, from, options),
    ]);
    if (!parts.circuit || !parts.provingKey) {
      throw new Error(`a ${this.name} prover needs \`circuit\` (circuit.xbc) and \`provingKey\` (pk.bin)`);
    }
    // Pinned (`options.digest`): this exact circuit, and no other build output.
    if (options?.digest !== undefined) {
      const got = wasm.circuitDigest(parts.circuit);
      if (got !== options.digest) {
        throw new Error(
          `the ${this.name} circuit.xbc has digest ${got}, not the ${options.digest} this prover is pinned to: ` +
            `deploy the build output of that circuit (\`xark build\` prints its digest), or pin the new one`,
        );
      }
    }
    await loadClient(this, parts.client, from);
    return new Prover(this, wasm, parts);
  }

  async verifier(from, options) {
    const wasm = await xarkWasm(options);
    const [parts] = await Promise.all([
      isLocation(from)
        ? fetchParts(from, ["verifyingKey"], options)
        : from instanceof Uint8Array
          ? { verifyingKey: from }
          : from,
      isLocation(from) && clientFrom(this, from, options),
    ]);
    if (!parts.verifyingKey) throw new Error(`a ${this.name} verifier needs \`verifyingKey\` (vk.bin)`);
    // Pinned (`options.keyHash`): this exact verifying key, and no other.
    if (options?.keyHash !== undefined) {
      const got = wasm.sha256Hex(parts.verifyingKey);
      if (got !== options.keyHash.toLowerCase()) {
        throw new Error(
          `the ${this.name} verifying key has sha256 ${got}, not the ${options.keyHash} this verifier is pinned to: ` +
            `deploy the vk.bin of that setup (\`xark setup\` prints its sha256), or pin the new one`,
        );
      }
    }
    await loadClient(this, parts.client, from);
    return new Verifier(this, wasm, parts);
  }

  /** Load `client.wasm`, from a URL serving the build output or its bytes. */
  async ready(from, options) {
    let wasm = from;
    if (isLocation(from)) {
      wasm = (await fetchParts(from, ["client"], options)).client;
      if (!wasm) throw new Error(`no client.wasm at ${from}: run \`xark client\` and serve its output`);
    }
    const module = wasm instanceof WebAssembly.Module ? wasm : await WebAssembly.compile(wasm);
    this.rust = { module, instance: await WebAssembly.instantiate(module, {}) };
    this.missingAt = undefined;
  }

  /** Call one of the circuit's Rust functions with JSON arguments; its result, as JSON. */
  call(name, args) {
    const rust = this.rust;
    if (!rust && this.missingAt) {
      throw new Error(
        `${name} runs from client.wasm, and there was none at ${this.missingAt}: serve the client.wasm \`xark client\` wrote beside the other files`,
      );
    }
    if (!rust) {
      throw new Error(
        `${name} runs from client.wasm: load it first with the circuit's \`ready(url)\` (making a prover or verifier from a URL does it)`,
      );
    }
    const x = rust.instance.exports;
    if (typeof x[name] !== "function") {
      throw new Error(
        `client.wasm has no \`${name}\`: it's from another build of ${this.name}; serve the client.wasm \`xark client\` wrote with this client`,
      );
    }
    const input = new TextEncoder().encode(JSON.stringify(args.map((a, i) => plain(a, `argument ${i + 1}`))));
    const ptr = x.xark_alloc(input.length);
    new Uint8Array(x.memory.buffer, ptr, input.length).set(input);
    let packed;
    try {
      packed = x[name](ptr, input.length);
    } catch (e) {
      const message = take(x, x.xark_panic());
      rust.instance = new WebAssembly.Instance(rust.module, {}); // a panic may leave the heap mid-update
      throw new Error(message || String(e));
    }
    x.xark_free(ptr, input.length);
    const out = JSON.parse(take(x, packed));
    if ("err" in out) throw "path" in out ? new InputError(out.err, out.path) : new Error(out.err);
    return out.ok;
  }
}

/** Load the `client.wasm` a prover or verifier was made with; remember a URL that had none. */
async function loadClient(circuit, client, from) {
  if (client) return circuit.ready(client);
  if (circuit.hasClient && isLocation(from) && !circuit.rust) circuit.missingAt = String(from);
}

/**
 * Fetch and load `client.wasm` from the build output at `from`, unless the circuit
 * has it already or is fetching it (one download for all its provers and verifiers).
 */
function clientFrom(circuit, from, options) {
  if (!circuit.hasClient || circuit.rust) return;
  circuit.loading ??= fetchParts(from, ["client"], options)
    .then(({ client }) => client && circuit.ready(client))
    .finally(() => (circuit.loading = undefined));
  return circuit.loading;
}

/** The string a Rust function handed over (`ptr << 32 | len`), freed. */
function take(x, packed) {
  const ptr = Number(packed >> 32n);
  const len = Number(packed & 0xffffffffn);
  const s = new TextDecoder().decode(new Uint8Array(x.memory.buffer, ptr, len));
  x.xark_free(ptr, len);
  return s;
}

/** What provers and verifiers share: the public-input encoding, and reading proofs. */
class Session {
  constructor(circuit, wasm) {
    this.circuit = circuit;
    this.wasm = wasm;
    // The schema, parsed once.
    this.codec = new wasm.Schema(circuit.schema);
  }

  encodePublicInputs(publicInputs) {
    return typed(() => this.codec.encodePublicInputs(toJson(publicInputs)));
  }

  decodePublicInputs(bytes) {
    return this.circuit.decodePublic(JSON.parse(this.codec.decodePublicValues(bytes)));
  }

  fields(type, value) {
    return typed(() => this.codec.valueFields(type, toJson(value))).map((f) => new Field(f));
  }

  poseidon2(fields) {
    return new Field(this.wasm.poseidon2(fields.map(String)));
  }
}

export class Prover extends Session {
  constructor(circuit, wasm, parts) {
    super(circuit, wasm);
    this.parts = parts;
  }

  /**
   * Decode the proving key now and keep it, so each proof skips decoding it (about
   * half a small circuit's proving time). It takes about 2.2× `pk.bin` in memory:
   * without it, a proof streams the key and needs far less.
   */
  preload() {
    const { circuit, provingKey, sources } = this.parts;
    this.session ??= typed(() => new this.wasm.ProvingSession(circuit, provingKey, sources));
  }

  prove(inputs) {
    const { circuit, provingKey, sources } = this.parts;
    const { proof, publicInputs } = typed(() => {
      const encoded = this.codec.encodeInputs(toJson(inputs));
      return this.session ? this.session.prove(encoded) : this.wasm.prove(circuit, provingKey, encoded, sources);
    });
    return new Proof(proof.slice(), this.decodePublicInputs(publicInputs), publicInputs.slice(), this.wasm);
  }
}

export class Verifier extends Session {
  constructor(circuit, wasm, parts) {
    super(circuit, wasm);
    // Decoded once: a malformed key throws here, not as a `false` from every verify.
    this.key = new wasm.VerifyingKey(parts.verifyingKey);
  }

  verify(proof, publicInputs) {
    const bytes = proof instanceof Uint8Array ? proof : proof.proofBytes;
    if (proof instanceof Uint8Array && publicInputs === undefined) {
      throw new TypeError("verify(bytes, publicInputs): a proof's bytes don't carry its public inputs; pass the ones it must prove");
    }
    const inputs =
      publicInputs === undefined
        ? proof.publicInputBytes
        : publicInputs instanceof Uint8Array
          ? publicInputs
          : this.encodePublicInputs(publicInputs);
    try {
      return this.key.verify(bytes, inputs);
    } catch {
      return false; // a malformed proof
    }
  }
}
