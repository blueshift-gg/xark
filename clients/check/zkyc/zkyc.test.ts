// The generated `zkyc` client (`xark client`) through xark-wasm. `npm test` runs it,
// after setup.ts builds the example and its keys.
import { Circuit } from "@blueshift-gg/xark-wasm/client";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { artifacts, outDir, serve } from "../artifacts";
import schema from "./zkyc.schema.js";
import { CheckFailed, Country, Field, Identity, InputError, Policy, PolicyValue, Zkyc, ZkycProver, ZkycVerifier } from "./zkyc";

// Made from the build output, the prover also loads `client.wasm`: the Rust
// functions (`Policy.default`, `Identity.commitment`) work from then on.
let prover: ZkycProver;
let verifier: ZkycVerifier;
beforeAll(async () => {
  prover = await Zkyc.prover(artifacts("zkyc"));
  verifier = await Zkyc.verifier(artifacts("zkyc"));
});

// The holder's credential, in the circuit's own types: `Text`, `Date`, a `Country`.
// A `Date` is read as its UTC day: `new Date("1990-01-01")` is 1990-01-01 anywhere.
const id: Identity = {
  document: "A1938274",
  born: new Date("1990-01-01"),
  nationality: Country.US,
  netWorth: 1_000_000,
  expires: new Date("2030-01-01"),
  salt: new Field("33701741659145338741541800171033551611705418330992198479621539463087461139"),
};
// The issuer's Poseidon2 commitment over `id` (the Rust `id.commitment()`; see the
// test below, which computes it here).
const commitment = new Field(14027122776066679586866430602253390234316410519759139985776472857287265910584n);
// 18 or older on 2026-10-20, worth ≥ 500k, a document valid that day, from US/GB/FR/DE
// (as data; the test below builds it with the Rust constructors).
const policy: Policy = {
  today: new Date("2026-10-20"),
  bornBy: new Date("2008-10-20"),
  minNetWorth: 500_000,
  allowed: [Country.US, Country.GB, "FR", "DE"], // constants or names
};

test("builds the policy and the commitment with the circuit's Rust code", () => {
  // `Policy::default().on(..).min_age(..)…` and `Identity::commitment`, from `#[input] impl`: the
  // same chain as in Rust.
  const built = Policy.default().on(new Date("2026-10-20")).minAge(18).worthAtLeast(500_000).nationalities(["US", "GB", "FR", "DE"]);
  expect(built).toBeInstanceOf(PolicyValue);
  expect({ ...built }).toEqual({ ...policy, minNetWorth: 500_000n, allowed: ["DE", "FR", "GB", "US"] });
  expect(Policy.minAge(policy, 21).bornBy).toEqual(new Date("2005-10-20"));
  expect(Identity.commitment(id)).toEqual(commitment);
  const proof = prover.prove({ id, commitment: Identity.commitment(id), policy: built });
  expect(verifier.verify(proof, { commitment, policy: built })).toBe(true);
  // A Rust panic is an exception with its message, and the module keeps working.
  expect(() => built.minAge(3000)).toThrow(/a date before year 0/);
  expect(Policy.default().on(new Date("2024-02-29")).minAge(1).bornBy).toEqual(new Date("2023-02-28"));
  // The default policy passes everyone; `on` sets only the day, which a minimum age needs.
  expect({ ...Policy.default().on(new Date("2026-10-20")) }).toEqual({
    today: new Date("2026-10-20"),
    bornBy: new Date("9999-12-31"),
    minNetWorth: 0n,
    allowed: expect.arrayContaining(["US", "KP"]),
  });
  expect(() => Policy.default().minAge(18)).toThrow(/call `on\(today\)` first/);
  // Values are checked on the way in, as for `prove`.
  expect(() => Policy.default().on(new Date("2026-10-20")).nationalities(["XX" as Country])).toThrow(/"XX" is not a Country/);
});

test("countries are typed", () => {
  expect(Country.US).toBe("US");
  // @ts-expect-error: not an ISO 3166 code, so not a `Country` (tsc checks this line)
  const unknown: Country = "XX";
  expect(() => prover.prove({ id: { ...id, nationality: unknown }, commitment, policy })).toThrow(
    /"XX" is not a Country/,
  );
});

test("proves a compliant holder", () => {
  const proof = prover.prove({ id, commitment, policy });
  // Decoded, the policy has its Rust methods too.
  expect(proof.publicInputs.policy.minAge(21).bornBy).toEqual(new Date("2005-10-20"));
  expect(proof.publicInputs).toEqual({
    commitment,
    policy: {
      today: new Date("2026-10-20"),
      bornBy: new Date("2008-10-20"),
      minNetWorth: 500_000n,
      allowed: ["DE", "FR", "GB", "US"], // in bit order
    },
  });
  // A verifier checks the proof against the policy it requires: the proof's own
  // public inputs only say what it proves.
  const sent = proof.toBytes();
  expect(verifier.verify(sent, { commitment, policy })).toBe(true);
  expect(proof.publicInputs.policy.allowed).toEqual(["DE", "FR", "GB", "US"]);
  expect(verifier.verify(sent, { commitment, policy: { ...policy, allowed: ["US", "GB"] } })).toBe(false);
});

test("names the check a holder fails", () => {
  const fails = (rules: Partial<Policy>) => () =>
    prover.prove({ id, commitment, policy: { ...policy, ...rules } });
  expect(fails({ allowed: ["GB", "FR"] })).toThrow(
    /the inputs fail the check at src\/lib\.rs:\d+:\d+: `id\.nationality\.require_in\(policy\.allowed\);`/,
  );
  expect(fails({ bornBy: new Date("1989-12-31") })).toThrow(/`require\(id\.born <= policy\.born_by\);`/);
  expect(fails({ minNetWorth: 2_000_000 })).toThrow(/`require\(id\.net_worth >= policy\.min_net_worth\);`/);
  expect(() => prover.prove({ id, commitment: new Field(1), policy })).toThrow(
    /`require_eq\(id\.commitment\(\), commitment\);`/,
  );
  // A `CheckFailed`, whose `site` a UI can point at.
  const failure = (() => {
    try {
      fails({ allowed: ["GB", "FR"] })();
    } catch (e) {
      return e;
    }
  })();
  expect(failure).toBeInstanceOf(CheckFailed);
  expect((failure as CheckFailed).site).toMatchObject({
    file: "src/lib.rs",
    text: "id.nationality.require_in(policy.allowed);",
    chain: ["require_in"],
  });
  expect((failure as CheckFailed).site.line).toBeGreaterThan(0);
});

test("computes the issuer's commitment as the circuit does", () => {
  // `xark_poseidon2::hash(id.to_fields())`, the circuit's `id.commitment()`.
  const fields = prover.fields("Identity", id);
  expect(fields).toHaveLength(6);
  expect(prover.poseidon2(fields)).toEqual(commitment);
  // @ts-expect-error: `fields` takes the circuit's structs by name (tsc checks this line)
  expect(() => prover.fields("Nope", id)).toThrow();
});

test("names the input at fault", () => {
  const long = { ...id, document: "a document number past 31 bytes" + "!" };
  expect(() => prover.prove({ id: long, commitment, policy })).toThrow(/id\.document.*longer than 31 bytes/);
  // An `InputError`, whose `path` names the input.
  for (const [inputs, path] of [
    [{ id: long, commitment, policy }, "id.document"],
    [{ id, commitment, policy: { ...policy, allowed: ["XX" as Country] } }, "policy.allowed"],
    [{ id, commitment: -1, policy }, "commitment"],
  ] as const) {
    try {
      prover.prove(inputs);
      expect.unreachable();
    } catch (e) {
      expect(e).toBeInstanceOf(InputError);
      expect((e as InputError).path).toBe(path);
    }
  }
  // A value JS can't send names its path too, before it reaches the circuit.
  expect(() => prover.prove({ id, commitment, policy: { ...policy, today: new Date("not a day") } })).toThrow(
    expect.objectContaining({ name: "InputError", path: "policy.today" }),
  );
  // Paths use the names you wrote (`netWorth`), as do the circuit's Rust functions'.
  expect(() => prover.prove({ id: { ...id, netWorth: -1 }, commitment, policy })).toThrow(
    expect.objectContaining({ name: "InputError", path: "id.netWorth" }),
  );
  expect(() => Policy.default().on(new Date("2026-10-20")).nationalities(["XX" as Country])).toThrow(
    expect.objectContaining({ name: "InputError", path: "allowed" }),
  );
  expect(() => Policy.minAge({ ...policy, bornBy: new Date("x") }, 18)).toThrow(
    expect.objectContaining({ name: "InputError", path: "argument 1.bornBy" }),
  );
});

test("a verifier needs only the verifying key", async () => {
  const bare = await Zkyc.verifier(artifacts("zkyc").verifyingKey);
  expect(bare.verify(prover.prove({ id, commitment, policy }), { commitment, policy })).toBe(true);
});

test("ready() loads the Rust functions on their own", async () => {
  await expect(Zkyc.ready("http://127.0.0.1:1/")).rejects.toThrow();
  await Zkyc.ready(artifacts("zkyc").client!);
  expect(Identity.commitment(id)).toEqual(commitment);
  // A client.wasm from another build, without a function this client calls.
  expect(() => Zkyc.call("removed_since", [])).toThrow(/client.wasm has no `removed_since`/);
});

test("a Set goes as a list; a Map is refused", () => {
  // Plain JS (or `any`): a Set of countries is the policy's list.
  const allowed = new Set([Country.US, Country.GB, "FR", "DE"]) as unknown as Country[];
  const proof = prover.prove({ id, commitment, policy: { ...policy, allowed } });
  expect(verifier.verify(proof, { commitment, policy })).toBe(true);
  const map = new Map([["US", true]]) as unknown as Country[];
  expect(() => prover.prove({ id, commitment, policy: { ...policy, allowed: map } })).toThrow(
    expect.objectContaining({ name: "InputError", path: "policy.allowed", message: expect.stringMatching(/a Map can't be sent/) }),
  );
});

test("a URL without client.wasm says so when a Rust function is called", async () => {
  // A circuit of its own: the shared `Zkyc` has loaded client.wasm already.
  const circuit = new Circuit({ name: "zkyc", schema, decodePublic: (v) => v, client: true });
  const server = await serve("zkyc", ["client.wasm"]);
  try {
    await circuit.verifier(server.url);
    expect(() => circuit.call("Policy.default", [])).toThrow(/there was none at http:\/\/127\.0\.0\.1/);
  } finally {
    await server.close();
  }
});

test("a circuit fetches client.wasm once, for all its provers and verifiers", async () => {
  const circuit = new Circuit({ name: "zkyc", schema, decodePublic: (v) => v, client: true });
  const server = await serve("zkyc");
  try {
    await Promise.all([circuit.prover(server.url), circuit.verifier(server.url)]);
    await circuit.verifier(server.url);
    expect(server.requests.filter((r) => r === "client.wasm")).toHaveLength(1);
    expect(circuit.call("Policy.default", [])).toBeDefined();
  } finally {
    await server.close();
  }
});

test("a preloaded prover keeps its key decoded, and proves as before", async () => {
  const fast = await Zkyc.prover(artifacts("zkyc"));
  fast.preload();
  fast.preload(); // once is enough; again does nothing
  const proof = fast.prove({ id, commitment, policy });
  expect(verifier.verify(proof.toBytes(), { commitment, policy })).toBe(true);
  expect(proof.publicInputs).toEqual(prover.prove({ id, commitment, policy }).publicInputs);
  // A failed check still names its statement (the preloaded key keeps `sources.json`).
  expect(() => fast.prove({ id, commitment, policy: { ...policy, allowed: ["GB", "FR"] } })).toThrow(CheckFailed);
  expect(() => fast.prove({ id, commitment, policy: { ...policy, allowed: ["GB", "FR"] } })).toThrow(
    /`id\.nationality\.require_in\(policy\.allowed\);`/,
  );
});

test("a prover pinned to the client's circuit refuses another", async () => {
  // The digest of the circuit this client was generated from (`xark build` prints it).
  expect(Zkyc.digest).toMatch(/^[0-9a-f]{32}$/);
  const pinned = await Zkyc.prover(artifacts("zkyc"), { digest: Zkyc.digest });
  expect(verifier.verify(pinned.prove({ id, commitment, policy }), { commitment, policy })).toBe(true);
  await expect(Zkyc.prover(artifacts("zkyc"), { digest: "0".repeat(32) })).rejects.toThrow(
    new RegExp(`has digest ${Zkyc.digest}, not the 0{32} this prover is pinned to`),
  );
  // Not a circuit at all: said so, not a crash.
  const bogus = { ...artifacts("zkyc"), circuit: new Uint8Array([1, 2, 3]) };
  await expect(Zkyc.prover(bogus, { digest: Zkyc.digest })).rejects.toThrow(/not a circuit.xbc/);
});

test("a verifier pinned to a verifying key refuses another", async () => {
  // `xark setup` records the key's sha256 (and prints it).
  const meta = JSON.parse(readFileSync(join(outDir("zkyc"), "metadata.json"), "utf8"));
  const keyHash: string = meta.verifying_key_sha256;
  expect(keyHash).toMatch(/^[0-9a-f]{64}$/);
  const vk = artifacts("zkyc").verifyingKey;
  for (const pin of [keyHash, keyHash.toUpperCase()]) {
    const pinned = await Zkyc.verifier(vk, { keyHash: pin });
    expect(pinned.verify(prover.prove({ id, commitment, policy }), { commitment, policy })).toBe(true);
  }
  await expect(Zkyc.verifier(vk, { keyHash: "0".repeat(64) })).rejects.toThrow(
    new RegExp(`has sha256 ${keyHash}, not the 0{64} this verifier is pinned to`),
  );
});
