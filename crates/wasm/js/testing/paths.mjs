import { existsSync, readFileSync } from "node:fs";
import { dirname, isAbsolute, join, relative, resolve, sep } from "node:path";

/** The project `from` is in: the nearest directory with a `xark.toml`. */
export function projectRoot(from = process.cwd()) {
  for (let dir = from; ; dir = dirname(dir)) {
    if (existsSync(join(dir, "xark.toml"))) return dir;
    if (dirname(dir) === dir) throw new Error(`no xark.toml in ${from} or above it: not in a xark project`);
  }
}

/**
 * A build output directory (`target/xark/<name>/`), as a prover takes it, with
 * the keys in `keys` (by default the same directory).
 */
export function artifacts(dir, keys = dir) {
  const read = (d, f) => new Uint8Array(readFileSync(join(d, f)));
  if (!existsSync(join(keys, "pk.bin"))) throw new Error(`no proving key in ${keys}: run \`xark build\``);
  return {
    // A key fits the build it was made from: the one kept beside it, if it is.
    circuit: existsSync(join(keys, "circuit.xbc")) ? read(keys, "circuit.xbc") : read(dir, "circuit.xbc"),
    provingKey: read(keys, "pk.bin"),
    verifyingKey: read(keys, "vk.bin"),
    sources: readFileSync(join(dir, "sources.json"), "utf8"),
    client: existsSync(join(dir, "client.wasm")) ? read(dir, "client.wasm") : undefined,
  };
}

/**
 * Circuit `name`'s build output (`circuits/<name>/target/xark/<name>/`) and keys
 * (`keys/<name>/`) in the project.
 */
export function circuit(name, root = projectRoot()) {
  return artifacts(join(root, "circuits", name, "target", "xark", name), join(root, "keys", name));
}

/**
 * Program `name`'s artifact: `target/deploy/<name>_program.so` in the project.
 * Pass a root as the second argument, or options: `{ root, dir, file }`.
 * This is a test helper, not a sandbox: the inputs are trusted.
 */
export function program(name, rootOrOptions = undefined) {
  if (typeof name !== "string" || !name) {
    throw new Error(`program: expected a program name, got ${JSON.stringify(name)}`);
  }
  const options =
    typeof rootOrOptions === "string" || rootOrOptions === undefined
      ? { root: rootOrOptions }
      : rootOrOptions;
  if (options === null || typeof options !== "object") {
    throw new Error("program: the second argument must be a project root or options");
  }
  const base = resolve(options.root ?? projectRoot());
  const file = options.file ?? `${name.replaceAll("-", "_")}_program.so`;
  const full = resolve(base, options.dir ?? "target/deploy", file);
  const fromBase = relative(base, full);
  if (fromBase === ".." || fromBase.startsWith(`..${sep}`) || isAbsolute(fromBase)) {
    throw new Error(`program: ${file} resolves outside the project`);
  }
  return full;
}
