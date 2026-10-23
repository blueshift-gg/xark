// Test harness only: an example's build output (`xark build` + `xark setup`, run by
// setup.ts, before the tests). An app gets these bytes however it ships them — a
// bundler asset, `fetch`, a CDN — so the example tests take them from here.
import { readFile } from "node:fs/promises";
import { existsSync, readFileSync } from "node:fs";
import { createServer } from "node:http";
import type { AddressInfo } from "node:net";
import { join } from "node:path";

export const outDir = (example: string) => join(__dirname, "..", "..", "examples", example, "target", "xark", example);

export function artifacts(example: string) {
  const dir = outDir(example);
  const read = (f: string) => new Uint8Array(readFileSync(join(dir, f)));
  return {
    circuit: read("circuit.xbc"),
    provingKey: read("pk.bin"),
    verifyingKey: read("vk.bin"),
    sources: readFileSync(join(dir, "sources.json"), "utf8"),
    /** `client.wasm`: the circuit's Rust functions, when it has some. */
    client: existsSync(join(dir, "client.wasm")) ? read("client.wasm") : undefined,
  };
}

/**
 * Serve an example's build output over HTTP on a free local port, as an app would,
 * leaving out the files in `without`. `requests`: the files asked for, in order.
 */
export async function serve(
  example: string,
  without: string[] = [],
): Promise<{ url: string; requests: string[]; close: () => Promise<void> }> {
  const dir = outDir(example);
  const requests: string[] = [];
  const server = createServer(async (req, res) => {
    const name = (req.url ?? "/").slice(1);
    requests.push(name);
    try {
      if (name.includes("/") || name.includes("..") || without.includes(name)) throw new Error("no");
      res.end(await readFile(join(dir, name)));
    } catch {
      res.statusCode = 404;
      res.end();
    }
  });
  await new Promise<void>((ok) => server.listen(0, "127.0.0.1", ok));
  const { port } = server.address() as AddressInfo;
  return {
    url: `http://127.0.0.1:${port}/`,
    requests,
    close: () => new Promise((ok) => server.close(() => ok())),
  };
}
