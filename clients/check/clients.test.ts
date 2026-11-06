// The committed clients are exactly what `xark client` generates now, so a
// generator change shows up in review. `npm run update` (vitest -u) rewrites them.
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { inject } from "vitest";
import { outDir } from "./artifacts";
import { examples } from "./setup";

for (const name of examples) {
  for (const file of [`${name}.ts`]) {
    test(`${name}/${file} is current`, async () => {
      const generated = readFileSync(join(inject("generated"), file), "utf8");
      await expect(generated).toMatchFileSnapshot(`./${name}/${file}`);
    });
  }
}

// A generated client is one file with no relative import, so Node's own ESM loader
// runs it as is (no bundler, no `moduleResolution` settings), given its build
// output's bytes.
test("a generated client runs in Node as is", () => {
  const client = pathToFileURL(join(__dirname, "cube", "cube.ts")).href;
  const script =
    `import { readFileSync } from "node:fs";\n` +
    `import { Cube } from ${JSON.stringify(client)};\n` +
    `const dir = ${JSON.stringify(outDir("cube"))};\n` +
    `const read = (f) => readFileSync(dir + "/" + f);\n` +
    `const prover = await Cube.prover({ circuit: read("circuit.xbc"), provingKey: read("pk.bin") });\n` +
    `console.log(prover.prove({ secret: 3, result: 27 }).publicInputs.result.toString());`;
  const out = execFileSync(process.execPath, ["--input-type=module", "-e", script], { encoding: "utf8" });
  expect(out.trim()).toBe("27");
});
