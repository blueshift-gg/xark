// The committed clients are exactly what `xark client` generates now, so a
// generator change shows up in review. `npm run update` (vitest -u) rewrites them.
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { inject } from "vitest";
import { examples } from "./setup";

for (const name of examples) {
  for (const file of [`${name}.ts`, `${name}.schema.ts`]) {
    test(`${name}/${file} is current`, async () => {
      const generated = readFileSync(join(inject("generated"), file), "utf8");
      await expect(generated).toMatchFileSnapshot(`./${name}/${file}`);
    });
  }
}
