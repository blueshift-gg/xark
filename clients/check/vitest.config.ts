import { fileURLToPath } from "node:url";
import { defineConfig } from "vitest/config";

// `npm test` typechecks everything (tsc, which also fails on an `@ts-expect-error`
// with nothing to expect), then: builds what the clients need (setup.ts), checks the
// committed clients are current (clients.test.ts), and runs each example's
// `<name>/<name>.test.ts` through xark-wasm's node build. `npm run update` rewrites
// stale clients.
export default defineConfig({
  cacheDir: fileURLToPath(new URL("node_modules/.vite", import.meta.url)),
  test: {
    include: ["*.test.ts", "*/*.test.ts"],
    globalSetup: ["./setup.ts"],
    globals: true,
    testTimeout: 60_000,
    hookTimeout: 120_000,
  },
});
