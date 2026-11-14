import { defineConfig } from "vitest/config";

// `tests/*.test.ts`: prove with a circuit's generated client, then send the proof to
// its program in LiteSVM. They read the circuits' build output and the programs'
// `target/deploy/*.so`.
export default defineConfig({
  test: {
    include: ["tests/*.test.ts"],
    globals: true,
    testTimeout: 300_000,
    hookTimeout: 300_000,
  },
});
