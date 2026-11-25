const assert = require("node:assert/strict");
const { test } = require("node:test");
const fs = require("node:fs");
const os = require("node:os");
const path = require("node:path");
const { pathToFileURL } = require("node:url");

test("program() resolves a name, with optional directory and file", async () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "xark-paths-"));
  try {
    const root = path.join(tmp, "project");
    fs.mkdirSync(path.join(root, "sub"), { recursive: true });
    fs.writeFileSync(path.join(root, "xark.toml"), "");
    const { program, projectRoot } = await import(
      pathToFileURL(path.join(__dirname, "..", "js", "testing", "paths.mjs")).href
    );

    assert.equal(projectRoot(path.join(root, "sub")), root);
    assert.equal(
      program("my-circuit", root),
      path.join(root, "target/deploy/my_circuit_program.so"),
    );
    assert.equal(
      program("my_circuit", root),
      path.join(root, "target/deploy/my_circuit_program.so"),
    );
    assert.equal(
      program("my_circuit", { root }),
      path.join(root, "target/deploy/my_circuit_program.so"),
    );
    assert.equal(
      program("my_circuit", { root, dir: "dist" }),
      path.join(root, "dist/my_circuit_program.so"),
    );
    assert.equal(
      program("my_circuit", { root, file: "my_circuit.so" }),
      path.join(root, "target/deploy/my_circuit.so"),
    );
    assert.throws(() => program("", root), /program:/);
    assert.throws(() => program("../../../outside", root), /outside the project/);
    assert.throws(() => program("x", { root, dir: "../outside" }), /outside the project/);
    assert.throws(() => program("x", { root, dir: "/outside" }), /outside the project/);
    assert.throws(() => program("x", { root, file: "../../../outside.so" }), /outside the project/);
    assert.throws(() => program("x", { root, file: "/outside.so" }), /outside the project/);
    assert.throws(() => program("x", null), /second argument/);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});
