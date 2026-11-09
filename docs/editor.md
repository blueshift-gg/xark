# Editor diagnostics

`xark check <crate-dir>` runs the full `rustc` frontend *and* the xark subset
validator, surfacing every rejection as a **real `rustc` diagnostic with a source
span**. With `--message-format=json` it emits the same JSON stream as `cargo
check`, so an editor shows live rejections on save. In that mode it first runs the
`cargo check --all-targets` it replaces, so errors in tests and other host-only
code still show. `xark init` writes this
wiring; to add it to an existing crate, point `rust-analyzer`'s check command at
`xark` (which must be on `PATH`):

```toml
# rust-analyzer.toml
[check]
overrideCommand = ["xark", "check", ".", "--message-format=json"]
```

```jsonc
// .vscode/settings.json (VS Code equivalent)
{
  "rust-analyzer.check.overrideCommand": ["xark", "check", ".", "--message-format=json"]
}
```

Replace `.` with the crate directory (e.g. `examples/cube`) when the editor is
opened above the circuit crate. A violation then appears inline, e.g.:

```text
error: witness-dependent control flow is not supported
 --> src/lib.rs:7:5
note: branch conditions must be compile-time constants (e.g. loop bounds)
```
