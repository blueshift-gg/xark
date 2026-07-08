//! `xark client` — scaffold a small TypeScript starter for a circuit, built on
//! the reusable **xark-client** library (the Anchor pattern: one library, and
//! the per-circuit part is just the IDL).
//!
//! It writes the typed IDL (`<name>.idl.ts` + `.json`), a `package.json` that
//! depends on `xark-client`, and an `example.ts` that verifies a proof and
//! shows the on-chain instruction bytes. It does NOT fake a transaction: the
//! accounts and instruction discriminator belong to your program.
//!
//! Proving stays in the `xark` CLI — snarkjs verifies xark proofs but can't
//! generate them. The loop is `xark prove …` → feed the resulting
//! `<name>-<hash>.proof.json` bundle to `example.ts`.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Args;

use crate::xark_project::XarkProject;

#[derive(Args, Debug)]
pub struct ClientArgs {
    /// Circuit crate directory (or its `target/xark/` output dir). Defaults to
    /// the current directory; paths are inferred from `target/xark/`.
    #[arg(value_hint = clap::ValueHint::DirPath)]
    pub path: Option<PathBuf>,

    /// Output directory for the generated client. Inferred as
    /// `target/xark/<name>/client`.
    #[arg(long, value_hint = clap::ValueHint::DirPath)]
    pub out: Option<PathBuf>,
}

pub fn run(args: ClientArgs) -> Result<()> {
    let project = XarkProject::resolve(args.path.clone())?;
    let idl = super::idl::build_idl(&project)?;

    // Verification needs the verifying key; guide to `xark setup` rather than
    // scaffolding a client that can't verify.
    if idl.verifying_key.is_none() {
        anyhow::bail!(
            "no verifying key yet — run `xark setup {}` first, then re-run `xark client`. \
             The client verifies proofs with snarkjs, which needs the VK.",
            super::path_arg(&args.path)
        );
    }

    let out = args.out.clone().unwrap_or_else(|| project.client_dir());
    fs::create_dir_all(&out).with_context(|| format!("creating {}", out.display()))?;

    let name = idl.name.clone();
    let const_name = idl.ts_const();
    let idl_base = format!("{name}.idl"); // the `./<name>.idl` import specifier

    // The typed IDL is the per-circuit data the library consumes.
    write(
        &out.join(format!("{name}.idl.json")),
        &format!("{}\n", serde_json::to_string_pretty(&idl.to_json())?),
    )?;
    write(&out.join(format!("{name}.idl.ts")), &idl.to_typescript())?;

    let subst = |t: &str| {
        t.replace("__NAME__", &name)
            .replace("__CONST__", &const_name)
            .replace("__IDLBASE__", &idl_base)
    };
    write(&out.join("package.json"), &subst(PACKAGE_JSON))?;
    write(&out.join("example.ts"), &subst(EXAMPLE_TS))?;
    write(&out.join("README.md"), &subst(README_MD))?;

    println!(
        "Generated TypeScript client for `{name}` at {}",
        out.display()
    );
    println!(
        "{}",
        crate::style::brand(
            "✅ Client scaffolded on the xark-client library — verify (snarkjs) + on-chain bytes."
        )
    );
    let dir = out.display();
    println!(
        "\n{}",
        crate::style::next_steps(&[
            (
                format!("cd {dir} && npm install"),
                "install xark-client (+ snarkjs)",
            ),
            (
                "npx tsx example.ts <path-to-.proof.json>".to_string(),
                "verify a proof produced by `xark prove`",
            ),
        ])
    );
    Ok(())
}

fn write(path: &Path, contents: &str) -> Result<()> {
    fs::write(path, contents).with_context(|| format!("writing {}", path.display()))?;
    Ok(())
}

const PACKAGE_JSON: &str = r#"{
  "name": "__NAME__-client",
  "version": "0.1.0",
  "private": true,
  "description": "Client for the __NAME__ xark circuit (built on xark-client).",
  "scripts": {
    "verify": "tsx example.ts"
  },
  "dependencies": {
    "xark-client": "^0.1.0"
  },
  "devDependencies": {
    "@types/node": "^22.0.0",
    "tsx": "^4.19.0"
  }
}
"#;

const EXAMPLE_TS: &str = r#"// Verify a proof for the __NAME__ circuit with the xark-client library.
//
//   npm install
//   npx tsx example.ts <path-to-.proof.json>
//
// Produce a bundle first with:  xark prove <circuit> --input <name>=<value>

import { readFileSync } from "node:fs";
import { XarkClient, type ProofBundle } from "xark-client";
import { __CONST__ } from "./__IDLBASE__";

async function main() {
  const path = process.argv[2];
  if (!path) {
    console.error("usage: npx tsx example.ts <path-to-.proof.json>");
    console.error("  produce one with:  xark prove <circuit> --input <name>=<value>");
    process.exit(2);
  }

  // The IDL is typed, so `client.publicSignals(...)` is typed too.
  const client = new XarkClient(__CONST__);
  const bundle = JSON.parse(readFileSync(path, "utf8")) as ProofBundle;

  const ok = await client.verify(bundle);
  console.log(ok ? "✅ proof verified (snarkjs)" : "❌ proof INVALID");
  console.log("public signals:", client.publicSignals(bundle));

  // For on-chain use: `client.calldata(bundle)` returns the packed
  // `proof ‖ public_inputs` bytes. Your program owns the accounts and any
  // instruction discriminator, so build the transaction with your own client:
  //
  //   const data = client.calldata(bundle);   // Uint8Array

  process.exit(ok ? 0 : 1);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
"#;

const README_MD: &str = r#"# __NAME__ — client

Generated by `xark client`. Built on the **xark-client** library, driven by this
circuit's IDL — the Anchor pattern: one library, and the IDL is your circuit's
data.

## Install

```bash
npm install
```

## Verify a proof

```bash
xark prove <circuit> --input <name>=<value>   # writes __NAME__-<hash>.proof.json
npx tsx example.ts /path/to/__NAME__-<hash>.proof.json
```

## In your own app

```ts
import { XarkClient } from "xark-client";
import { __CONST__ } from "./__NAME__.idl";  // typed IDL

const client = new XarkClient(__CONST__);
await client.verify(bundle);          // snarkjs verify
const data = client.calldata(bundle); // packed proof ‖ public bytes (Uint8Array)
```

`data` is the verifier calldata — you own the accounts and any discriminator,
so build the transaction with your own client. The on-chain verifier itself
comes from `xark export`.

Proving happens in the `xark` CLI: snarkjs can verify an xark proof but cannot
generate one. Flow: `xark prove …` → feed the `.proof.json` bundle here.

> **xark-client not on npm yet?** Point the dependency at a local checkout:
> `npm install /path/to/xark/clients/typescript` (or a git URL).

Files: `__NAME__.idl.json`, `__NAME__.idl.ts` (typed), `example.ts`.
"#;
