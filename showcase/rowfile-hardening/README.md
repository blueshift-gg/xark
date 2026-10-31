# Xark row stream hardening demo

Open `index.html` directly, or serve the repository root:

```bash
python3 -m http.server 8000
```

Then open `http://localhost:8000/showcase/rowfile-hardening/`.

The page describes the row-window guard and malformed-stream parser hardening now grouped on PR #33. This is input validation for Xark’s existing streaming Groth16 path. It does not add a CUDA backend. The focused `xark-ir` tests still need to run in an environment that can resolve the workspace dependencies.
