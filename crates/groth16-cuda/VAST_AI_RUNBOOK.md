# Vast.ai CUDA validation runbook

This runbook uses Vast.ai only for the CUDA checks that cannot run on the local
Intel Mac. It does not assume that the account credit is available or prevent
charges to a payment method. Check the credit balance and billing settings in
the Vast console before creating an instance.

## What is already verified at no GPU cost

- PR #47 is open. Before any GPU launch, query its current head and exact-head
  checks with `gh pr view 47 --repo blueshift-gg/xark` and
  `gh pr checks 47 --repo blueshift-gg/xark`. Require the PR head to match the
  checkout commit and all required checks to pass; this runbook intentionally
  does not treat historical CI results as current evidence.
- `make -C crates/groth16/cuda test-host` passed the host-side arithmetic,
  representation, range, and shape suites locally.
- `bash -n crates/groth16-cuda/scripts/run_cuda_validation.sh` and its `--help`
  path passed locally.
- A local Cargo CLI test could not reach compilation: crates.io DNS failed, and
  the offline Cargo cache lacks `ark-relations`. This is an environment limit;
  hosted CI is the available CLI test evidence until a networked Rust host runs
  the command.

No local NVIDIA device, CUDA compiler, or Nsight Systems installation is
available. No GPU result or speedup claim exists yet. Xark is a Groth16 proof
system, not an ML predictor. Record proof correctness and timing as the relevant
prediction/performance results.

## Credit-funded preflight

Use credits for one short, single-GPU run first. Do not use the $50 budget to
debug missing tools, dependency download failures, or an incompatible CUDA
image.

1. In Vast billing, confirm the available credit amount and whether usage can
   charge a saved payment method after credits run out.
2. Search for one verified NVIDIA offer with at least 16 GB VRAM, host
   reliability of at least 98%, a CUDA development image with `nvcc`, and a
   total GPU rate at or below $1/hour. Prefer a single RTX 3090 (Ampere) or
   RTX 4090 (Ada) if the current offers meet those requirements. Do not choose
   another architecture only because its price is lower; first verify it is
   supported by the pinned ICICLE v4.0.0 backend and CUDA toolkit. The Vast CLI
   supports read-only offer searches such as:

   ```sh
   vastai search offers 'gpu_name=RTX_3090 num_gpus=1'
   ```

   Review the listing's verified status, reliability, GPU, CUDA compatibility,
   disk, storage rate, transfer rate, and total hourly amount. The account
   balance is private to the Vast console; do not infer it from market offers.
3. Use on-demand for this correctness run so a preemption does not discard a
   compile or test run. Set the console's maximum instance duration to two hours.
   Budget no more than $5 equivalent from credits for this preflight, including
   disk and transfer charges. If the account cannot enforce credit-only usage,
   do not create the instance until the billing behavior is clear.
4. Use a CUDA *development* container, not a runtime-only image. Vast's CUDA
   Ubuntu template documents a `cudnn-devel` image with `nvcc`. Verify `nvcc`,
   `nvidia-smi`, `g++`, `make`, `git`, Python 3, Rust/Cargo, and GNU time before
   running the suite. The credit smoke can skip Nsight with
   `XARK_CUDA_CAPTURE_NSYS=0`; the full run requires `nsys`. If Rust is missing,
   install stable Rust using the official [rustup guide](https://rustup.rs/).
   Install the version-matched ICICLE CUDA backend using Xark's pinned v4.0.0
   setup instructions. Nsight CLI installation is documented by NVIDIA's
   [Nsight Systems installation guide](https://docs.nvidia.com/nsight-systems/InstallationGuide/).
5. Read the current fork branch head, clone that branch, and require the clone
   to match the recorded revision:

   ```sh
   expected_commit=$(git ls-remote https://github.com/aryanputta/xark.git \
     refs/heads/gpu-msm-isolated | cut -f1)
   git clone --branch gpu-msm-isolated --depth 1 \
     https://github.com/aryanputta/xark.git xark
   cd xark
   test "$(git rev-parse HEAD)" = "$expected_commit"
   git status --short --branch
   ```

   Record `git rev-parse HEAD` in the output bundle. The validation script also
   records the commit in its environment file and output directory.

6. Run the bounded smoke matrix. This runs the required host checks, both GPU
   correctness paths, CUDA CLI cube proof and verification on both backends,
   then three benchmark repetitions at 1,024 and 65,536 points. Nsight is
   skipped on the credit preflight to keep its toolchain and runtime small; the
   full $50 run captures Nsight traces.

   The CLI inputs are the public cube fixture (`secret=3`, `result=27`). Do not
   send private proving inputs or keys to a marketplace host. The CLI records
   its timing-side-channel warning and requires an explicit acknowledgment.

   ```sh
   XARK_MSM_SIZES=1024,65536 \
   XARK_MSM_REPEATS=3 \
   XARK_MSM_SEED=24841619657020237 \
   XARK_CUDA_CAPTURE_NSYS=0 \
   crates/groth16-cuda/scripts/run_cuda_validation.sh
   ```

   The default artifact directory is `out/cuda-validation/<commit>/`. Copy it
   off the instance before cleanup. Capture the exact GPU model, driver, CUDA,
   Rust, Nsight, ICICLE backend version, and actual invoice/credit usage.
7. Stop immediately on any missing requirement, failed correctness test, device
   loss, or spend-limit concern. After copying results, destroy the instance and
   any attached volume in the Vast console. Stopping alone may leave storage
   charges active.

## $50 compute budget

After the credit preflight passes, use one GPU and the same pinned source. Keep
at least $10 unspent as a rerun and billing buffer; treat $40 as the maximum
planned spend, including storage and transfer. Use the same verified-offer
criteria and set a four-hour maximum instance duration for each session. Review
the live offer total before every launch; Vast prices are marketplace rates and
change over time.

Run the full reproducible matrix only after the smoke run succeeds:

```sh
crates/groth16-cuda/scripts/run_cuda_validation.sh
```

This requires GPU MSM comparison, GPU proof generation and verification, CUDA
CLI prove/verify through both adapters with confirmed GPU chunk use, the default
seeded sweep (1,024, 65,536, and 524,288 inputs, seven repetitions), and Nsight
captures at 65,536 and 524,288. If the run exceeds the
four-hour session cap, retain its logs and run a planned second session rather
than increasing the cap during the run. Preserve every raw CSV and profile
report. Compare each GPU adapter with CPU Pippenger from the same input set;
report medians and raw samples with the machine and software versions. Do not
report a speedup from the small correctness proof.

Vast.ai states that GPU charges stop when an instance is stopped, while storage
charges continue until the instance is destroyed. Include disk and data transfer
in the ledger and remove the instance/volume as soon as outputs are copied.

## Official references

- [Vast.ai live pricing](https://vast.ai/pricing): offer prices vary with supply
  and demand; inspect the live total before a run.
- [Vast.ai CLI quickstart](https://cloud.vast.ai/cli/): installation and
  read-only offer search. Do not put the API key in the repository or logs.
- [Vast.ai CUDA Ubuntu template notes](https://cloud.vast.ai/template/readme/672cdff0f451f9a5df952e71c5c5a92d):
  the development image includes `nvcc`.
- [Vast.ai stopped-instance billing explanation](https://vast.ai/article/hosting-an-llm-locally-vs-vast-ai):
  storage can continue billing after compute is stopped.
