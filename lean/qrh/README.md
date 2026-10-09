# Hunt 125 on the OpenAI toolchain

**Status, 2026-10-09 UTC: source draft, not compiled.** The first Namespace
create request returned `access denied`. A parallel session added a Modal
launcher, preserved below. Namespace activation is now authorized; its opened
checkout requires card entry by the operator. No instance, cache volume,
build time or Lean axiom
report was produced. The written result keeps its existing grade:
**proved, given OpenAI's Theorem 1.1, unreviewed**.

## Package boundary

This directory is a separate Lake package inside zeta-lab. Its toolchain is
Lean 4.34.1 and its Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The parent `lean/` package remains
on its existing toolchain. The five interval modules are copied downward;
the OpenAI library is never ported upward. See `NOTICE` for the extraction
changes and `LICENSE-OpenAI` for the upstream Apache-2.0 license.

`QRH125` contains the interval layer, Lemma 4's rational domination inequality,
its endpoint arithmetic, and a finite residue-cover certificate for q = 3 to
12. The finite certificate uses `decide`. A separate exact Python check of
all 44 unit residues passed, but is not a Lean verification. The draft now
connects that data to nonprincipal characters and interval-based logarithm
bounds, with `small_moduli_nonresidue_bound` as the finite-case target. This
new source has not been elaborated.

`QRHOpenAI.lean` imports the real upstream nonvanishing theorem, retaining its
principal-character pole exception. It defines the target bound as a
proposition, without asserting a proof. It also defines the complex Hadamard
constant as the log derivative of the normalized completion at zero and
derives its zero-sum identity from OpenAI's affine factorization. The real
part cancellation for complex characters remains open.

The bridge compiles in OpenAI's own Lake environment. This avoids nesting
OAI's pre-resolution and post-update hooks in a different package root.
Those hooks install compatibility patches into specific dependency paths.
The independent package and the bridge share the exact Mathlib/toolchain
pins; `scripts/namespace-build.sh` checks them and preserves both manifests
and the build logs. No proof source in OpenAI's checkout is edited.

## Run on Modal

From any machine with a Modal login (`modal token new`, or `MODAL_TOKEN_ID` and
`MODAL_TOKEN_SECRET` in the environment), on a clean committed branch:

```bash
pip install modal
modal run lean/qrh/scripts/modal_build.py
```

The calling machine only uploads `lean/qrh` and waits; the build runs remotely
(8 physical cores, 48 GiB, four-hour cap; estimate in `RUNS.md`). It prints the
pins, cache state, per-stage timings, exit code and axiom status, and leaves the
full evidence and a warm cache archive on the Modal volume
`zeta-qrh-4341-adc7f124`. The second run starts from that cache.

## Run on Namespace

Only proceed after the workspace has compute access. Start a single Ubuntu
container with the retained cache and a three-hour lifetime:

```bash
nsc run --image ubuntu:24.04 --name qrh125 \
  --machine_type linux/amd64:16x32 --duration 3h \
  --volume cache:zeta-qrh-4341-adc7f124:/cache:50gb \
  --documented_purpose 'Hunt 125 pinned Lean build' \
  --wait --output json -- sleep infinity
```

Record the returned instance ID, container image digest and startup time in
`RUNS.md`. This container launch has not been exercised: the earlier bare
instance create request was denied before provisioning.

From a clean, committed branch, archive and upload the source with the CLI's
`instance upload --container_name qrh125` command. The archive contains only
`lean/qrh`, with the Git revision next to it. Inside the container, install
`ca-certificates`, `git`, `curl`, `build-essential`, `python3`, `time`,
`util-linux`, `unzip` and `zstd` with Ubuntu's package manager. Extract into
`/cache/source/<revision>` and run:

```bash
QRH_NAMESPACE_RUN=1 timeout --signal=TERM --kill-after=60s 170m \
  bash /cache/source/<revision>/lean/qrh/scripts/namespace-build.sh
```

Keep the calling session attached and supervised. The script refuses macOS
and an unmounted cache, takes an exclusive cache lock, pins the upstream
revision, runs OpenAI's patching hooks, obtains the Mathlib cache, builds the
interval package first, then the required upstream modules and bridge, and
finally checks the eight axiom reports. Checking the port before the long
upstream build exposes compatibility failures sooner.
`LEAN_NUM_THREADS=6` controls runtime workers;
it is not a claim that Lake accepts `-j` or that six is a measured memory cap.

Every stage writes timing, logs and exit status under `/cache/evidence/`.
Collect that directory before the instance expires. A timeout or failed
axiom check is a failed run; partial cached oleans may be reused, but do not
raise the proof grade. Cache generations can be stale or empty.

## Obligations still open

1. Prove the contour-shift explicit formula for the smoothed character sum,
   adapting PNT+'s `MediumPNT/SmoothedChebyshev*` and using
   `OAI.SevenEighths.LogarithmicControl.logarithmic_control` where applicable.
2. Prove real part cancellation of the Hadamard constant for complex primitive
   characters, then the required weighted zero-sum estimates.
3. Prove the imprimitive-to-primitive comparison, the residue and trivial-zero
   estimates, and the kernel supremum and margin monotonicity.
4. Establish all analytic constant enclosures and prove `m(5/2) > 0` using
   kernel intervals. The numerical enclosure in the written proof is not a
   Lean input masquerading as a proved bound.
5. Compile and validate the draft character reduction and logarithmic
   comparisons for q = 3 to 12.
6. Instantiate `LeastNonresidueBound`, then Theorem 2. Run the axiom gate,
   Comparator and NanoDa before preparing a Palomar submission.

No statement-only file with a placeholder is introduced in this package.
The eventual comparison surface must respect the campaign's prohibition on
new proof placeholders as well as Comparator's format.
