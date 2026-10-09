# Namespace build record

## Initial allocation, 2026-10-08

The measured baseline is the lab's previous OpenAI replay: 135 minutes on a
GitHub-hosted runner with Lake's default parallelism of four (`docs/38`, section 7).
Namespace performance has not yet been measured. Allocate one Linux amd64
instance with 16 vCPUs and 32 GB RAM for at most three hours, initially
`LEAN_NUM_THREADS=6` runtime workers. This is not a `lake build -j` flag or a
measured cap on build memory. A live supervising session must own the run
and collect its terminal outcome.

Retain the OpenAI checkout, dependency builds, toolchain and evidence on a
50 GB cache volume named `zeta-qrh-4341-adc7f124`. Reusing a cache requires
checking the complete pinned revision and toolchain. Record cache hits and
misses; the provider may supply an older generation or an empty volume.

Estimate at the published overage rate: at most $4.32 for three hours of
16x32 compute, plus cache snapshot and retained-storage charges. The published
snapshot rate is $0.002/GB-hour and retained storage $0.0048/GB-day, with
storage accounting in 100 GB blocks. This is a planning bound for this one
compute allocation, not a measured bill or a performance prediction.
Source: https://namespace.so/pricing.md, read 2026-10-08.

Write each stage's log and elapsed time to the cache. Lake writes outputs
per module, allowing an interrupted build to resume. Do not launch concurrent
builds into the same directory. No build result is claimed until recorded.

## Attempt 1: creation denied

On 2026-10-08, `nsc create --bare --machine_type linux/amd64:16x32
--duration 3h --volume cache:zeta-qrh-4341-adc7f124:/cache:50gb` returned
`access denied` (request `cnsjuehdleq35uru9up0oeisj8`). No runner was created.
The CLI login was valid. The workspace billing page said a subscription was
required. Activating a paid plan was left for explicit operator approval.

First Namespace build time: **not measured, no build started**. No cache
volume exists from this attempt and no remote numerical job was launched.

Local checks are limited to shell syntax, source policy, exact finite
residue enumeration, and fault-injection checks of the axiom-log parser.
They do not establish that any Lean declaration elaborates on 4.34.1.

## Modal allocation, 2026-10-09

Namespace is blocked on a subscription, so the first build moves to Modal, also
Thomas's routing (Lean builds and numerics on Modal until Namespace is paid for).
`scripts/modal_build.py` runs `scripts/namespace-build.sh` unchanged except for
`QRH_RUNNER=modal` and `QRH_CACHE=/work`: the build works on the container's
local disk, then packs the warm cache into `cache.tar.zst` on the Modal volume
`zeta-qrh-4341-adc7f124` and copies the evidence directory beside it.

Allocation: one container, 8 physical cores (16 vCPU), 48 GiB, four-hour
timeout, at most one container at a time. Memory is set high because Lake
compiles one module per hardware thread; 32 GiB at 16 threads would be marginal
for the OpenAI library.

Estimate at Modal's published rates, $0.0000131 per physical core-second and
$0.00000222 per GiB-second (https://modal.com/pricing, read 2026-10-09):
8 cores cost $0.377 an hour and 48 GiB cost $0.384 an hour, so $0.76 an hour
and at most $3.04 for the four-hour cap. The Starter plan includes $30 of
compute a month. The cache archive will be a few GiB, inside the free 1 TiB of
volume storage. This bounds the allocation; it is not a measured bill or a
build-time prediction. The only measured baseline is still 135 minutes for
the OpenAI tree on a four-core GitHub runner (`docs/38`, section 7).

First Modal build time: **not measured yet**. The launcher was checked to load
under modal 1.6.1; it has not run, because the session that wrote it has no
Modal login.

## Activation continued with authorization

Later on 2026-10-08, the operator explicitly directed the session to proceed.
The Developer plan was selected and its checkout opened. It requires card
entry; no payment method was available in the checkout form. Activation has
not completed and no second allocation was attempted. There is no remaining
permission question about the plan or the bounded first run.

While awaiting that input, the finite-case source was extended through the
character argument and logarithm comparisons. An exact rational cross-check
of the log(3) enclosure and the two power comparisons passed. The remote
script now checks the port before starting the long upstream build. These
remain source drafts, not kernel-checked results.

## Shared branch reconciled, 2026-10-09 UTC

The Ghost session rebased over `cc38d39c`, preserving the parallel session's
Modal launcher and allocation record. It did not launch that alternative:
this session's task specifies Namespace for Lean, and the payment form is
still incomplete. The temporary routing authorization above is recorded by
the parallel session; it was not independently confirmed in this session.

The finite-character draft was pushed as `9dc7e8ab`. The module-header guard
repair was incorporated as `8f6109d2`: an explicit eleven-file legacy allowlist
with a 4.34.1 pin check, retaining the other package's header requirement and
all line-limit and symlink checks. Four fault-injection cases test those
boundaries. All 43 focused repository tests passed, along with generated
context, shell syntax and whitespace checks. The pre-push secret check passed.
No Lean process ran on Ghost. No remote build has produced evidence.
