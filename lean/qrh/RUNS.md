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
