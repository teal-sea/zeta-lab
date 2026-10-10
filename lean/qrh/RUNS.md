# Hunt 125 remote build record

## Bridge compiler failure, 2026-10-10 UTC

The third replacement restored the cache and completed all three upstream
targets, including `OAI.NumberTheory.DirichletL.Nonvanishing`. The upstream
stage passed in 5,991 seconds, including checkpoint pauses. This is a warm
recovery stage time, not a cold build time. The bridge failed at 01:11:30 UTC:
`hadamardB` depends on noncomputable `logDeriv` but lacked `noncomputable`.
The source now declares it `noncomputable def`; the definition and proofs
are otherwise unchanged. The fix passed 22 lightweight repository tests,
with five slow tests excluded, plus context and whitespace checks.

The final checkpoint completed in 129.67 seconds. Downloaded volume evidence
at `evidence/77912557fa8f631370dda09329689a2bef704d69-20261009T232507Z-9`
confirms shell and supervisor exit code 1. The supervisor measured 6,513.38
seconds after cache restoration, including nine checkpoint saves totaling
1,183.23 seconds. The axiom stage did not run. The app stopped and no container
remained before preparing the retry. Evidence is preserved under
[bridge failure](evidence/2026-10-10-bridge-failure/).

| Stage | Wall seconds | Exit code |
| --- | ---: | ---: |
| toolchain | 0 | 0 |
| upstream-update | 154 | 0 |
| upstream-cache | 108 | 0 |
| qrh-update | 31 | 0 |
| qrh-cache | 27 | 0 |
| qrh-build | 10 | 0 |
| upstream-build | 5991 | 0 |
| bridge | 47 | 1 |

## Current route, 2026-10-09

The repaired attempt launched at 19:57:38 UTC from committed source
`77912557fa8f631370dda09329689a2bef704d69`:
https://modal.com/apps/teal-sea/main/ap-RMu4JSUjqi0guhBtjGEPnF.
The old app is stopped. The new worker restored the retained setup archive.
Its first periodic checkpoint committed in 86.40 seconds at about 20:09:52 UTC;
the build process group then resumed. The checkpoint's evidence directory is
visible on the retained volume at
`evidence/77912557fa8f631370dda09329689a2bef704d69-20261009T195825Z-8`.
The retry has completed upstream-update (242 seconds), upstream-cache (149
seconds), qrh-update (190 seconds), qrh-cache (114 seconds) and qrh-build
(83 seconds), all with exit code zero.
Heartbeat
`watch-hunt-125-modal-build` now follows this app and CLI session 32240.
The repaired source passed 29 lightweight repository tests, including seven
checkpoint cases, with five slow tests excluded. Generated context, shell
syntax, whitespace and pre-push secret checks passed.

The repaired worker was also preempted. It received termination at 21:57:18
UTC, with the shell correctly reporting `exit_code=143 total_seconds=7133`;
Modal reported the preemption and automatic restart at 21:59:10 UTC. Ten
periodic checkpoint commits had completed, taking 86.40, 97.99, 102.00,
115.81, 106.87, 100.73, 100.73, 103.79, 133.16 and 133.64 seconds. The last
completed checkpoint was at 21:56:27 UTC. The final preemption cleanup did
not persist an outcome or supervisor file, so the signal outcome comes from
the application log, not a terminal volume verdict.

The replacement container `ta-01M4HATRSGHVSPS24WW9SY3GZR` started at 21:59:12
UTC in the same app and restored the warm cache at 22:00:38 UTC. Direct file
checks in that container found the compiled `QRH125.olean` and OpenAI
`ConstantCancellation.olean`. Lake then completed upstream-update in 146
seconds, upstream-cache in 106, qrh-update in 29, qrh-cache in 22 and the
cached package build in 8 seconds, all with exit code zero. Its package log
explicitly replayed the saved SmallModuli, IntervalCExp, Ball and BallTerm
results. The upstream build resumed with modules that had been in progress
at the last checkpoint. Cache reuse after preemption is now observed.
No duplicate build was launched. The checkpoint's stage timings, manifests,
package build log and a preemption/restart application-log excerpt are
preserved under [recovery evidence](evidence/2026-10-09-checkpoint-recovery/).
The upstream nonvanishing target, bridge and all eight axiom reports remain
pending. Checkpoint recovery does not change the theorem's grade.

The replacement worker received termination at 23:19:59 UTC, reporting
`exit_code=143 total_seconds=4761`. Modal confirmed a third preemption at
23:22:24 UTC and automatically restarted the same input in container
`ta-01M4HFKYQCXZ00CVWS1TQXJM0R` at 23:22:53 UTC. That container began restoring
the retained archive. The interrupted worker had committed six checkpoints,
taking 84.40, 94.56, 87.15, 97.62, 87.48 and 102.92 seconds. The last completed
save was at 23:09:53 UTC. Its final archive was interrupted, leaving the
previous complete 8.6-GiB archive intact. No terminal outcome or supervisor
file was present in its volume evidence; the signal status comes from the
application log. Its completed stage timings and preemption log are preserved
under [third-preemption evidence](evidence/2026-10-09-third-preemption/).
No compiler failure was reported and no duplicate build was launched.

### Preemption and checkpoint repair

The first worker was preempted at 19:47:28 UTC, 2 hours 4 minutes 59 seconds
after its 17:42:29 UTC start. No compiler error had been reported. The final
observed upstream job was 5982; Lake's changing job counts are not an ETA.
The package stage had completed at 18:00:09 UTC, but the upstream nonvanishing
target, bridge and axiom gate had not finished. This is not a completed build
or a proof of Theorem 1(a).

Completed stages from the Modal application log:

| Stage | Wall seconds | Exit code |
| --- | ---: | ---: |
| upstream-clone | 45 | 0 |
| elan-install | 2 | 0 |
| toolchain | 130 | 0 |
| upstream-update | 433 | 0 |
| upstream-cache | 111 | 0 |
| qrh-update | 207 | 0 |
| qrh-cache | 25 | 0 |
| qrh-build | 85 | 0 |

The volume had no archive because the original launcher saved only at the
end. Modal automatically restarted the same input at 19:48:22 UTC in
`ta-01M4H3B687VNP6X8HRKE948SQR`; that worker reported a cold cache. The
supervisor stopped its build at 19:51:59 UTC so the launcher could archive
the recovered setup before a repaired retry. Its Python subprocess status
was `-15` (SIGTERM). The shell's EXIT trap incorrectly wrote zero, and the
old CLI also exited zero. Neither zero is a successful build verdict.

The stopped retry's volume evidence was downloaded from
`evidence/2eb8a1bb88f49b8fd54d3e5339177cf73cfb10bc-20261009T194822Z-5`.
[Preserved evidence](evidence/2026-10-09-preemption/) includes those original
outcome, pin and timing files plus a timestamped application-log excerpt.
The first worker's terminal volume evidence does not exist; its completed
stage times above come from the application log. The retained volume now
contains `cache.tar.zst`. There were no active containers before retry setup.

The repair keeps the same eight-core, 48-GiB allocation and volume. Every ten
minutes it pauses the build process group, saves the cache and evidence, commits
the volume, then resumes. The prior archive survives a partial archive failure.
Nested timeouts stay in that group. Signal exits and remote failure status now
propagate accurately; the supervisor also records its own outcome. The upstream
cap is 210 minutes within a 230-minute overall build budget and four-hour function
cap, so checkpoint time is counted. No paid non-preemptible multiplier is enabled.
This follows Modal's [preemption](https://modal.com/docs/guide/preemption) and
[volume commit](https://modal.com/docs/guide/volumes#volume-commits-and-reloads)
guidance. Seven lightweight tests exercise paused descendants, failure exits,
timeout cleanup, interrupted archives and evidence persistence. Remote checkpoint
timing was measured on the repaired attempt above.

### Earlier launches

Thomas directly selected Modal for both Lean builds and numerics. Namespace
activation is no longer a prerequisite and no Namespace subscription was
created by this session. The earlier route and failed allocation below are
historical records.

The first Modal launch started from Ghost at 17:38:44 UTC using the
Infisical wrapper. Run:
https://modal.com/apps/teal-sea/main/ap-zy6pFKeM1T4GG7DX4klwrg.
The allocation is the one recorded below: eight physical cores, 48 GiB,
four-hour cap, retained volume `zeta-qrh-4341-adc7f124`. This Codex session
owns the attached run and collects its terminal outcome.

Outcome: image `im-9udQjixL7mranmMuigfwjO` built in 48.14 seconds, then the
launcher refused the dirty source tree before invoking the remote function.
Route documentation had been edited during image preparation. Its clean-tree
guard worked; no Lean compilation occurred. Commit those edits before the
retry, then keep the upload tree unchanged until the source has been captured.

The clean retry started at 17:40:17 UTC with source
`2eb8a1bb88f49b8fd54d3e5339177cf73cfb10bc`:
https://modal.com/apps/teal-sea/main/ap-qYdxL9dkFmIyrnxn8ykpuN.
Modal initially queued it for CPU capacity, then started container
`ta-01M4GW4BQPE5S48HNTF4C3ZV6R` at 17:42:29 UTC. The cold OpenAI clone took
45 seconds, elan setup two seconds, and Lean 4.34.1 installation 130 seconds.
The installer reports Lean commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Dependency setup is in progress; these stage timings are not a completed
build time. No kernel verdict has been obtained.

Supervision continues in the owning Codex thread through heartbeat
`watch-hunt-125-modal-build`, every five minutes. It must collect the terminal
build outcome and axiom evidence, handle concrete failures, and pause after
the initial package and bridge build is resolved. No parallel build may
write to this cache.

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
