# Rung 3 receipts

`RESULTS.md` and `RUNS.md` cite these as `<cache>/rung3-ball-production-full/...` and
`<cache>/rung3-conron-fleet-20261027`. They were on one machine only. They were copied
into the tree on 2026-10-30 because the site oleans they hash, the 20 job artifacts of
GitHub Actions run 40353536947, expire on 2026-11-25. After that date these files are
the record of what was built and checked.

| directory | what it holds | cited in |
|---|---|---|
| `rung3-ball-production-full/receipts` | the first assembly: site-root and assembly olean SHA-256, logs | `RESULTS.md` section 3, Assembly |
| `rung3-ball-production-full/receipts-strip-20261026` | the strip re-assembly and its three faults | `RESULTS.md` section 3, strip |
| `rung3-ball-production-full/receipts-replay-20261027` | door 1, Stage A: `leanchecker --fresh`, census, sample, logs | `RESULTS.md` section 3, Stage A |
| `rung3-ball-production-full` (the rest) | collect and assemble logs, fault logs, records, terminal state | `RUNS.md`, 2026-10-26 |
| `rung3-conron-fleet-20261027` | door 1, Stage B: state files, the VM registry `vms.jsonl`, every shard receipt and log | `RESULTS.md` section 3, Stage B |

## What changed on the way in

- **Home paths scrubbed.** The operator's home directory became `<cache>` (the cache
  directory), `<repo>` (the checkout) or `~`, in 348 files. `SCRUBBED.sha256` lists
  each of those files with its SHA-256 *before* the scrub. No scrubbed file's digest
  is pinned in `pilot.json` or in another receipt, so the scrub breaks no pin. Every
  other file is byte for byte as it was. The VM working directory `/data/home/zr3c`
  belongs to the fleet's throwaway VM account and is kept.
- **Process state dropped:** the `*.pid` files, `STOP` and `deadman.deadline` of the
  fleet directory, nine files with no content beyond a process id or a flag.
- **Too large to commit, digests kept:** `NOT_COMMITTED.sha256` gives the SHA-256 of
  every fleet file left on the machine. These are the 217 shard manifests
  (`manifests/`, 1.5 GB), the phase-0 census and closure (`phase0/*.zst`), the
  assembly oleans (`asm/`), the `exportshard` binary and its generated C (`build/`)
  and the two spooled exports (`spool/`).

The probe scripts under `rung3-conron-fleet-20261027/probe` read provider keys at call
time and contain none.
