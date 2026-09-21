# Evaluate a model against a proof-backed grader

**For you if** you want to see an LLM work against deterministic mathematical
checks instead of an LLM judge.

**First command:**

```bash
uv run --directory environments/bloch_certificate bloch-smoke
```

The first run downloads Frank Wikström's public MIT-licensed Bloch certificate
archive from Zenodo, verifies its pinned SHA-256, and runs four positive plus
four negative controls through the same reward path used by the environment.
The model never executes code or chooses a path. It can only query two
read-only tools and submit one exact decimal string.

The public seed contains four calibration rows: two fixed-radius certificate
reproductions, the published near-branch target, and the shipped near-branch
cutoff. It does not replay the 24 away sectors, include a secret test split, or
ship the Lean rung. Read
[`environments/bloch_certificate/README.md`](../../environments/bloch_certificate/README.md)
for the trust boundary and exact scientific scope.

Run a model after the controls pass:

```bash
uv run --directory environments/bloch_certificate vf-eval bloch-certificate   --model <provider/model> -n 4 -r 1
```

An accepted near-branch target is not by itself a theorem about Bloch's
constant. The paper's analytic bridge and the away branch remain separate
obligations, and the environment says so in every score's audit record.
