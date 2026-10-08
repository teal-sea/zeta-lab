# Read-only reproduction from a fresh lab checkout

Use the repository's installed Python environment (Python3.13 and
python-flint0.9.0 were used for Arb checks; the exact DFT producer manifests
record Python3.10.4). No model access, credentials,
network, Lean build or large DFT arrays are required. Run from the repository
root. These commands do not overwrite the recorded evidence; Python may create
ignored bytecode caches. Historical producer RUNS/README files preserve their
original task-local commands and pending-review labels; use this integration
entry point and REVIEW-STATUS.md for the imported package.

```sh
.venv/bin/python -c 'from zeta import rigor; print(rigor.BACKEND, rigor.available_backends())'
.venv/bin/python hunts/oct08_extensions/routes/prime-gap-multistrip/layers.py
.venv/bin/python hunts/oct08_extensions/audits/prime-gap-multistrip/check.py
.venv/bin/python hunts/oct08_extensions/routes/dft-central-compression/verify.py
.venv/bin/python hunts/oct08_extensions/audits/dft-central-compression/check.py
.venv/bin/python hunts/oct08_extensions/routes/dft/verify.py
.venv/bin/python hunts/oct08_extensions/audits/dft/check.py
.venv/bin/python hunts/oct08_extensions/routes/algorithm/falsify.py
```

The prime checks need python-flint; the DFT and algorithm checks use exact
standard-library arithmetic. Every command is serial and bounded on the
recorded inputs. For original manifests, without generating new ones:

```sh
.venv/bin/python hunts/oct08_extensions/routes/dft/validate_manifest.py hunts/oct08_extensions/routes/dft/manifest.json --root hunts/oct08_extensions/routes/dft
.venv/bin/python hunts/oct08_extensions/routes/dft/validate_manifest.py hunts/oct08_extensions/routes/dft-central-compression/manifest.json --root hunts/oct08_extensions/routes
```

Check immutable artifact bytes from the hunt directory with:

```sh
shasum -a 256 -c CHECKSUMS.sha256
```

## Separate dependency contracts

| Result | Nonstandard input assumed | Published or upstream inputs | What the finite checks establish |
| --- | --- | --- | --- |
| Seventh-power prime intervals for every integer n>=1 | All nontrivial zeta zeros have real part<=7/8 | Explicit formula, verified RH height, zero counting and KLN explicit density rows; source leaves in the prime audits | All764 enclosed cells, tail inequalities, exact small witnesses and mutation controls; the universal reduction is written mathematics |
| Central-wire reduction and exact-complex DFT bound | Pinned upstream written frame/compiler/synchronization/all-length lemmas | OpenAI source commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, with Git-blob-checked snapshots | Scalar schedules, arbitrary auxiliaries, finite ranks and rational exponent inequalities; universal labels and transfer remain written mathematics |

The DFT result does not assume QRH. The prime result does not depend on the
DFT compiler. Neither audit validates OpenAI's QRH argument or makes either
new result Lean-formalized. The DFT model permits1/3 and supplies a root of
order<1024n^3; it is not a Gaussian-dyadic integer multiplication result.
Literature checks do not establish global novelty.
