# Reproduction

2026-10-08, owner prime_gap_density, workspace task-3/routes/prime-gap.
Read-only lab f4ef0715bbe2f4890b3dcea034757ef0c823053a, pinned PR276 input
1aff81ebbdb5b749c638a6450016e167f9b3f61e. No paid compute or external jobs.
Source base_bound.py SHA256 a5e2e54079979bbd71197ddddb4e45443bc027fe23a4692f7d44ea8e46410969.

From task-3/zeta-research:

```
.venv/bin/python ../routes/prime-gap/density.py > ../routes/prime-gap/verification.txt
.venv/bin/python ../routes/prime-gap/crosscheck.py > ../routes/prime-gap/crosscheck.txt
```

Python 3.13, python-flint 0.9.0, Arb 256-bit. Serial, no array allocation or
parallel worker. Measured wall times .146s and .349s. Resource limits were
organizational, not OS enforced; no heavy code was run. Output hashes:

verification.txt 8c7de7604be9c443334a270bbd6cf9cfeee953b6e73d6e359a306b3c07f29e2b
crosscheck.txt 43c9a24619624425c603fc66ad95ef3c1dc9eabf2aa35e842df3282dab18db12

Outcomes: 604 closed Arb intervals, analytic monotone tail bound below .045583,
nine exact prime witnesses. Negative controls reject full-N k8 and fixed-.85
k7 bounds at log n=30. Additional diagnostic of k7 with split .8 and rounded
source constants7,4 gave margin -57.566 at log n30, so that proposed change
is not a useful extension. This failed diagnostic does not refute k7.

The output records inequalities and exact witnesses. It does not prove the
external source theorem or the inherited analytic explicit-formula argument.
The written reduction and source check require independent review.

Correction: the first run used B.upper() for the rare-zero integration
endpoint. Independent audit found this discards a positive sliver. The repaired
run keeps the exact endpoint inside an Arb ball and propagates that enclosure.
The first output hash was b9698875079e9782b003e7814605311ea8cda230cd3600a20854132a5f8039d1;
the corrected output hash above supersedes it. Both scripts replayed in .479s
combined after the repair, with unchanged displayed margins.
