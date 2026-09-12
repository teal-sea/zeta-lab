# RUNS: hunt `overlap_lower`

One block per autonomous run. A run that produced nothing records that it
produced nothing.

## Run 1: literature, reimplementation, local smoke tests

```runmanifest
id: overlap_lower-2026-08-23-local
hunt: overlap_lower
started: 2026-08-23T14:05-05:00
finished: 2026-08-23T15:20-05:00
ran:
  - two independent literature passes over arXiv:2201.05704, arXiv:2606.31182, arXiv:1609.08000 and github.com/teorth/optimizationproblems
  - .venv/bin/python hunts/overlap_lower/probe.py --front quick
  - .venv/bin/python hunts/overlap_lower/probe.py --front certificate --N 400 --R 10 --denom 1000000
  - .venv/bin/python hunts/overlap_lower/probe.py --front guard --N 400 --R 8
outcome: the reimplementation reproduces White's section 4 program (0.37368 at N=4000 R=20 against his 0.375169 at N=80000 R=20) and runs his section 5 program; three of the brief's premises were found wrong and corrected; the sweep was written for CI because the laptop could not carry it
artifacts:
  - hunts/overlap_lower/program.py
  - hunts/overlap_lower/probe.py
  - hunts/overlap_lower/ci-sweep.yml
```

## Run 2: the parameter sweep, in short local bursts

The sweep was written for CI (`hunts/overlap_lower/ci-sweep.yml`) and did not
run there: the credential available refuses to create a workflow file without
the `workflow` scope. It ran instead as a series of separately budgeted local
invocations, none longer than about ninety seconds, on the understanding that
the large end of the sweep would simply not be reached. It was not. What that
cost is stated in `RESULTS.md` under "What was not done".

```runmanifest
id: overlap_lower-2026-08-23-sweep
hunt: overlap_lower
started: 2026-08-23T15:25-05:00
finished: 2026-08-23T16:40-05:00
ran:
  - probe.py --front simplified --ns 1000,2000,5000,10000 --rs 20
  - probe.py --front simplified --ns 20000 --rs 20
  - probe.py --front simplified --ns 5000 --rs 5,10,20,40,80,160,320
  - probe.py --front simplified --ns 10000 --rs 10,20
  - probe.py --front full --rounds 25 --sweep 250:300:10,500:300:10,1000:300:10,2000:300:10
  - probe.py --front full --rounds 25 --sweep 1000:300:5,1000:300:10,1000:300:20
  - probe.py --front full --rounds 25 --sweep 1000:300:40
  - probe.py --front sine --N 1000 --T 300 --R 10 --rounds 25
  - probe.py --front box --N 500 --T 300 --R 10 --rounds 25 --nh 2 --np 3
  - probe.py --front certificate --N 5000 --R 20 --denom 10000000
  - probe.py --front guard --N 2000 --R 10
outcome: section 4 reproduced and its ceiling in R measured (saturates at R=40, total gain from White's R=20 onward 2.9e-6); section 5 swept but not reproduced, because the Parseval cone survives no cutting-plane formulation tried; one exact rational dual certificate accepted at 0.37399241331; the section 4 R sweep at N=10000 beyond R=20 exceeded the local budget and was abandoned rather than run
artifacts:
  - hunts/overlap_lower/results/simplified_N_a.json
  - hunts/overlap_lower/results/simplified_N_b.json
  - hunts/overlap_lower/results/simplified_R.json
  - hunts/overlap_lower/results/simplified_R_n10000.json
  - hunts/overlap_lower/results/full_N.json
  - hunts/overlap_lower/results/full_R.json
  - hunts/overlap_lower/results/full_R40.json
  - hunts/overlap_lower/results/sine.json
  - hunts/overlap_lower/results/box_grid.json
  - hunts/overlap_lower/results/certificate.json
  - hunts/overlap_lower/results/guard.json
```
