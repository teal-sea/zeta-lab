# RUNS

```runmanifest
id: gauss_positivity-2026-10-03-main
hunt: gauss_positivity
started: 2026-10-03T09:00-05:00
finished: 2026-10-03T15:30-05:00
ran:
  - .venv/bin/python hunts/gauss_positivity/newton_battery.py --n-max 60 --d-max 10 --dps 60
  - .venv/bin/python hunts/gauss_positivity/turan_large_n.py --dps 60 --n-list 100,200,400,800,1600,3200
  - .venv/bin/python hunts/gauss_positivity/laplace_D.py --dps 80 --n-list 50,100,200,400,800,1600,3200
  - .venv/bin/python hunts/gauss_positivity/reproduce.py
outcome: the Turan inequality reduces exactly to a Cauchy-Schwarz deficit D_n <= 1/(n+1) on the moments of a positive weight, a saddle instrument reproduces D_n to 4-6 digits with 1/n error, the law n(r_n-1) -> 1 is measured, and two counterexamples move the criterion from positivity to Schoenberg total positivity; no RH statement is claimed.
artifacts:
  - hunts/gauss_positivity/journal.md
  - hunts/gauss_positivity/RESULTS.md
  - hunts/gauss_positivity/reproduce.py
  - hunts/gauss_positivity/reproduce_results.json
  - hunts/gauss_positivity/turan_large_n.py
  - hunts/gauss_positivity/laplace_D.py
  - hunts/gauss_positivity/newton_battery.py
  - hunts/gauss_positivity/newton_results.json
  - hunts/gauss_positivity/modal_moments.py
```

## Cost and compute notes

- **No Modal run.** The Modal token is absent on this machine (`~/.modal.toml`,
  `MODAL_TOKEN_ID`/`MODAL_TOKEN_SECRET`, `~/.config/modal*`, the keychain and
  the shell rc files were all checked). `modal_moments.py` is written and
  ready but was never executed. Every number in `RESULTS.md` was computed
  locally from the committed `zeta/li.py` machinery.
- The expensive object a Modal run would have bought (`b_n = ∫Φ u^{2n}` at
  large n) was not needed: the exact relation `b_n = (2n)!γ(n)/(64·4ⁿ·n!)` was
  derived and confirmed (`b_0 = Ξ(0)/8 = 0.0621400972735392637` to 30 digits),
  so the committed `γ(n)` table is the same data.
- Local wall time: `newton_battery.py` under 60 s; `turan_large_n.py` to
  n = 3200 under 5 min; `laplace_D.py` under 5 min; `reproduce.py` under 5 min.
  Nothing ran on a shared checkout and no long-lived process was left behind.

## Known defects in this hunt's own artifacts

- `modal_moments.py` is untested against a live Modal endpoint. It is kept
  because it is the costed path for the next experiment, and it is labelled
  here as unexecuted rather than presented as working.
- `newton_battery.py` returns `float` margins; at `d = 10, n = 50` the smallest
  is `1.2e-40`, i.e. at the working precision. It was re-checked at dps 120 and
  is stable, so it is a genuine small margin rather than noise, but the file
  should carry interval arithmetic before any margin is quoted as decided.