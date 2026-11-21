# The class-number lists for h <= 5000, given GRH for the quadratic characters

Base commit: `a401821c`. Branch `claude/sweet-planck-pf4oco`. Opened
2026-11-20. Status: bounded construction on a hypothesis that is not a
theorem. Reviewed the same day by two independent attack passes (proof and
computation), both "holds"; no claim downgraded. The findings and their
dispositions are in RESULTS.md section 9. What the review changed in scope:
the delta against the published frontier is the range 2000 < h <= 5000
only; the table D_GRH(h) is a valid cutoff but not the smallest Theorem B
gives (stalled cover cells, 1 to 2% for about 400 < h <= 2760); a stronger
classical route at abscissa 1/2 exists in float (the first door) and is not
adopted.

*Updated 2026-11-21*: the hypothesis is contained in the Alpoge theorem (through the routine bridge from chi_D to Mathlib's L-function, not yet written here),
verified outside this laboratory that day; the result is now stated as
proved, given the Alpoge theorem, and stays a candidate pending external
review. See the update at the top of RESULTS.md. The mission text below is
kept as written.

## Question and scope

On 2026-11-20 Levent Alpoge posted a claimed Lean proof of RH and of GRH for
Dirichlet L-functions. Its formal statement: for every Dirichlet character
chi mod N and every s with Re s > 1/2, L(s, chi) != 0 unless chi = 1 and
s = 1. No kernel has accepted the archive so far and no human has reviewed
it. This hunt does not read, replay or check it.

Six weeks ago `hunts/qrh_class_number/` took OpenAI's weaker half-plane
Re s > 7/8 and turned it into an explicit bound L(1, chi_D) >= 1/(10 log log
|D|) and the complete list of imaginary quadratic fields of class number h
for every h <= 1500. Its own door analysis ranks the abscissa first: moving
it from 7/8 to 1/2 multiplies the bound by about 2.9. Its code takes sigma0
as a parameter.

This hunt cashes that in, and does not trust the parameter:

1. a line-by-line audit of the sibling's written proof at sigma0 = 1/2, with
   every sigma0-dependent step rederived;
2. the cutoff table D_GRH(h), from an Arb-enclosed cover with no gaps, with
   sigma0 = 1/2, by importing the sibling's modules unchanged;
3. an exact class-number search over |D| <= D_GRH(5000), completing the list
   of imaginary quadratic fields of class number h for every h <= 5000.

Every result is stated as **proved, given GRH for the real primitive
characters chi_D** (no zero of L(s, chi_D) with Re s > 1/2), never
unconditional. It is a GRH-conditional theorem whatever happens to the
claim of 2026-11-20; if that archive is accepted by a kernel, the hypothesis
is discharged.

Controls: the bound against the exact L(1, chi_D) of every field found
(with its detection floor, a factor 1.449 in L); the
two halves of the inequality separately at real characters with zeros from
PARI; the published GRH bound of Lamzouri, Li and Soundararajan; monotonicity
in sigma0 against the sibling's 7/8 cover; a planted sign fault; the lists
against the sibling's h <= 1500 run, Watkins, Holmin and Kurlberg (odd h),
Cremona and Sutherland, Garcia, Grenie, Lee and Molteni (their table, and
their per-field file for h <= 2000), PARI, and, since review, an independent
full-range sweep (truncated Euler products plus PARI) that shares no code
with the class-number program.

## Resource boundary

Four shared cores and 15 GB. At most three search processes at a time, each
under 3 GB, about 4 CPU-hours in total. Time one unit and write the estimate
in `RUNS.md` before the scaled run; every chunk is a checkpoint. No paid
compute, no push, no commit. Write only this directory and the session
scratchpad; the sibling hunt is imported, never edited.

```huntspec
id: grh_class_number
question: Given GRH for the real primitive characters chi_D, what cutoff D_GRH(h) does the two-cutoff Littlewood bound give at abscissa 1/2, and for which H does an exact search below D_GRH(H) complete the imaginary quadratic class number lists h <= H?
frontier: Watkins 2004 unconditional h <= 100; under GRH every h <= 2000 (Garcia, Grenie, Lee, Molteni, arXiv:2610.14257, 9 Oct 2026, largest |D| 1062350083; whether their list below their cutoff also depends on GRH through PARI's class-group routine is unresolved here), so the delta is the range 2000 < h <= 5000 and odd h < 10^6 as counts (Holmin, Jones, Kurlberg, McLeman, Petersen); under the 7/8 half-plane every h <= 1500 (hunts/qrh_class_number, D(1500) = 12409254457)
proposed_attack: the sibling hunt's two-cutoff bound with Hadamard positivity re-audited at sigma0 = 1/2, an Arb-enclosed cover for D_GRH(h), then a blocked reduced-form sieve with direct enumeration of the forms with large first coefficient over all |D| <= D_GRH(5000)
dead_routes:
  - The sibling's cn.c unchanged at H = 5000, measured at more than 20 CPU-hours because its filter was tuned for H <= 1500 and every listed field pays a scalar exact count
  - Zero pairing (beta and 1 - beta at one height), which is vacuous at abscissa 1/2
  - Explicit zero counting for the low zeros, whose error term exceeds the main term near height zero (recorded by the sibling hunt)
required_oracles:
  - Arb ball arithmetic (python-flint, 128 bits) for every constant in the inequality and every cell of the cover
  - Exact class numbers from reduced-form counting, checked against brute force and against the sibling hunt's cn.c
  - The sibling hunt's lists for h <= 1500, identified by sha256
  - Watkins' published counts for h <= 100 (OEIS A046125, A038552) and the Holmin-Kurlberg table of F(h) for odd h
  - PARI qfbclassno and lfunzeros as unrelated implementations for cross-checks
kill_conditions:
  - Any exact L(1, chi_D) falls below the claimed lower bound
  - A step of the written proof fails at sigma0 = 1/2 or uses a property of the zeros that GRH for chi_D does not supply
  - The bound at 1/2 is not stronger than the bound at 7/8 on some cell of the cover, or exceeds the published GRH bound by a margin that the zero-term control does not account for
  - The lists for h <= 1500 differ from the sibling hunt's run in any count or any largest discriminant
  - The class-number code disagrees with brute force, cn.c, PARI, Watkins or Holmin-Kurlberg on any checked discriminant or count
agents_may:
  - derive
  - compute bounded ranges
  - implement local instruments and tests
  - reuse the sibling hunt's modules by import
agents_may_not:
  - claim the result unconditionally
  - claim novelty from an empty search
  - promote their own claim
  - read, replay or vouch for the archive of 2026-11-20
  - edit the sibling hunt or any shared file
```
