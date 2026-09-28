# Referee progress, 2026-09-28

**ACTIVE: L=1.19 independent assembly on Modal.** Approved ceiling four
core-hours. Pilot 1 stopped safely at its precision guard after 5.43 seconds;
pilot 2 passed at 1280 bits in 71.383 seconds. Full assembly app
`ap-zyqkre7VOF1BRnS7SjZEWi` is active with ten single-use one-core containers.
At least 69 of 100 units are complete; receipts are in outputs_L119/548f9a4.
No assembly unit has failed after the precision repair. See RUNS.md.

Assembly source 548f9a4, CC degree 192, 500 even modes. Every unit matrix is
on volume oob-envelope-referee under l119/548f9a4/panels_START_STOP.
The pilot supplied panels 990..999; the batch supplies the other 99 units.
Reducer source e5f8885 is ready but not launched. It verifies hashes,
source identity and complete panel coverage before using the matrix.
It tests the fixed exact shift 5.718e-48, aims at outward endpoint
5.7179e-48, encloses a Rayleigh witness, and requires rejection of the
-1e-47 I lesion with an enclosed negative witness. Scientific positivity
remains UNRESOLVED until reduction completes.

Independent tail budget already passes: eps_D <1.490e-184 and
 eps_B <1.553e-90. REVIEW.md opens with the new L=1.19 audit. Historical
L=4/5 evidence remains under its own heading and at b65ef69.

Next: watch batch to stopped, reconcile 100 receipts, record compute in
RUNS, then launch one reducer with revision e5f8885 and unit
reduce_548f9a4. Monitor it to stopped; download and verify its evidence,
update the five-line verdict, run scope/lexical checks and commit. No push.
No author code read; all writes confined to referee/. No local numerical
work, no external messages or publication.
