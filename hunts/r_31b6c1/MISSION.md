# Hunt R-31B6C1: Krenn-Gu 8x3: build the orbit-reduced polynomial system and price the elimination

CONTINUATION of R-322DAE
Source: operator
Reference: prize:krenn-gu:n8-d3-orbit-reduced-system

This run builds the layer R-322DAE was forbidden to touch: the polynomial system itself.

First run only, in this order:

(1) CALIBRATION GATE. Build the generator pipeline for 6x3 first, where the answer is known, and confirm it reproduces the no-complex-witness verdict of algal/krenn-gu-6x3-certificate. A pipeline that cannot reproduce a settled instance is not evidence about an open one. If the gate fails, STOP and report that; it is a real result and it is worth more than an unvalidated 8x3 number.

(2) EMIT the 8x3 generators expressed over the 31 orbit representatives, or the 57 H x S2 pair orbits if calibration shows that is the working quotient. Deliver as data: generator count, distinct monomial count, degree profile, and the exact map from representative to generator.

(3) PRICE the elimination. Attempt Groebner or CAD elimination on the reduced ideal under a hard cap (60 mins, 8GB memory limit is implied by the container, do not set it yourself) and report wall clock, peak memory, solver and configuration, and exactly where it stopped.

The nominal system recorded there is 252 variables and 6561 equations. 6561 = 3^8, one equation per vertex colouring, is confirmed. 252 = 28 edges of K8 x 9 is Fulcrum's inference from the 6x3 shape 15 x 9 = 135 and is NOT confirmed; establish the true variable indexing against algal/krenn-gu-6x3-certificate before relying on either number, and say plainly in RESULTS.md which one you found.
