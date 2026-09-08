# Height-kernel continuation, N=10000 only

Continue PR #207 from `3099c7ac01eeeb1542bf40478fd73d1d58e794d3`.
The coordinator selected the class with N>=10000, y=floor(sqrt(N)),
coverage on every Q_N cell and B_c<=2N. This deliverable tests N=10000,
y=100 only, keeping the full budget. The choice of class asserts no transfer.

Consume only the tight primal, basis, positive dual masses and exact moments
from Fable's PR #208 at `600ff8044ed9f5e30b9dd9ddc5f488faf1af329a`.
Check whether #203's archived rational vector equals that exact optimizer.
Retain all attainable-cell inequalities in the slack parameterization.

Determine whether this class meets the actual height kernel. Supply an
exact witness or an exact exclusion and a quantitative variance estimate,
then explicitly pay the smallest-atom loss to bound linear excess.

Ownership: new files here, a focused test, regenerated CONTEXT.md and a
continuation pointer in FINITE_TRANSFER.md. Fable's files and original
archives remain unchanged. Use existing algebra/data, one numerical thread,
no larger-N run, no general audit or optimization batch. Leave #207 open.
