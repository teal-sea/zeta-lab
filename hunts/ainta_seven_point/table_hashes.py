from zeta_simple_zeros.kernel import build_second_derivative_lower_table, build_kernel_table, table_sha256
from zeta_simple_zeros.verify_seven import GRID, PRECISION_BITS, PRESSURE_CUTOFF_CELLS
import flint, math
cc = PRESSURE_CUTOFF_CELLS + 8
k = build_kernel_table(GRID, cc, PRECISION_BITS)
s = build_second_derivative_lower_table(GRID, cc, start_index=3_800, precision=PRECISION_BITS)
print("flint", flint.__version__)
print("kernel_table_sha256          =", table_sha256(k))
print("second_derivative_table_sha256=", table_sha256(s))
fin = [v for v in s if math.isfinite(v)]
print("finite entries:", len(fin), "min:", min(fin), "max:", max(fin))
