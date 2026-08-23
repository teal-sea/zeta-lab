import dataclasses, time, sys
import zeta_simple_zeros.verify_seven as vs
vs.TARGET_NUMERATOR = 191
vs.TARGET_DENOMINATOR = 50000
print("effective target:", vs.TARGET_NUMERATOR, "/", vs.TARGET_DENOMINATOR, "=", vs.TARGET_NUMERATOR/vs.TARGET_DENOMINATOR, flush=True)
t0 = time.perf_counter()
try:
    rep = vs.verify_seven()
except Exception as e:
    print("FAILED:", type(e).__name__, str(e)[:500]); sys.exit(1)
dt = time.perf_counter() - t0
d = dataclasses.asdict(rep) if dataclasses.is_dataclass(rep) else dict(vars(rep))
for k, v in d.items():
    print(f"{k}={v}")
print(f"wall_seconds={dt:.1f}")
