import sys, signal, time, dataclasses
import zeta_simple_zeros.verify_seven as vs
num, den = int(sys.argv[1]), int(sys.argv[2])
vs.TARGET_NUMERATOR, vs.TARGET_DENOMINATOR = num, den
def bail(*a): print(f"target={num}/{den} TIMEOUT after 2400s (not refuted, not accepted)", flush=True); sys.exit(3)
signal.signal(signal.SIGALRM, bail); signal.alarm(2400)
t0=time.perf_counter()
try:
    r = vs.verify_seven(); d = dataclasses.asdict(r) if dataclasses.is_dataclass(r) else vars(r)
    print(f"target={num}/{den}={num/den:.7f} ACCEPTED nodes={d.get('nodes')} depth={d.get('maximum_depth')} wall={time.perf_counter()-t0:.0f}s", flush=True)
except RuntimeError as e:
    print(f"target={num}/{den}={num/den:.7f} REFUTED-AT-GRID: {str(e)[:160]} wall={time.perf_counter()-t0:.0f}s", flush=True)
