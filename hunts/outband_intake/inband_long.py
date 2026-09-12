import json, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "frontier_math"))
from configuration_lp import solve
OUT = HERE / "artifacts" / "lane-a-control-inband-long.json"
rows = []
for X, J in [(240.,960),(320.,1280),(480.,1920),(640.,2560)]:
    t0=time.time(); r=solve(J=J,X=X,eps=0.4/X,A_out=None); el=round(time.time()-t0,1)
    rows.append({"X":X,"J":J,"value":r["value"],"wall_seconds":el})
    OUT.write_text(json.dumps(rows,indent=1)+"\n")
    print(f"in-band X={X:6.1f} J={J:5d}  {r['value']:.7f}  excess {r['value']-0.6725007036794116:+.6f}  {el}s", flush=True)
