import sys
sys.path.insert(0, "<repo>/.claude/worktrees/rung3-ball-production/hunts/rung3_ball_production")
import conron_fleet as F
ib = F.InstaBox()
mid = sys.argv[1]
op = ib.delete(mid)
print("delete op", op and op.get("id"))
import time
while op:
    o = ib.op(op["id"]); print(o["state"])
    if o["state"] in ("succeeded", "failed"): break
print("machine now:", ib.machine(mid))
F.registry_add({"provider": "instabox", "id": mid, "event": "deleted", "by": "hand"})
