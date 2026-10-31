import sys, json
sys.path.insert(0, "<repo>/.claude/worktrees/rung3-ball-production/hunts/rung3_ball_production")
import conron_fleet as F
ib = F.InstaBox()
r = ib.exec(sys.argv[1], sys.argv[2], timeout=int(sys.argv[3]) if len(sys.argv) > 3 else 120)
print(r.get("exitCode")); print(r.get("stdout", "")[-3000:]); print(r.get("stderr", "")[-3000:])
