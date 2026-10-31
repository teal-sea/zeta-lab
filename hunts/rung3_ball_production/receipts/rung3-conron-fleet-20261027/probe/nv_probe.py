import os, subprocess, json
os.environ["NOVITA_API_KEY"] = subprocess.run(["infisical","secrets","get","novita","--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
from novita_sandbox.core import Sandbox
try:
    q = Sandbox.get_quota()
    print("quota", q)
except Exception as e:
    print("quota error", type(e).__name__, str(e)[:500])
try:
    lst = Sandbox.list()
    items = lst.next_items() if hasattr(lst, "next_items") else lst
    print("running sandboxes:", [ (s.sandbox_id, getattr(s,'metadata',None)) for s in items])
except Exception as e:
    print("list error", type(e).__name__, str(e)[:500])
