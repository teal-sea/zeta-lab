import subprocess, json, time
key = subprocess.run(["infisical","secrets","get","novita","--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
from novita_sandbox.core import Sandbox
t0=time.time()
sbx = Sandbox.create(timeout=300, metadata={"project":"zeta-rung3-conron","purpose":"probe"}, api_key=key)
print("created", sbx.sandbox_id, round(time.time()-t0,1), "s")
open("<cache>/rung3-conron-fleet-20261027/vms.jsonl","a").write(json.dumps({"provider":"novita","id":sbx.sandbox_id,"name":"probe","created_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),"shard":"probe"})+"\n")
try:
    info = sbx.get_info()
    print("info", {k: getattr(info,k,None) for k in ("template_id","name","cpu_count","memory_mb","started_at","end_at","metadata")})
    r = sbx.commands.run("nproc; free -m; df -h / /home/user /tmp 2>/dev/null; python3 --version; which zstd xz gzip; cat /etc/os-release | head -3; ldd --version | head -1; id; grep -m1 'model name' /proc/cpuinfo", timeout=60)
    print(r.stdout); print(r.stderr)
finally:
    sbx.kill()
    print("killed")
    open("<cache>/rung3-conron-fleet-20261027/vms.jsonl","a").write(json.dumps({"provider":"novita","id":sbx.sandbox_id,"event":"deleted","utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())})+"\n")
