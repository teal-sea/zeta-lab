import subprocess, time, json
key = subprocess.run(["infisical","secrets","get","novita","--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
from novita_sandbox.core import Template
t = Template().from_template("base").apt_install(["zstd"])
t0 = time.time()
info = Template.build(t, "zr3c-conron-2x4", cpu_count=2, memory_mb=4096, api_key=key,
                      on_build_logs=lambda e: print("LOG", str(e)[:300], flush=True))
print("BUILT", json.dumps({k: str(getattr(info, k, None)) for k in ("template_id","build_id","alias","name","tags")}), round(time.time()-t0,1), flush=True)
