import json, subprocess, urllib.request, sys
def key(name):
    return subprocess.run(["infisical","secrets","get",name,"--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
K = key("instabox")
def get(path):
    req = urllib.request.Request("https://api.instabox.sh"+path, headers={"X-API-Key": K, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.loads(r.read())
for p in ["/v1/me","/v1/orgs","/v1/usage","/v1/templates"]:
    try:
        d = get(p)
    except Exception as e:
        d = {"error": str(e)}
    s = json.dumps(d)
    print(p, s[:1500]); print()
d = get("/v1/machines?limit=100")
for m in d.get("machines", []):
    print(m["id"], m["name"], m["state"], m.get("spec"), m.get("metadata"))
