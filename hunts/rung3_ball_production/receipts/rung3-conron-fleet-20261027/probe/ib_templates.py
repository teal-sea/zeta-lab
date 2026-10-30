import json, subprocess, urllib.request
K = subprocess.run(["infisical","secrets","get","instabox","--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
req = urllib.request.Request("https://api.instabox.sh/v1/templates", headers={"X-API-Key": K})
d = json.loads(urllib.request.urlopen(req, timeout=60).read())
for t in d["templates"]:
    if t.get("creatable") and t.get("latest"):
        print(t["id"], t["version"], t.get("description","")[:80], t.get("defaultSpec"), "default" if t.get("default") else "")
