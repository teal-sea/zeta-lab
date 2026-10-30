import subprocess
key = subprocess.run(["infisical","secrets","get","novita","--projectId","36d20a40-4684-48bb-9351-010ec83b0cd9","--env","prod","--plain","--silent"],capture_output=True,text=True,check=True).stdout.strip()
from novita_sandbox.core import Template, Sandbox
print("delete template:", Template.delete("6u3xl5rrw6n31q0ac7hb", api_key=key))
print("quota usage now:", Sandbox.get_quota(api_key=key).usage)
