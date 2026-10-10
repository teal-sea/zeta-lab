#!/usr/bin/env python3
"""Bounded reproducible run; manifest paths are relative to routes/."""
import datetime, hashlib, json, platform, subprocess, sys, time
from pathlib import Path
here=Path(__file__).resolve().parent
root=here.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[here/'verify.py',here/'PROOF.md']+sorted((root/'dft'/'sources').glob('*.tex'))
before={str(p.relative_to(root)):sha(p) for p in inputs}
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
t0=time.monotonic()
run=subprocess.run([sys.executable,str(here/'verify.py')],capture_output=True,text=True,timeout=10)
elapsed=time.monotonic()-t0
assert before=={str(p.relative_to(root)):sha(p) for p in inputs}
(here/'result.json').write_text(run.stdout)
(here/'stderr.txt').write_text(run.stderr)
assert run.returncode==0,run.stderr
result=json.loads(run.stdout)
manifest={
 'schema_version':1,'claim_id':'dft-central-compression-h24-v1',
 'repository':{'commit':result['source_commit'],'dirty':True,
  'meaning':'Pinned upstream collection; extension is an uncommitted workspace artifact.'},
 'command':[sys.executable,str(here/'verify.py')],
 'environment':{'software':[platform.python_implementation()+' '+platform.python_version()],
  'hardware':platform.machine()+'; one standard-library process'},
 'mathematics':{
  'assertion_tested':'Compressed central map, rational scalar schedule and inverse, fixed-side rank, exact h24 exponent certificate.',
  'coefficient_domain':'Exact integers and rational numbers; no floating point proof.',
  'conventions':'Ordered side edges; arbitrary auxiliary values; exact complex-field downstream model.',
  'inputs':[{'path':p,'sha256':s} for p,s in before.items()],
  'bounds':{'main_h':24,'schedule_h':[7,8],'literal_rank_h':[4,5,7,9,10],'wall_timeout_seconds':10},
  'non_claims':['No full DFT implementation','No formal universal proof','No novelty claim','No practical or bit-complexity improvement']},
 'randomness':{'used':False,'generator':'none','seed':None},
 'run':{'started_at':start,'runtime_seconds':elapsed,'exit_status':run.returncode},
 'outputs':[{'path':str((here/f).relative_to(root)),'sha256':sha(here/f)} for f in ('result.json','stderr.txt')],
 'checks':['Pinned upstream blob identity','Rational eight-row schedule and inverse',
  'Literal matrix Gaussian elimination','Exact spectrum and trace','Rational exponent inequalities','Five negative controls'],
 'result':'Finite checks passed; universal argument is in PROOF.md, undergoing separate independent audit.',
 'residual_risks':['Written upstream compiler and label lemmas are not formally replayed here',
  'v1 manifest; input hashes verified before and after; wall timeout but no OS memory cap']}
(here/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'passed in {elapsed:.4f}s; manifest paths relative to routes/')
