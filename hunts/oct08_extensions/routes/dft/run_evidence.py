#!/usr/bin/env python3
"""Record one bounded run; stores outputs beside this script."""
import datetime, hashlib, json, platform, subprocess, sys, time
from pathlib import Path
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inputs = [root/'verify.py'] + sorted((root/'sources').glob('*.tex'))
before = {str(p.relative_to(root)):sha(p) for p in inputs}
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
t0 = time.monotonic()
run = subprocess.run([sys.executable,str(root/'verify.py')], capture_output=True,
                     text=True,timeout=10,check=False)
elapsed = time.monotonic()-t0
after = {str(p.relative_to(root)):sha(p) for p in inputs}
assert before == after, 'input changed during run'
(root/'result.json').write_text(run.stdout)
(root/'stderr.txt').write_text(run.stderr)
assert run.returncode == 0, run.stderr
result = json.loads(run.stdout)
manifest = {
 'schema_version':1,'claim_id':'dft-h24-finite-certificate-v1',
 'repository':{'commit':result['source_commit'],'dirty':True,
   'meaning':'Pinned upstream source commit; extension files are uncommitted workspace artifacts.'},
 'command':[sys.executable,str(root/'verify.py')],
 'environment':{'software':[platform.python_implementation()+' '+platform.python_version()],
                'hardware':platform.machine()+'; one process, standard library only'},
 'mathematics':{
   'assertion_tested':'Exact h24 counts and rational exponent bound; scalar cancellation, reverse scheduling, small phase identities and negative controls.',
   'coefficient_domain':'Integers, rational numbers, bit vectors over F2; no floating proof.',
   'conventions':'Unnormalized positive-exponent DFT; ordered adjacent triples; all auxiliary initial values permitted.',
   'inputs':[{'path':p,'sha256':s} for p,s in before.items()],
   'bounds':{'main_h':24,'scalar_schedule_h':7,'phase_dimension':7,
             'phase_cases':8192,'wall_timeout_seconds':10},
   'non_claims':['No full-array construction','No formal universal proof','No global parameter optimality','No practical FFT or bit complexity improvement']},
 'randomness':{'used':False,'generator':'none','seed':None},
 'run':{'started_at':start,'runtime_seconds':elapsed,'exit_status':run.returncode},
 'outputs':[{'path':f,'sha256':sha(root/f)} for f in ('result.json','stderr.txt')],
 'checks':['Upstream Git blob identity','Exact integer counts','Positive rational exponential partial sum',
           'Exact rational epsilon comparison','S_h orbit coefficient identity',
           'Arbitrary auxiliary forward/reverse schedule','8192 exact phase cases','Five negative controls'],
 'result':'Finite assertions passed. Universal parameter extension is separately derived in PROOF.md; independent audit pending.',
 'residual_risks':['Self-review only','Upstream local compiler and all-length transport are written lemmas, not replayed formal proofs here',
                   'v1 manifest; inputs hashed before and after; wall timeout enforced but no OS memory cap']}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f'passed in {elapsed:.4f}s; result.json and manifest.json written')
