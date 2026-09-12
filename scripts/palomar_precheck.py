#!/usr/bin/env python3
"""Pre-flight check of a Palomar Registry submission.

Checks the mechanical requirements of PalomarPolicy CONTRIBUTING.md sections
2 and 3 against a local checkout, before the submission is sent. A FAIL here
is a FAIL at Palomar intake; the point is to find it locally rather than in
public.

Scope, honestly: this covers the MECHANICAL gate only. It says nothing about
the editorial review, which is a language model working through the prompts in
PalomarPolicy/prompts/ and which is where the mandatory notability floor lives
(rubric.json: minimum_score 4, mandatory_reject_below_minimum ["notability"]).
Passing this script means intake will not bounce you; it does not mean you
will be registered.

It is a reimplementation from the published policy, not a copy of Palomar's
own verifier. The authoritative implementation is
PalomarSubmission/scripts/submission_contract.py. Where they disagree, that
one is right and this one is a bug.

It also runs the correspondence checks in scripts/palomar_correspondence.py,
which is the half that would have caught both refusals that were ours: a
well-formed record describing a different object than the comparator selected.

Usage, and prefer the first form. Naming only the comparator derives the
project directory and the metadata path from lean/palomar-pairs.json, so no
argument of a submission is chosen by hand -- which is precisely how the
2026-08-25 submission went out against the wrong record:

    python3 scripts/palomar_precheck.py <repo_root> <comparator_path>
    python3 scripts/palomar_precheck.py <repo_root> <project_dir> <comparator_path> [metadata_path]

Zeta Lab's submissions (project and metadata both derived, pass neither):
    python3 scripts/palomar_precheck.py . lean/comparator.json
    python3 scripts/palomar_precheck.py . lean/comparator-dh.json
    python3 scripts/palomar_precheck.py . lean/bridge/comparator-v2.json
"""
import json,os,re,subprocess,sys
try: import yaml
except ImportError: sys.exit("pip install pyyaml")
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import palomar_correspondence as corr

REPO=sys.argv[1] if len(sys.argv)>1 else "."
# Two forms. `<repo> <comparator>` derives the project dir and the metadata
# path from lean/palomar-pairs.json and is the one to use: nothing about a
# submission is then chosen by hand, which is the failure that cost the
# 2026-08-25 cycle. The long form stays for a surface not yet in the registry.
_short=len(sys.argv)>2 and sys.argv[2].endswith(".json")
try:
    if _short:
        CMP=sys.argv[2]; PROJ=corr.resolve_project(CMP,REPO); META=corr.resolve(CMP,REPO)
    else:
        PROJ=sys.argv[2] if len(sys.argv)>2 else "lean"   # selected project (sec 6.1)
        CMP =sys.argv[3] if len(sys.argv)>3 else "lean/comparator.json"
        META=sys.argv[4] if len(sys.argv)>4 else corr.resolve(CMP,REPO)
except KeyError as e: sys.exit(f"FAIL  {e}")
P=lambda *a: os.path.join(REPO,*a)
ok=[];warn=[];fail=[]
def chk(c,m,w=False):(ok if c else (warn if w else fail)).append(m)

# --- 2.5 licence at REPOSITORY ROOT (always, even for a sub-project) ---
NAMES={"license","licence","copying","unlicense","ofl"}
EXT={"",".md",".markdown",".txt"}
lics=[f for f in os.listdir(REPO) if os.path.isfile(P(f)) and not os.path.islink(P(f))
      and os.path.splitext(f.lower())[0] in NAMES and os.path.splitext(f.lower())[1] in EXT]
chk(len(lics)==1,f"root licence file: exactly one required, found {lics}")

# --- 2.1 toolchain (project-local takes precedence) ---
tcp=P(PROJ,"lean-toolchain") if os.path.exists(P(PROJ,"lean-toolchain")) else P("lean-toolchain")
tc=open(tcp).read().strip() if os.path.exists(tcp) else ""
m=re.fullmatch(r"leanprover/lean4:(v.+)",tc)
chk(bool(m),f"lean-toolchain names a Lean release: {tc!r} (min v4.28.0)")
def vkey(v):
    b=re.match(r"v(\d+)\.(\d+)\.(\d+)",v)
    return tuple(int(x) for x in b.groups()) if b else (0,0,0)
if m: chk(vkey(m.group(1))>=(4,28,0),f"toolchain {m.group(1)} >= minimum v4.28.0")
chk(m and "-rc" not in m.group(1),f"toolchain {tc} is a release candidate, not a stable release; permitted by policy (only the v4.28.0 minimum is enforced) but confirm lean4export has a matching tag",w=True)

# --- 2.1 exactly one lakefile, manifest committed ---
lf=[f for f in ("lakefile.toml","lakefile.lean") if os.path.exists(P(PROJ,f))]
chk(len(lf)==1,f"exactly one lakefile in selected project: {lf}")
if lf: chk(os.path.getsize(P(PROJ,lf[0]))<=1<<20,f"{lf[0]} <= 1 MiB")
chk(os.path.exists(P(PROJ,"lake-manifest.json")),"lake-manifest.json committed")

# --- 2.4 dependency pins ---
mf=P(PROJ,"lake-manifest.json")
if os.path.exists(mf):
    for pk in json.load(open(mf)).get("packages",[]):
        if pk.get("type")=="git":
            u,r=pk.get("url",""),pk.get("rev","")
            chk(re.fullmatch(r"https://github\.com/[^/]+/[^/?#]+",u.rstrip("/")) is not None,
                f"dep {pk.get('name')}: credential-free public URL ({u})")
            chk(re.fullmatch(r"[0-9a-f]{40}",r) is not None,
                f"dep {pk.get('name')}: pinned to 40-char lowercase SHA")

# --- 2.3 comparator.json ---
c=json.load(open(P(CMP)))
chk(os.path.getsize(P(CMP))<=1<<20,"comparator.json <= 1 MiB")
chk(set(c)<= {"challenge_module","solution_module","theorem_names","permitted_axioms",
              "definition_names","enable_nanoda"},f"comparator.json keys accepted: {sorted(c)}")
for k in ("challenge_module","solution_module","theorem_names","permitted_axioms"):
    chk(k in c,f"comparator.json has required key {k}")
chk(isinstance(c.get("theorem_names"),list) and c["theorem_names"] and
    all(isinstance(x,str) and x for x in c["theorem_names"]),"theorem_names nonempty array of nonempty strings")
chk(set(c.get("permitted_axioms",[]))<={"propext","Quot.sound","Classical.choice"},
    f"permitted_axioms subset of the three allowed: {c.get('permitted_axioms')}")
chk(c.get("challenge_module")!=c.get("solution_module"),"Challenge and Solution modules distinct")
for k in ("challenge_module","solution_module"):
    chk(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*",p) for p in str(c.get(k,"")).split(".")),
        f"{k} is a valid dotted Lean module name")

# --- 2.2 Challenge size ---
ch=P(PROJ,c["challenge_module"].replace(".","/")+".lean")
if os.path.exists(ch):
    b=os.path.getsize(ch); L=sum(1 for _ in open(ch,encoding="utf-8"))
    chk(b<=100*1024 and L<=1000,f"Challenge within hard limit (100 KiB/1000 lines): {b}B/{L} lines")
    chk(b<=32*1024 and L<=300,f"Challenge under mechanical-warning threshold (32 KiB/300 lines): {b}B/{L} lines",w=True)
    imps=re.findall(r"^import\s+(\S+)",open(ch,encoding="utf-8").read(),re.M)
    chk(all(i.split(".")[0] in ("Mathlib","Init","Std","TauCeti","CSLib") for i in imps),
        f"Challenge imports approved roots only: {imps}")
else: fail.append(f"Challenge source not found at {ch}")

# --- no compiled artifacts tracked ---
tr=subprocess.run(["git","-C",REPO,"ls-files"],capture_output=True,text=True).stdout.split()
bad=[f for f in tr if os.path.splitext(f)[1] in
     (".olean",".ilean",".a",".bc",".dll",".dylib",".o",".obj",".so",".trace")]
chk(not bad,f"no compiled artifacts tracked: {bad[:5]}")
chk(not os.path.exists(P(".gitmodules")),"no git submodules")

# --- 3 formalization.yaml ---
raw=open(P(META),'rb').read()
chk(len(raw)<=256*1024,"formalization.yaml <= 256 KiB")
class NoDup(yaml.SafeLoader): pass
def nodup(loader,node,deep=False):
    seen=set()
    for k,_ in node.value:
        key=loader.construct_object(k,deep=deep)
        if key in seen: raise yaml.YAMLError(f"duplicate key {key}")
        seen.add(key)
    return yaml.SafeLoader.construct_mapping(loader,node,deep)
NoDup.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,nodup)
try:
    y=yaml.load(raw,Loader=NoDup); chk(isinstance(y,dict),"one top-level YAML mapping, no duplicate keys")
except yaml.YAMLError as e:
    fail.append(f"formalization.yaml parse: {e}"); y={}

g=lambda *k: (lambda d: d)(_get(y,*k))
def _get(d,*ks):
    for k in ks:
        if not isinstance(d,dict): return None
        d=d.get(k)
    return d
chk(isinstance(_get(y,"project","name"),str) and _get(y,"project","name"),"project.name nonempty string")
d=_get(y,"project","description")
chk(isinstance(d,str) and 0<len(d)<=10000,f"project.description nonempty, <=10000 chars (len={len(d) if isinstance(d,str) else 'n/a'})")
au=_get(y,"project","authors")
chk(isinstance(au,list) and au and all(isinstance(x,str) and x for x in au),"project.authors nonempty list of nonempty strings")
rm=_get(y,"project","responsible_maintainers")
chk(isinstance(rm,list) and rm and all(isinstance(x,str) and x for x in rm),"project.responsible_maintainers nonempty list of strings")
# licence match
lic=_get(y,"project","license")
det=None
if lics:
    t=open(P(lics[0]),encoding="utf-8").read()
    det="MIT" if "MIT License" in t else ("Apache-2.0" if "Apache License" in t else None)
chk(lic and det and lic==det,f"project.license ({lic}) == SPDX detected in {lics[0] if lics else '?'} ({det})")
ax=_get(y,"classification","arxiv")
chk(isinstance(ax,list) and 1<=len(ax)<=8 and len(set(ax))==len(ax),f"classification.arxiv 1-8 distinct codes: {ax}")
ms=_get(y,"classification","msc2020")
chk(ms is None or (isinstance(ms,list) and len(ms)<=8 and len(set(ms))==len(ms)),f"classification.msc2020 <=8 distinct: {ms}")
am=_get(y,"automation","methods")
chk(isinstance(am,list) and am and all(isinstance(x,dict) and x.get("method") for x in am),"automation.methods nonempty list of mappings with nonempty method")
chk(isinstance(_get(y,"review","status"),str) and _get(y,"review","status"),"review.status nonempty string")
chk(_get(y,"repository") is None,"repository omitted (submitted repo holds the substantive development)")

# --- 3.2 source contract ---
TYPES={"paper","book","web discussion","folklore","original-proof","other"}
RELS={"formalizes","adapts","independently-proves","background","other"}
srcs=_get(y,"sources")
chk(isinstance(srcs,list) and srcs,"sources nonempty list")
if isinstance(srcs,list):
    for i,s in enumerate(srcs):
        chk(bool(s.get("title")),f"sources[{i}] nonempty title")
        chk(s.get("relationship") in RELS,f"sources[{i}] relationship in vocabulary: {s.get('relationship')!r}")
        if "type" in s: chk(s["type"] in TYPES,f"sources[{i}] type in vocabulary: {s['type']!r}")
    orig=[s for s in srcs if s.get("type")=="original-proof"]
    A1 = bool(orig) and all(s.get("relationship")=="other" for s in orig) and \
         all(s.get("relationship") in ("background","other") for s in srcs)
    A2 = (not orig) and any(s.get("relationship") in ("formalizes","adapts","independently-proves") for s in srcs)
    chk(A1 or A2,f"sources satisfy exactly one origin alternative (derived: {'original' if A1 else 'source-based' if A2 else 'NEITHER'})")
rf=_get(y,"related_formalizations") or []
for i,r in enumerate(rf): chk(bool(r.get("id")),f"related_formalizations[{i}] has id")

# --- 4 correspondence: does the record describe what the comparator selects? ---
cok,cwarn,cfail=corr.check(REPO,CMP,META)
ok+=cok; warn+=cwarn; fail+=cfail

print("\n".join("  PASS  "+m for m in ok))
if warn: print("\n".join("  WARN  "+m for m in warn))
if fail: print("\n".join("  FAIL  "+m for m in fail))
print(f"\n{len(ok)} pass, {len(warn)} warn, {len(fail)} FAIL")
if not fail:
    print(f"\nSubmit these two paths, copied not chosen:\n\n    comparator  {CMP}\n    metadata    {META}\n")
sys.exit(1 if fail else 0)
