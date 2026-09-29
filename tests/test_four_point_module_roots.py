"""The candidate four-point package must not share a module root with lean/bridge.

The candidate (`hunts/ainta_seven_point/lean-four-point`) requires
`Zeta23Bridge` by path, and Lake exposes every library of a required package
to import resolution. Both declaring root `FourPoint` made every
`import FourPoint.Base` fail with "could not disambiguate the module" (run
36368994326). Static, reads text only, runs no Lake.
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CAND = os.path.join(ROOT, "hunts", "ainta_seven_point", "lean-four-point")
BRIDGE = os.path.join(ROOT, "lean", "bridge")


def roots(pkg):
    """Module roots of every `[[lean_lib]]` in a lakefile.toml (text scan, so
    it also runs on the repo's Python 3.10 which has no tomllib)."""
    text = open(os.path.join(pkg, "lakefile.toml")).read()
    out = set()
    for block in re.split(r"^\[\[lean_lib\]\]", text, flags=re.M)[1:]:
        block = re.split(r"^\[", block, flags=re.M)[0]
        block = "\n".join(l for l in block.splitlines() if not l.lstrip().startswith("#"))
        r = re.search(r"^roots\s*=\s*\[([^\]]*)\]", block, re.M)
        if r:
            out.update(re.findall(r'"([^"]+)"', r.group(1)))
        else:
            out.add(re.search(r'^name\s*=\s*"([^"]+)"', block, re.M).group(1))
    return out


def test_module_roots_disjoint():
    shared = roots(CAND) & roots(BRIDGE)
    assert not shared, "module roots visible in both packages: %s" % sorted(shared)


def test_disk_roots_disjoint():
    def on_disk(pkg):
        return {n[:-5] if n.endswith(".lean") else n for n in os.listdir(pkg)
                if n.endswith(".lean") or os.path.isdir(os.path.join(pkg, n))}
    shared = (on_disk(CAND) & on_disk(BRIDGE)) - {".lake"}
    assert not shared, "top-level module paths on disk in both packages: %s" % sorted(shared)


def test_candidate_imports_stay_in_own_root():
    (own,) = roots(CAND)
    bad = []
    for dp, _, fs in os.walk(CAND):
        for fn in fs:
            if fn.endswith(".lean"):
                for ln in open(os.path.join(dp, fn)):
                    m = re.match(r"(?:public )?import (\w+)", ln)
                    if m and m.group(1) not in (own, "Mathlib", "Zeta23Ext", "Zeta23", "Std", "Lean"):
                        bad.append((fn, ln.strip()))
    assert not bad, bad[:3]


def test_generator_and_preflight_follow_lakefile():
    (own,) = roots(CAND)
    sys.path.insert(0, os.path.join(ROOT, "hunts", "ainta_seven_point"))
    src = open(os.path.join(ROOT, "hunts", "ainta_seven_point", "four_point_gen.py")).read()
    assert re.search(r'^LIB = "%s"$' % own, src, re.M)
    pre = open(os.path.join(ROOT, "hunts", "ainta_seven_point", "four_point_preflight.py")).read()
    assert '"lean-four-point", "%s"' % own in pre
