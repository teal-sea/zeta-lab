"""Chain lane of hunt #147 (`dbn_pt_height`): the files are checked, not trusted.

Three things are pinned here.

1. **Every quotation is re-read.**  `chain.json` holds 124 quotations, each an
   exact substring (after collapsing whitespace; HTML and JSON after removing
   tags and decoding entities) of a source whose SHA-256, URL and retrieval
   time are in `sources.json`.  When the download cache exists (it does on the
   box this hunt ran on), every quotation is re-read from the cached bytes at
   its locator: a TeX line, a file at a git commit, a blog comment anchor, a
   GitHub comment id, or a bundle member found by basename and SHA-256.  When
   the cache is absent the re-reading tests skip and say so; the shape checks
   still run.
2. **Every stated identity is re-derived**, in exact rationals or in interval
   arithmetic (mpmath `iv`, 256 bits), never read back from the JSON.
3. **Every number in CHAIN.md and REDUCTION.md is registered**: each run of
   digits in those two files must occur in `chain.json` or `sources.json`,
   whose contents are pinned by (1) and (2).  Every `[Q:ID]` citation must name
   a quotation that exists.

The lexical rules of this tree are also enforced on the chain lane's own
files, more strictly than the hunt-wide gate: no em dash and no occurrence of
the reserved stem at all.
"""

from __future__ import annotations

import hashlib
import html
import json
import os
import re
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
if str(REPO) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(REPO))

CHAIN = json.loads((HERE / "chain.json").read_text(encoding="utf-8"))
SOURCES = json.loads((HERE / "sources.json").read_text(encoding="utf-8"))
SRC = SOURCES["sources"]
CACHE = Path(os.environ.get("DBN_CACHE_ROOT", SOURCES["cache_root"]))
QUOTES = {q["id"]: q for q in CHAIN["quotes"]}

OWN_FILES = ["MISSION.md", "CHAIN.md", "REDUCTION.md", "chain.json", "sources.json", "test_chain.py"]
STEM = "cert" + "if"
EM_DASH = "\u2014"

needs_cache = pytest.mark.skipif(not CACHE.is_dir(), reason="download cache not present on this machine")


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def strip_tags(s: str) -> str:
    s = re.sub(r"<script.*?</script>", " ", s, flags=re.S)
    s = re.sub(r"<style.*?</style>", " ", s, flags=re.S)
    return norm(html.unescape(re.sub(r"<[^>]+>", " ", s)))


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# shape and lexical rules
# ---------------------------------------------------------------------------


def test_own_files_exist_and_obey_the_lexical_rules() -> None:
    for name in OWN_FILES:
        text = (HERE / name).read_text(encoding="utf-8")
        assert STEM not in text.lower(), f"{name} carries the reserved stem"
        assert EM_DASH not in text, f"{name} carries an em dash"


def test_sources_have_url_time_and_digest() -> None:
    for key, s in SRC.items():
        assert s.get("note"), key
        if s["kind"] in {"file", "derived"}:
            assert re.fullmatch(r"[0-9a-f]{64}", s["sha256"]), key
            assert isinstance(s["bytes"], int) and s["bytes"] > 0, key
            assert re.fullmatch(r"2026-10-21T\d\d:\d\d:\d\dZ", s["retrieved_utc"]), key
            assert s["url"], key
        elif s["kind"] == "git":
            assert re.fullmatch(r"[0-9a-f]{40}", s["head"]), key
        elif s["kind"] == "export":
            assert re.fullmatch(r"[0-9a-f]{40}", s["commit"]), key


def test_every_cited_quote_exists() -> None:
    cited: set[str] = set()
    ref_keys = {"quotes", "gap_quotes", "mitigation"}

    def take(values) -> None:
        for v in values:
            assert isinstance(v, str), v
            cited.add(v)

    for key, node in CHAIN.items():
        if key == "quotes":
            continue
        if key in {"verdict_row2", "label_swap"}:
            for v in node.values():
                if isinstance(v, list):
                    take(v)
        elif key == "outside_review":
            take(node)
        elif isinstance(node, dict) and "quotes" in node:
            take(node["quotes"])
        elif isinstance(node, list):
            for item in node:
                if isinstance(item, dict):
                    for k in ref_keys & set(item):
                        take(item[k])
    for name in ("CHAIN.md", "REDUCTION.md"):
        cited |= set(re.findall(r"\[Q:([A-Z]{1,3}\d{1,2})\]", (HERE / name).read_text(encoding="utf-8")))
    missing = sorted(c for c in cited if c not in QUOTES)
    assert not missing, f"cited quotations that do not exist: {missing}"
    assert len(QUOTES) == len(CHAIN["quotes"]), "duplicate quotation id"


def test_every_number_in_the_notes_is_registered() -> None:
    registry = (HERE / "chain.json").read_text(encoding="utf-8") + (HERE / "sources.json").read_text(encoding="utf-8")
    for name in ("CHAIN.md", "REDUCTION.md"):
        runs = set(re.findall(r"\d+", (HERE / name).read_text(encoding="utf-8")))
        loose = sorted((r for r in runs if r not in registry), key=lambda r: (len(r), r))
        assert not loose, f"{name}: numbers with no entry in chain.json or sources.json: {loose}"


# ---------------------------------------------------------------------------
# 1. quotations re-read from the hashed cache
# ---------------------------------------------------------------------------


def _file(key: str) -> Path:
    s = SRC[key]
    p = CACHE / s["cache_path"]
    assert p.is_file(), f"{key}: cached file missing"
    assert sha256(p) == s["sha256"], f"{key}: cached bytes differ from the recorded SHA-256"
    return p


def _lines(text: str, span) -> str:
    lines = text.split("\n")
    a, b = span
    return norm("\n".join(lines[a - 1:b]))


def _bundle_member(key: str, basename: str, digest: str) -> Path:
    root = CACHE / SRC[key].get("members_root", SRC[key]["cache_path"])
    hits = []
    for d, _, files in os.walk(root):
        if basename in files:
            p = Path(d) / basename
            if sha256(p) == digest:
                hits.append(p)
    assert len(hits) == 1, f"{key}: {basename} with the recorded digest found {len(hits)} times"
    return hits[0]


def _git_show(key: str, commit: str, path: str) -> str:
    repo = CACHE / SRC[key]["cache_path"]
    out = subprocess.run(["git", "-C", str(repo), "show", f"{commit}:{path}"],
                         capture_output=True, text=True, check=True)
    return out.stdout


def _dotted(obj, dotted: str):
    for part in dotted.split("."):
        obj = obj[part]
    return obj


def _check(q: dict) -> None:
    kind, key, want, loc = q["kind"], q["source"], norm(q["text"]), q["locator"]
    if kind == "line":
        text = _file(key).read_text(encoding="utf-8")
        assert want in _lines(text, loc["lines"])
    elif kind == "repo":
        text = (REPO / loc["path"]).read_text(encoding="utf-8")
        assert want in _lines(text, loc["lines"])
    elif kind == "gitfile":
        assert want in _lines(_git_show(key, loc["commit"], loc["path"]), loc["lines"])
    elif kind == "bundle":
        p = _bundle_member(key, loc["basename"], loc["sha256"])
        assert want in _lines(p.read_text(encoding="utf-8"), loc["lines"])
    elif kind == "html_page":
        assert want in strip_tags(_file(key).read_text(encoding="utf-8", errors="replace"))
    elif kind == "html_comment":
        raw = _file(key).read_text(encoding="utf-8", errors="replace")
        start = raw.index('id="%s"' % loc["anchor"])
        end = raw.find('id="comment-', start + 10)
        assert want in strip_tags(raw[start:end if end > 0 else len(raw)])
    elif kind == "json_comment":
        rows = json.loads(_file(key).read_text(encoding="utf-8"))
        row = [r for r in rows if r["id"] == loc["comment_id"]]
        assert len(row) == 1 and row[0]["user"]["login"] == loc["author"]
        assert row[0]["created_at"] == loc["created_at"]
        assert want in norm(row[0]["body"])
    elif kind == "json_issue_body":
        rows = json.loads(_file(key).read_text(encoding="utf-8"))
        row = [r for r in rows if r["number"] == loc["issue"]]
        assert len(row) == 1 and row[0]["user"]["login"] == loc["author"]
        assert want in norm(row[0]["body"])
    elif kind == "json_field":
        obj = json.loads(_file(key).read_text(encoding="utf-8"))
        assert want in strip_tags(_dotted(obj, loc["field"]))
    elif kind == "json_comment_list":
        row = json.loads(_file(key).read_text(encoding="utf-8"))[loc["index"]]
        assert row["user"]["login"] == loc["author"] and row["created_at"] == loc["created_at"]
        assert want in norm(row["body"])
    else:  # pragma: no cover - a new kind must be taught here first
        raise AssertionError(f"unknown quotation kind {kind}")


@needs_cache
@pytest.mark.parametrize("qid", sorted(QUOTES))
def test_quotation_is_in_its_hashed_source(qid: str) -> None:
    _check(QUOTES[qid])


@needs_cache
def test_every_cached_file_still_has_its_recorded_digest() -> None:
    for key, s in SRC.items():
        if s["kind"] in {"file", "derived"}:
            _file(key)
        elif s["kind"] == "git":
            head = subprocess.run(["git", "-C", str(CACHE / s["cache_path"]), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
            assert head == s["head"], key


@needs_cache
def test_a_planted_misquote_is_refused() -> None:
    """The control: one changed character in a real quotation must fail."""
    q = dict(QUOTES["P12"])
    q["text"] = q["text"].replace("(iii)", "(ii)")
    with pytest.raises(AssertionError):
        _check(q)
    q = dict(QUOTES["P9"])
    q["text"] = q["text"].replace("630783", "630784")
    with pytest.raises(AssertionError):
        _check(q)


@needs_cache
def test_the_expect_sentence_entered_the_writeup_at_4a460d9() -> None:
    """CHAIN.md section 2: absent from further.tex at 7eff611, present at 4a460d9."""
    before = _git_show("DBN_REPO", "7eff6114efd97ed8de58d31503a6e4b464d61c18", "Writeup/further.tex")
    after = _git_show("DBN_REPO", "4a460d9b85198c78e6314f30718314160e2b1473", "Writeup/further.tex")
    assert "expect to be able" not in before and "expect to be able" in after


@needs_cache
def test_no_sweep_at_row2_parameters_in_any_commit() -> None:
    """Every file the eulerbounds path ever held is at y = 0.2; the only N0 = 630783 sweep is t = 0.17."""
    repo = CACHE / SRC["DBN_REPO"]["cache_path"]
    out = subprocess.run(["git", "-C", str(repo), "log", "--all", "--format=", "--name-only", "--", "output/eulerbounds"],
                         capture_output=True, text=True, check=True).stdout
    names = sorted({n for n in out.split("\n") if n.strip() and not n.endswith("README.md")})
    assert len(names) >= 12
    assert all("y_0.2" in n for n in names), names
    assert not [n for n in names if "16733" in n or "0.186" in n]
    at_n0 = [n for n in names if "630783" in n]
    assert at_n0 == ["output/eulerbounds/lemmasawtooth_bounds_t_0.17_y_0.2_N_630783_15mil_moll_2,3,5.txt"]


@needs_cache
def test_the_banked_window_bound_has_no_producer_in_the_bundle() -> None:
    """REDUCTION.md A4: the members naming lwin2 are exactly the recorded list, and none is C or GP source."""
    want = set(next(r for r in CHAIN["reduction_1875"] if r["id"] == "A4")["lwin2_naming_members"])
    root = CACHE / SRC["ZEN_ZIP"]["members_root"]
    seen = set()
    for d, _, files in os.walk(root):
        for name in files:
            p = Path(d) / name
            if p.stat().st_size > 50_000_000:
                continue
            if b"lwin2" in p.read_bytes():
                seen.add(name)
    assert seen == want
    assert not [n for n in seen if n.endswith((".c", ".gp"))]


# ---------------------------------------------------------------------------
# 2. identities, re-derived
# ---------------------------------------------------------------------------

from contextlib import contextmanager  # noqa: E402

from mpmath import iv, mp  # noqa: E402


@contextmanager
def ivprec(bits: int):
    """mpmath's interval context has no workprec; set and restore by hand."""
    old = iv.prec
    iv.prec = bits
    try:
        yield
    finally:
        iv.prec = old

T_PT = 3000175332800
X2 = 5000000194858
XS = 6000000185827


def _row2() -> tuple[F, F]:
    r = CHAIN["row2"]
    return F(r["t0"]), F(r["y0"])


def test_row2_parameters_match_the_quoted_table_row() -> None:
    row = QUOTES["P9"]["text"]
    assert "194858" in row and "0.186" in row and "0.16733" in row and "630783" in row and "0.0376" in row
    assert CHAIN["row2"]["X"] == str(X2) and CHAIN["row2"]["N0"] == 630783


def test_row2_lambda() -> None:
    t0, y0 = _row2()
    lam = t0 + y0 ** 2 / 2
    assert lam == F(3999993289, 20000000000)
    assert str(float(lam)) == "0.19999966445"
    assert lam <= F(1, 5)


def test_row2_height() -> None:
    half = F(X2, 2)
    assert half == 2500000097429
    assert T_PT - half == 500175235371
    assert half < F(251, 100) * 10 ** 12 <= T_PT  # PT's printed sufficient threshold, 2.51e12


def _N_is_constant(x_lo: int, t_hi: F, n: int) -> bool:
    """floor(sqrt(x/(4 pi) + t/16)) == n on [x_lo, x_lo + 1] x [0, t_hi]; the argument increases in x and t."""
    with ivprec(256):
        lo = iv.mpf(x_lo) / (4 * iv.pi)
        hi = iv.mpf(x_lo + 1) / (4 * iv.pi) + iv.mpf(t_hi.numerator) / iv.mpf(t_hi.denominator) / 16
        return (iv.mpf(n) ** 2).b < lo.a and hi.b < (iv.mpf(n + 1) ** 2).a


def test_row2_N_constant_on_the_barrier_slab() -> None:
    t0, _ = _row2()
    assert _N_is_constant(X2, t0, 630783)
    assert not _N_is_constant(X2, t0, 630782)


def test_site_1875_identities() -> None:
    assert F(1680, 10 ** 4) + F(39, 1000) / 2 == F(3, 16)
    assert F(XS, 2) == F(6000000185827, 2)
    assert T_PT - F(XS, 2) == F(350479773, 2)
    assert F(33, 200) ** 2 == F(1089, 40000)
    assert F(39, 1000) - F(33, 200) ** 2 == F(471, 40000)
    assert _N_is_constant(XS, F(1809, 10000), 690988)


def test_collision_band_walls() -> None:
    a, b = F(4, 25), F(3, 16)
    C, H, J, W = 690988, 2299999, 2300000, 66476100549959
    with ivprec(256):
        def wall(n, t):
            return 4 * iv.pi * (iv.mpf(n) ** 2 - iv.mpf(t.numerator) / iv.mpf(t.denominator) / 16)

        assert wall(C, a).b < XS < wall(C + 1, b).a
        assert wall(H, a).b < W < wall(J, b).a and wall(J, b).b < W + 1  # so W = floor(s_J(b))


def test_the_other_n0_sweep_is_the_019_rung() -> None:
    assert F(17, 100) + F(1, 5) ** 2 / 2 == F(19, 100)


def test_collision_bands() -> None:
    assert F(4, 25) == F("0.16") and F(319, 2000) == F("0.1595")
    assert 0 < F(319, 2000) < F(4, 25) < F(3, 16)


# ---------------------------------------------------------------------------
# the structural Davenport-Heilbronn gate
# ---------------------------------------------------------------------------


def test_dh_zero_is_the_laboratory_pin() -> None:
    from zeta import epstein

    gate = CHAIN["dh_gate"]
    assert gate["zero_re"] == epstein.OFFLINE_ZERO_RE
    assert gate["zero_im"] == epstein.OFFLINE_ZERO_IM
    with mp.workdps(40):
        rho = mp.mpc(mp.mpf(gate["zero_re"]), mp.mpf(gate["zero_im"]))
        assert abs(epstein.dh_f(rho, dps=40)) < mp.mpf("1e-20")
        assert mp.re(rho) - mp.mpf(1) / 2 > mp.mpf("0.3")


def test_dh_fails_the_verification_height_input() -> None:
    gate = CHAIN["dh_gate"]
    sigma, gamma = F(gate["zero_re"]), F(gate["zero_im"])
    t0, y0 = _row2()
    # row 2: Theorem 1.2 (i) excludes zeros with (1 + y0)/2 <= sigma <= 1 and 0 <= T <= X/2
    assert (1 + y0) / 2 < sigma <= 1 and 0 < gamma <= F(X2, 2)
    # the 0.1875 site, y0 = sqrt(39/1000): (1 + y0)/2 < sigma iff y0 < 2 sigma - 1
    assert F(39, 1000) < (2 * sigma - 1) ** 2 and 0 < gamma <= F(XS, 2)
    # wide frame s = 1/2 + i z / 2: z = 2 gamma - i (2 sigma - 1)
    assert F(gate["wide_frame_z_re"]) == 2 * gamma
    assert F(gate["wide_frame_z_im_abs"]) == 2 * sigma - 1
    assert 0 < 2 * gamma <= XS and 2 * sigma - 1 > 0
    assert gate["fails_input"] == "verification height" and gate["passes_gate"] is True
