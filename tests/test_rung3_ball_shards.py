"""Sharded ball-certificate emission stays import-ordered and size-capped."""
from __future__ import annotations

import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "rung3_generate", ROOT / "scripts" / "60_rung3_generate.py")
assert SPEC is not None and SPEC.loader is not None
gen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gen)
PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())

FORBIDDEN = ("sorry", "admit", "mulA", "absUpper", "sqrtUpperQ")
MAX_SHARD_BYTES = 2_000_000


def _site(sid: str):
    site = dict(next(x for x in PLAN["big"]["boxes"] if x["id"] == sid))
    site["M"] = PLAN["M"]
    return site


def _centre_site():
    site = dict(PLAN["centre"])
    site.setdefault("id", "centre")
    site["re_lo"] = site["re_hi"] = PLAN["small"]["cre"]
    site["im_lo"] = site["im_hi"] = PLAN["small"]["cim"]
    site["eps"] = PLAN["small"]["eps"]
    return site


def _imports(text: str) -> list[str]:
    return [line.split()[1] for line in text.splitlines() if line.startswith("import ")]


def _by_rel(files: list[tuple[str, str]]) -> dict[str, str]:
    return dict(files)


def test_one_file_mode_is_unchanged_for_current_sites():
    text, stats = gen.emit_site(_site("B_right_06"), "big", arith="ball")
    assert "import ZetaLean.BallCertSupport" in text
    assert "private lemma hp_B_right_06_84" in text
    assert "theorem upper_B_right_06" in text
    assert "namespace Prime_" in text
    assert stats["prime_towers"] == 23
    joined = text
    for token in FORBIDDEN:
        assert token not in joined


def test_sharded_small_site_splits_primes_and_keeps_the_site_theorem():
    files, stats = gen.emit_site_modules(
        _site("B_right_06"), "big", arith="ball", max_bytes=2_000_000)
    by = _by_rel(files)

    assert files[-1][0] == "CB_right_06.lean"
    assert "CB_right_06/Base.lean" in by
    assert any(rel.startswith("CB_right_06/Primes") for rel, _ in files)
    assert any(rel.startswith("CB_right_06/Composites") for rel, _ in files)
    assert "theorem upper_B_right_06" in by["CB_right_06.lean"]
    assert "theorem enc_B_right_06" in by["CB_right_06.lean"]
    assert "namespace Prime_" not in by["CB_right_06.lean"]
    assert any("namespace Prime_" in text for rel, text in files if "/Primes" in rel)
    assert any("contains_cpow_mulB_coarsen_lit" in text
               for rel, text in files if "/Composites" in rel)
    assert stats["n_files"] >= 4
    assert stats["max_file_bytes"] <= 2_000_000
    assert stats["normBound"] == gen.emit_site(_site("B_right_06"), "big", arith="ball")[1]["normBound"]
    for rel, text in files:
        for token in FORBIDDEN:
            assert token not in text, (rel, token)


def test_sharded_modules_import_in_dependency_order():
    files, _ = gen.emit_site_modules(
        _site("B_right_06"), "big", arith="ball", max_bytes=2_000_000)
    names = {rel.replace("/", ".").removesuffix(".lean"): rel for rel, _ in files}
    imported_by = {rel: _imports(text) for rel, text in files}

    def site_imports(rel: str) -> list[str]:
        return [imp for imp in imported_by[rel] if imp.startswith("CB_right_06")]

    assert imported_by["CB_right_06/Base.lean"] == ["ZetaLean.BallCertSupport"]
    for rel, text in files:
        if rel.endswith("/Primes.lean") and "import CB_right_06.Primes0" in text:
            continue
        if "/Primes" in rel and rel.endswith(".lean") and rel != "CB_right_06/Primes.lean":
            assert site_imports(rel) == ["CB_right_06.Base"]
    composite_numbered = [
        rel for rel, _ in files
        if re.fullmatch(r"CB_right_06/Composites\d+\.lean", rel)]
    if composite_numbered:
        first = sorted(composite_numbered)[0]
        assert "CB_right_06.Primes" in imported_by[first]
        for prev, cur in zip(sorted(composite_numbered), sorted(composite_numbered)[1:]):
            prev_mod = prev.replace("/", ".").removesuffix(".lean")
            assert prev_mod in imported_by[cur]
    assert "theorem upper_B_right_06" in dict(files)["CB_right_06.lean"]
    root_imps = imported_by["CB_right_06.lean"]
    assert root_imps, names
    assert all(imp in names or imp.startswith("CB_right_06.") for imp in root_imps)


def _walk_strings(obj):
    if isinstance(obj, str):
        yield obj
    elif isinstance(obj, dict):
        for value in obj.values():
            yield from _walk_strings(value)
    elif isinstance(obj, list):
        for value in obj:
            yield from _walk_strings(value)


def test_sharded_emission_builds_a_relative_compile_manifest():
    files, stats = gen.emit_site_modules(
        _site("B_right_06"), "big", arith="ball", max_bytes=2_000_000)
    man = stats["manifest"]
    assert man["source_format_version"] == 2
    assert man["root"] == "CB_right_06"
    assert man["id"] == "B_right_06"
    assert man["kind"] == "big"
    assert man["K"] == 17
    assert man["modules"][-1]["path"] == "CB_right_06.lean"
    assert [m["path"] for m in man["modules"]] == [rel for rel, _ in files]
    assert [m["bytes"] for m in man["modules"]] == stats["file_bytes"]
    assert man["n_files"] == stats["n_files"]
    assert man["max_file_bytes"] == stats["max_file_bytes"]
    assert man["prime_towers"] == 23
    assert man["normBound"] == str(stats["normBound"])
    assert man["normLower"] == str(stats["normLower"])
    earlier = []
    for mod in man["modules"]:
        assert "depends" in mod
        for dep in mod["depends"]:
            assert dep in earlier
            assert not Path(dep).is_absolute()
        earlier.append(mod["path"])
    for text in _walk_strings(man):
        assert not text.startswith("/")
        assert not text.startswith("\\")


def test_cli_shard_flag_writes_nested_modules(tmp_path):
    out = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "60_rung3_generate.py"),
         str(ROOT / "lean" / "cert" / "rung3_plan2.json"), str(tmp_path),
         "--only", "B_right_06", "--arith", "ball", "--shard",
         "--max-bytes", "2000000"],
        check=True, capture_output=True, text=True)
    root = tmp_path / "CB_right_06.lean"
    base = tmp_path / "CB_right_06" / "Base.lean"
    manifest_path = tmp_path / "CB_right_06.manifest.json"
    assert root.is_file()
    assert base.is_file()
    assert manifest_path.is_file()
    assert "theorem upper_B_right_06" in root.read_text()
    assert "n_files=" in out.stdout
    assert "CB_right_06.manifest.json modules=" in out.stdout
    sizes = [p.stat().st_size for p in tmp_path.rglob("*.lean")]
    assert sizes and max(sizes) <= 2_000_000
    man = json.loads(manifest_path.read_text())
    assert man["source_format_version"] == 2
    assert man["root"] == "CB_right_06"
    assert man["kind"] == "big"
    assert man["K"] == 17
    written = {str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*.lean")}
    assert [m["path"] for m in man["modules"]][-1] == "CB_right_06.lean"
    earlier = []
    for mod in man["modules"]:
        assert mod["path"] in written
        assert (tmp_path / mod["path"]).stat().st_size == mod["bytes"]
        assert not Path(mod["path"]).is_absolute()
        for dep in mod["depends"]:
            assert dep in earlier
        earlier.append(mod["path"])
    for text in _walk_strings(man):
        assert not text.startswith("/")
        assert str(tmp_path) not in text


def test_default_shard_cap_is_two_million_bytes():
    assert gen._ball_backend().MAX_SHARD_BYTES == 2_000_000
    files, stats = gen.emit_site_modules(
        _site("B_right_06"), "big", arith="ball")
    assert stats["max_bytes"] == 2_000_000
    assert stats["max_file_bytes"] <= 2_000_000
    assert stats["manifest"]["source_format_version"] == 2


def test_sharded_centre_stays_under_default_cap(tmp_path):
    files, stats = gen.emit_site_modules(_centre_site(), "centre", arith="ball")
    by = _by_rel(files)
    assert files[-1][0] == "Ccentre.lean"
    assert "theorem centre_lt_centre" in by["Ccentre.lean"]
    assert "theorem enc_centre" in by["Ccentre.lean"]
    assert stats["max_bytes"] == MAX_SHARD_BYTES
    assert stats["max_file_bytes"] <= MAX_SHARD_BYTES
    assert stats["n_files"] >= 4
    for rel, text in files:
        assert len(text.encode("utf-8")) <= MAX_SHARD_BYTES
        for token in FORBIDDEN:
            assert token not in text, (rel, token)
        dest = tmp_path / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    written = list(tmp_path.rglob("*.lean"))
    assert (tmp_path / "Ccentre.lean") in written
    assert max(p.stat().st_size for p in written) <= MAX_SHARD_BYTES
    assert any(p.name.startswith("Primes") for p in written)
    assert any(p.name.startswith("Composites") for p in written)
