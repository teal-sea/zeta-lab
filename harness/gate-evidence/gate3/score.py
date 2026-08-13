"""Mechanical scorer for gate v3. Witnesses are VERIFIED, not taken on trust.

An agent answering NOT ESTABLISHED must exhibit a witness: a single textual edit
to the frozen source producing a variant that

  (i)  reproduces the bundle's recorded behaviour exactly, and
  (ii) differs from the frozen original on at least one in-scope expression.

Both are checked here by execution. A NOT ESTABLISHED verdict without a valid
witness is scored INCORRECT even when the key agrees -- otherwise an arm could
win by always answering NOT ESTABLISHED, which is the exact failure mode the
balance is there to catch.

An ESTABLISHED verdict needs no witness. But if an agent supplies a VALID
witness on an item keyed ESTABLISHED, the key is wrong: that item is VOID for
both arms and reported. The key is never silently amended.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from mutants import SRC, fires, load  # noqa: E402

VERDICTS = ("ESTABLISHED", "NOT ESTABLISHED")


def check_witness(old: str, new: str, bundle: list[str], fam: dict) -> tuple[bool, str]:
    src = SRC.read_text()
    if not old or old == new:
        return False, "empty or no-op edit"
    if src.count(old) != 1:
        return False, f"`old` occurs {src.count(old)}x in the source, not exactly once"
    try:
        mod = load("witness", src.replace(old, new))
    except Exception as exc:
        return False, f"variant does not import: {type(exc).__name__}: {exc}"
    for expr in bundle:
        got = fires(mod, expr)
        want = fam["base"][expr]
        if isinstance(want, list):
            want = tuple(want)
        if got != want:
            return False, f"variant fails the bundle at {expr!r}"
    for expr in fam["scope"]:
        want = fam["base"][expr]
        if isinstance(want, list):
            want = tuple(want)
        if fires(mod, expr) != want:
            return True, f"valid: passes the bundle, differs in scope at {expr!r}"
    return False, "variant is behaviourally identical across the whole scope"


def main() -> int:
    fam = json.loads((HERE / "family.json").read_text())
    key = json.loads((HERE / "key.json").read_text())
    items = {i["id"]: i for i in json.loads((HERE / "items.json").read_text())}
    runs = [json.loads(l) for l in (HERE / sys.argv[1]).read_text().splitlines() if l.strip()]

    out = []
    for r in runs:
        iid, verdict = r["item"], r.get("verdict")
        note = ""
        if verdict not in VERDICTS:
            correct, note = False, "unparseable verdict"
        elif verdict == "NOT ESTABLISHED":
            ok, note = check_witness(r.get("witness_old", ""), r.get("witness_new", ""),
                                     items[iid]["bundle"], fam)
            correct = ok and key[iid] == "NOT ESTABLISHED"
            if ok and key[iid] == "ESTABLISHED":
                note = "KEY REFUTED — " + note
        else:
            correct, note = key[iid] == "ESTABLISHED", ""
        out.append({**r, "truth": key[iid], "correct": correct, "note": note})
        print(f"{iid}  {r['arm']}  key={key[iid]:<16} said={str(verdict):<16} "
              f"{'ok' if correct else 'MISS':<5} {note}")

    (HERE / (Path(sys.argv[1]).stem + "_scored.jsonl")).write_text(
        "\n".join(json.dumps(o) for o in out) + "\n")
    for arm in sorted({o["arm"] for o in out}):
        a = [o for o in out if o["arm"] == arm]
        print(f"\narm {arm}: {sum(o['correct'] for o in a)}/{len(a)} correct")
    refuted = [o["item"] for o in out if "KEY REFUTED" in o["note"]]
    if refuted:
        print(f"\nKEY REFUTED on {sorted(set(refuted))} — those items VOID for both arms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
