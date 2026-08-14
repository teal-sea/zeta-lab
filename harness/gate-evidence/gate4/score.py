import json, sys
sys.path.insert(0, "/home/user/zeta-lab")
from compiler import semantics

def witness_ok(item, x, y):
    """Verify the claimed counterexample: source defined, target poison/UB there."""
    try:
        s = semantics.model_output_table(item["source_ir"])
        t = semantics.model_output_table(item["target_ir"])
    except Exception:
        return False
    if not (-128 <= x <= 127 and -128 <= y <= 127):
        return False
    i = (x + 128) * 256 + (y + 128)
    if s[i] is semantics.UB or s[i] is semantics.POISON:
        return False
    return t[i] is semantics.POISON or t[i] is semantics.UB

key = json.load(open("key.json"))
items = {i["id"]: i for i in json.load(open("items.json"))}
runs = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
by = {}
for r in runs:
    v, iid = r.get("verdict"), r["item"]
    if v == "INVALID":
        ok = witness_ok(items[iid], r.get("x"), r.get("y"))
        correct = ok and key[iid] == "INVALID"
        note = "" if ok else "witness does not verify"
        if ok and key[iid] == "VALID":
            note = "KEY REFUTED"
    elif v == "VALID":
        correct, note = key[iid] == "VALID", ""
    else:
        correct, note = False, "unparseable"
    by.setdefault(iid, {})[r["arm"]] = correct
    print(f"{iid} {r['arm']}  key={key[iid]:<8} said={str(v):<8} {'ok' if correct else 'MISS':<5} {note}")

b = sum(1 for i in by if by[i].get("B") and not by[i].get("A"))
c = sum(1 for i in by if by[i].get("A") and not by[i].get("B"))
n = len(by)
print(f"\npaired {n}   ArmA {sum(1 for i in by if by[i].get('A'))}/{n}   ArmB {sum(1 for i in by if by[i].get('B'))}/{n}")
print(f"b={b} c={c} b-c={b-c}")
print(f"CRITERION b-c >= 2  ->  {'PASS' if b-c >= 2 else 'FAIL'}")
