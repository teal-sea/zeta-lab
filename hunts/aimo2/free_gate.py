"""Free pre-GPU gate: does cheap-syntactic-perturbation decay predict the
robustness label out-of-fold? If not, a self-generated (necessarily noisier)
version cannot, and no GPU session is justified.

cheap set  = {typos, rephrase, rename, distract}   (a small model could self-generate these)
target set = {domain, expert_no_solution, expert_perturbations}  (cannot self-generate)
label      = pair (model,problem) robust iff pooled relative decay over ALL types < 0.5

Binding decision: on the public 8B rows (qwen3-8b:low -> DeepSeek-R1-8B), the
cheap-feature predictor must beat the better constant baseline out-of-fold
(leave-problem-out) by a margin exceeding the 95th percentile of a seeded
label-permutation null. A marginal pass counts as FAIL, because the real method
loses the shared-instance advantage this proxy enjoys.

Run: .venv/bin/python hunts/aimo2/free_gate.py
"""
import json, os, collections, random
HERE = os.path.dirname(__file__)
FULL = json.load(open(os.path.join(HERE, "data", "sample_full.json")))
CHEAP = {"typos", "rephrase", "rename", "distract"}
TARGET = {"domain", "expert_no_solution", "expert_perturbations"}

low = [r for r in FULL if r["model_id"].endswith(":low")]
def pooled_rel(rows):
    if not rows: return None
    b = max(float(r["base_accuracy"]) for r in rows)
    den = sum(int(r["n_permuted_predictions"]) for r in rows)
    num = sum(float(r["permuted_accuracy"]) * int(r["n_permuted_predictions"]) for r in rows)
    if not den or not b: return 0.0
    return (b - num / den) / b

def build(rows):
    byp = collections.defaultdict(list)
    for r in rows: byp[(r["model_id"], r["problem_id"])].append(r)
    data = []
    for k, rs in byp.items():
        allr = pooled_rel(rs)
        cheap = pooled_rel([r for r in rs if r["permutation_type"] in CHEAP])
        if allr is None or cheap is None: continue
        label = allr < 0.5                      # robust
        data.append((k[0], k[1], label, cheap)) # (model, problem, label, cheap_decay_feature)
    return data

def better_constant(train):  # chosen on train labels only
    t = sum(1 for *_, in train for l in [ _[2] ] ) if False else sum(d[2] for d in train)
    return (t > len(train) / 2)  # True if majority robust

def cv_threshold(data, hi):
    """leave-one-out over axis hi; fit a decay threshold and the better constant on train."""
    keys = sorted({d[hi] for d in data}); c_pred = 0; c_const = 0; n = 0
    for h in keys:
        tr = [d for d in data if d[hi] != h]; te = [d for d in data if d[hi] == h]
        # fit threshold on train: robust iff cheap_decay <= thr ; pick thr maximizing train acc
        best = (None, -1)
        for thr in sorted({d[3] for d in tr}) + [1e9]:
            acc = sum(((d[3] <= thr) == d[2]) for d in tr)
            if acc > best[1]: best = (thr, acc)
        thr = best[0]
        const = sum(d[2] for d in tr) > len(tr) / 2
        for d in te:
            c_pred += ((d[3] <= thr) == d[2]); c_const += (const == d[2]); n += 1
    return c_pred, c_const, n

def perm_null(data, hi, iters=2000, seed=0):
    rng = random.Random(seed); labels = [d[2] for d in data]; accs = []
    for _ in range(iters):
        perm = labels[:]; rng.shuffle(perm)
        d2 = [(data[i][0], data[i][1], perm[i], data[i][3]) for i in range(len(data))]
        p, _, n = cv_threshold(d2, hi); accs.append(p / n)
    accs.sort(); return accs[int(0.95 * len(accs))]

print("== FREE GATE: cheap-perturbation decay -> label, out of fold ==\n")
report = {}
for name, rows in [("8B only (qwen3-8b:low) [BINDING]", [r for r in low if r["model_id"] == "qwen3-8b:low"]),
                   ("all 7 models pooled", low)]:
    data = build(rows)
    n_rob = sum(d[2] for d in data)
    print(f"-- {name}: {len(data)} pairs, {n_rob} robust / {len(data)-n_rob} nonrobust")
    for hi, axis in [(1, "leave-problem-out")] + ([(0, "leave-model-out")] if rows is low else []):
        p, cst, n = cv_threshold(data, hi)
        null95 = perm_null(data, hi, iters=2000, seed=0)
        beats = p > cst and (p / n) > null95
        print(f"   {axis}: cheap-feature {p}/{n}={p/n:.3f} | better-constant {cst}/{n}={cst/n:.3f} | perm-null p95={null95:.3f} | beats={beats}")
        report[f"{name}|{axis}"] = {"pred": p, "const": cst, "n": n, "null95": round(null95,3), "beats": bool(beats)}
json.dump(report, open(os.path.join(HERE, "artifacts", "free_gate.json"), "w"), indent=2, sort_keys=True)

binding = report["8B only (qwen3-8b:low) [BINDING]|leave-problem-out"]
verdict = "PASS -> GPU justified" if binding["beats"] else "FAIL -> no GPU, report-only"
print(f"\nBINDING VERDICT (8B, leave-problem-out): {verdict}")
print("wrote artifacts/free_gate.json")
