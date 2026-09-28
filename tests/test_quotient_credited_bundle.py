"""Independent fixed-input arithmetic for the credited N10000 decomposition."""
import json
from pathlib import Path

from mpmath import mp
import pytest
from sympy import factorint

from hunts.quotient_certificate import credited_bundle as credited

HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"


def triangular_fold(a):
    rates = [0] * 100
    for j in range(100, 0, -1):
        parity = a // j - 2 * ((a // 2) // j)
        rates[j - 1] = parity - sum(rates[i - 1] * (i // j) for i in range(j + 1, 101))
    F = {a: -1, a // 2: 2}
    for i, value in enumerate(rates, 1):
        F[i] = F.get(i, 0) + value
    return {q: value for q, value in F.items() if value}


@pytest.fixture(scope="module")
def independent():
    products = {10000 // d: 1 for d in range(2, 10001)}
    for d in range(2, 10001):
        factors = factorint(d)
        if len(factors) == 1:
            products[10000 // d] *= int(next(iter(factors)))
    folds = {a: triangular_fold(a) for a in products if a > 100 and products[a] > 1}
    sources = sorted(a for a, F in folds.items() if sum(F.values()) > 0)
    additions = {163: 57, 232: 7, 270: 5, 434: 74,
                 625: 40, 1250: 22, 2500: 12, 5000: 4}
    U = {q: sum(folds[a].get(q, 0) for a in sources) for q in products}
    H = {q: sum(t * folds[a].get(q, 0) for a, t in additions.items()) for q in products}
    D = {q: 2 * U[q] + H[q] for q in products}
    V = folds[103]
    R = {q: D[q] - V.get(q, 0) for q in products}
    return products, folds, sources, additions, U, H, D, V, R


def test_prescribed_seed_and_all_used_fold_moments_independently(independent):
    products, folds, sources, additions, U, _, D, V, R = independent
    assert len(products) == 198 and sum(M == 1 for M in products.values()) == 99
    assert len(folds) == 35 and len(sources) == 28
    assert sum(U.values()) == 91 and sources[0] == 103
    used = set(sources) | set(additions)
    assert len(used) == 31
    for a in used:
        F = folds[a]
        assert products[a] > 1 and set(F) <= set(products)
        assert F == credited.fold(a, 100)
        assert all(sum(v * (q // j) for q, v in F.items()) == 0 for j in range(1, 101))
    for vector in (D, V, R):
        assert all(sum(v * (q // j) for q, v in vector.items()) == 0 for j in range(1, 101))


def test_net_capacities_and_exact_unique_maximal_scale(independent):
    products, _, _, _, _, _, D, _, _ = independent
    binding, withdrawals = [], 0
    for q, M in products.items():
        if M == 1:
            assert D[q] >= 0
        if D[q] < 0:
            withdrawals += 1
            assert M ** 146 >= 229 ** (-D[q])
            if M ** 146 == 229 ** (-D[q]):
                binding.append(q)
    assert withdrawals == 51 and binding == [43]
    assert (10000 // 44 + 1, 10000 // 43) == (228, 232)
    assert products[43] == 229 and D[43] == -146
    assert sum(D.values()) == 615


def test_existing_lemma_parameters_and_all_component_envelopes(independent):
    products, _, _, _, _, _, D, V, R = independent
    empty = sorted(q for q, M in products.items() if M == 1)
    assert {q: V[q] for q in empty if V.get(q, 0)} == {33: -1, 100: 1}
    assert R[33] == 1 and all(R[q] >= 0 for q in empty)
    assert all(V.get(q, 0) >= 0 for q in empty if q != 33)
    assert (R[54], R[62], R[100]) == (0, 0, 110)
    # Existing lemma: block={33}, p=1,C=0,rho=0,d=t=S=1.
    d = max(-V[33], 0)
    t, S = d, d
    assert d == t == S == 1
    assert all(D[q] == V.get(q, 0) + t * R[q] for q in products)
    checked, binding = 0, []
    for q, M in products.items():
        if M == 1:
            continue
        burden = max(-V.get(q, 0), 0) + S * max(-R[q], 0)
        assert max(-D[q], 0) <= burden
        if burden:
            checked += 1
            assert M ** 146 >= 229 ** burden
            if M ** 146 == 229 ** burden:
                binding.append(q)
    assert checked == 52 and binding == [43]


def test_full_original_seed_spends_credits_the_lemma_cannot_spend(independent):
    products, _, _, _, U, H, D, _, R = independent
    assert sorted(q for q, M in products.items() if M == 1 and H[q] < 0) == [54, 62]
    for q, expected in {33: (-22, 22, 0), 54: (2, -2, 0), 62: (4, -4, 0)}.items():
        assert products[q] == 1
        assert (2 * U[q], H[q], D[q]) == expected
    # Any output of the old lemma with seed2U must have D>=2U on Z.
    # The two violated necessary inequalities identify that decomposition's
    # obstruction; they say nothing against the regrouped repair.
    assert D[54] < 2 * U[54] and D[62] < 2 * U[62]
    assert R[54] == R[62] == 0


def test_positive_repair_gain_and_internal_losses_are_both_retained(independent):
    _, folds, _, additions, U, H, D, V, R = independent
    gains = {a: sum(folds[a].values()) for a in additions}
    assert gains == {163: 1, 232: -5, 270: 1, 434: 5, 625: 1, 1250: 0, 2500: -1, 5000: 2}
    positive = sum(t * max(gains[a], 0) for a, t in additions.items())
    loss = sum(t * max(-gains[a], 0) for a, t in additions.items())
    assert positive == 480 and loss == 47
    assert sum(H.values()) == positive - loss == 433
    assert sum(V.values()) == 3
    assert sum(R.values()) == 2 * sum(U.values()) - 3 + positive - loss == 612
    assert sum(D.values()) == 3 + 612 == 615
    assert 3 < 615  # the boxed ell=0 bound alone discards positive repair gain


def test_saved_output_and_logarithmic_gain_replay(independent):
    products, _, _, _, _, _, D, _, _ = independent
    before = mp.dps
    actual = credited.analyze()
    saved = json.loads((HUNT / "credited_bundle_results.json").read_text())
    normalized = json.loads(json.dumps(actual))
    assert all(saved[key] == value for key, value in normalized.items())
    assert saved["requested_bundles"] == saved["completed_bundles"] == 1
    assert saved["searches"] == saved["optimizations"] == 0
    with mp.workdps(110):
        scale = mp.log(products[43]) / -D[43]
        gain = scale * sum(D.values())
        for value, key in ((scale, "scale_enclosure"), (gain, "gain_enclosure")):
            lo, hi = map(mp.mpf, saved[key])
            assert lo <= value <= hi
        assert mp.mpf("22.888623508122310") < gain < mp.mpf("22.888623508122312")
    assert mp.dps == before
