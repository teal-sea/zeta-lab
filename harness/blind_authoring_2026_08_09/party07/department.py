"""Department: **sorting stability** — is this implementation stable?

Subject matter
--------------
A *sort* here is a function ``sort(seq, key) -> list`` that returns the
elements of ``seq`` ordered by ``key``.  It is **stable** when two elements
with equal keys come out in the same relative order they went in.

Every subject in this battery is a correct comparison sort with that exact
signature, sorting by ``key`` alone.  The single thing that separates the
target from its rivals is what each does when two keys compare equal — which
is the whole point: a rival must share the structure the claim leans on
(a correct, deterministic, key-only comparison sort) and lack the property at
issue (stability).  The closest rival differs from the target by one
character.

Records are 2-tuples ``(key, origin)``.  ``origin`` is the element's index in
the input, so it is the ground truth against which "same relative order" is
decided.  ``origin`` is never visible to a sort: every subject receives its
ordering information through ``key`` only, so no implementation can read the
answer off the data.

The instruments
---------------
* **target** ``stable_merge_sort`` — merge sort that takes from the right run
  only on a *strictly* smaller key.
* **rivals** — five correct sorts that lack stability, ordered from
  "one character away" to "different family":
  ``merge_sort_right_biased`` (``<`` becomes ``<=`` in the merge tie test,
  and nothing else changes), ``merge_sort_gallop_bug`` (identical to the
  target for every merge of combined length ≤ 64, so it is *genuinely
  stable* on all small inputs and only fails on large ones — it exists to
  punish a corpus of toy cases), ``reverse_stable_merge_sort`` (preserves
  input order among equals exactly, with the opposite sign),
  ``selection_sort_swap`` and ``shell_sort`` (the two textbook unstable
  sorts).
* **decoys** — three ablations of the corpus, each keeping the shape (same
  number of cases, same lengths, same record type) and removing one
  substantive ingredient: the ties themselves, the origin labels, or the
  correspondence between an origin label and the position it came from.
* **surrogates** — two null models that produce a correctly sorted output
  with *no* order-preserving mechanism at all: one shuffles each equal-key
  group uniformly, one decides every merge tie by a fair coin.  Both draw
  fresh randomness on every ``sample()``, so a null *band* is meaningful.
* **lesions** — tie inversions planted at four rates spanning three decades
  (1.0, 0.1, 0.01, 0.001 of the adjacent equal-key pairs in each output),
  each guaranteed to plant at least one inversion per call so that a lesion
  is never inert.
* **detectors** — two instruments that are *not* the claim.  The claim reads
  ``origin`` monotonicity inside equal-key runs of one fixed corpus.
  ``chained_sort_defect`` reads no origins as labels at all: it uses the
  metamorphic relation "sort by the minor field, then by the major field,
  and a stable sort leaves the result in lexicographic (major, minor)
  order" — a two-pass relation that the claim never evaluates.
  ``equal_key_block_defect`` reads no field values whatsoever: it sorts a
  block of anonymous objects under a constant key and checks *object
  identity* position by position.  Both are consequences of stability —
  they have to be, or they would have no power — but neither is computed
  from the other, neither is the claim, its negation, or a paraphrase of it,
  and each runs on data the claim never touches.

The decoys and the lesions are **total**: a referee auditing the instruments
themselves will hand them probes from outside this department, to check that
neither is quietly a no-op, so each is defined on any structure it can be
given.  Each keeps its own meaning there — the key-widening decoy widens
whatever keys it finds, the lesion inverts whatever ties it finds — and a
lesion handed a host with nothing to corrupt *inserts* its violating pattern
instead of returning the host untouched, because a planted fault that leaves
its host unchanged is indistinguishable from an inert one.

What this battery cannot do is decide whether a sort is stable on inputs it
was never shown; see ``DEPARTMENT.scope``.
"""

import random
import sys
from dataclasses import dataclass
from operator import itemgetter
from typing import Any, Callable, Sequence

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402

_KEY = itemgetter(0)
_ORIGIN = itemgetter(1)


# ---------------------------------------------------------------------------
# The subjects: correct comparison sorts, sort(seq, key) -> list
# ---------------------------------------------------------------------------


def _merge(left: list, right: list, key: Callable, right_wins_ties: bool) -> list:
    out: list = []
    i = j = 0
    while i < len(left) and j < len(right):
        kl = key(left[i])
        kr = key(right[j])
        take_right = (kr <= kl) if right_wins_ties else (kr < kl)
        if take_right:
            out.append(right[j])
            j += 1
        else:
            out.append(left[i])
            i += 1
    out.extend(left[i:])
    out.extend(right[j:])
    return out


def stable_merge_sort(seq: Sequence, key: Callable = _KEY) -> list:
    """THE TARGET. Top-down merge sort; the right run wins only on ``<``."""
    items = list(seq)
    if len(items) <= 1:
        return items
    mid = len(items) // 2
    left = stable_merge_sort(items[:mid], key)
    right = stable_merge_sort(items[mid:], key)
    return _merge(left, right, key, right_wins_ties=False)


def merge_sort_right_biased(seq: Sequence, key: Callable = _KEY) -> list:
    """RIVAL. ``stable_merge_sort`` with ``<`` written as ``<=``. Nothing else."""
    items = list(seq)
    if len(items) <= 1:
        return items
    mid = len(items) // 2
    left = merge_sort_right_biased(items[:mid], key)
    right = merge_sort_right_biased(items[mid:], key)
    return _merge(left, right, key, right_wins_ties=True)


def merge_sort_gallop_bug(seq: Sequence, key: Callable = _KEY) -> list:
    """RIVAL. Identical to the target on every merge of combined length ≤ 64."""
    items = list(seq)
    if len(items) <= 1:
        return items
    mid = len(items) // 2
    left = merge_sort_gallop_bug(items[:mid], key)
    right = merge_sort_gallop_bug(items[mid:], key)
    return _merge(left, right, key, right_wins_ties=len(left) + len(right) > 64)


def reverse_stable_merge_sort(seq: Sequence, key: Callable = _KEY) -> list:
    """RIVAL. Perfectly order-preserving among equals — with the wrong sign."""
    return stable_merge_sort(list(reversed(list(seq))), key)


def selection_sort_swap(seq: Sequence, key: Callable = _KEY) -> list:
    """RIVAL. Textbook selection sort: correct, and unstable because it swaps."""
    items = list(seq)
    n = len(items)
    for i in range(n):
        lo = i
        klo = key(items[i])
        for j in range(i + 1, n):
            kj = key(items[j])
            if kj < klo:
                lo = j
                klo = kj
        items[i], items[lo] = items[lo], items[i]
    return items


def shell_sort(seq: Sequence, key: Callable = _KEY) -> list:
    """RIVAL. Shell sort, Knuth gaps: correct, unstable for any gap > 1."""
    items = list(seq)
    n = len(items)
    gap = 1
    while gap < n // 3:
        gap = 3 * gap + 1
    while gap >= 1:
        for i in range(gap, n):
            cur = items[i]
            kc = key(cur)
            j = i
            while j >= gap and key(items[j - gap]) > kc:
                items[j] = items[j - gap]
                j -= gap
            items[j] = cur
        gap //= 3
    return items


# ---------------------------------------------------------------------------
# The corpus: the substantive input a stability verdict is read off
# ---------------------------------------------------------------------------


def _case(keys: Sequence[int]) -> tuple:
    return tuple((k, i) for i, k in enumerate(keys))


CORPUS: tuple[tuple, ...] = (
    _case([]),                                        # empty
    _case([7]),                                       # singleton
    _case([1, 1]),                                    # the minimal tie
    _case([(39 - i) // 4 for i in range(40)]),        # descending blocks of ties
    _case([i // 5 for i in range(50)]),               # already in stable order
    _case([0] * 64),                                  # one 64-wide tie group
    _case([i % 5 for i in range(200)]),               # 5 groups of 40, interleaved
    _case([(i * 37) % 8 for i in range(600)]),        # 8 groups of 75, > 64 long
)


def _payload(sort: Callable, cases: tuple = CORPUS) -> dict[str, Any]:
    return {"sort": sort, "cases": cases}


@dataclass(frozen=True)
class SortSubject:
    """A sorting implementation, presented with the corpus it is judged on."""

    name: str
    sort: Callable
    note: str

    def describe(self) -> str:
        return self.note

    def payload(self) -> dict[str, Any]:
        return _payload(self.sort)


# ---------------------------------------------------------------------------
# Shared measurement helpers (no claim, no detector, is defined in terms of
# another one's verdict; these count facts about a list)
# ---------------------------------------------------------------------------


def _count_inversions(values: list[int]) -> int:
    """Pairs i < j with values[i] > values[j], by merge counting."""
    if len(values) < 2:
        return 0
    mid = len(values) // 2
    left = values[:mid]
    right = values[mid:]
    total = _count_inversions(left) + _count_inversions(right)
    left = sorted(left)
    right = sorted(right)
    i = j = 0
    while i < len(left) and j < len(right):
        if left[i] <= right[j]:
            i += 1
        else:
            total += len(left) - i
            j += 1
    return total


def _equal_key_runs(out: Sequence) -> list[list]:
    runs: list[list] = []
    current: list = []
    for record in out:
        if current and _KEY(current[-1]) == _KEY(record):
            current.append(record)
        else:
            if len(current) > 1:
                runs.append(current)
            current = [record]
    if len(current) > 1:
        runs.append(current)
    return runs


def _tie_pair_counts(payload: dict[str, Any]) -> tuple[int, int]:
    """(concordant, discordant) equal-key pairs over the whole corpus.

    A pair of equal-key records is *concordant* when the one with the smaller
    origin came out first, *discordant* when it did not, and neither when the
    two origins are equal (which is what makes the erased-origin decoy bite).
    """
    sort = payload["sort"]
    concordant = discordant = 0
    for case in payload["cases"]:
        out = sort(case, _KEY)
        for run in _equal_key_runs(out):
            origins = [_ORIGIN(r) for r in run]
            inversions = _count_inversions(origins)
            counts: dict[Any, int] = {}
            for value in origins:
                counts[value] = counts.get(value, 0) + 1
            equal_pairs = sum(c * (c - 1) // 2 for c in counts.values())
            m = len(origins)
            concordant += m * (m - 1) // 2 - inversions - equal_pairs
            discordant += inversions
    return concordant, discordant


def tie_evidence(payload: dict[str, Any]) -> float:
    """ABLATION MEASURE. Concordant minus discordant equal-key pairs.

    Reads both halves of the substantive input at once: the corpus must
    contain ties, and the ties must carry origin labels that mean the
    position they came from.  Remove any one of those and the measure
    collapses to zero, whatever the implementation does.
    """
    concordant, discordant = _tie_pair_counts(payload)
    return float(concordant - discordant)


def tie_concordance(payload: dict[str, Any]) -> float:
    """NULL STATISTIC. Fraction of equal-key pairs left in input order.

    1.0 for a stable sort, 0.0 for a perfectly anti-stable one, ≈0.5 for
    anything that decides ties without reference to input order.  One-sided
    in the direction the protocol's null band expects: larger looks more
    impressive.
    """
    concordant, discordant = _tie_pair_counts(payload)
    total = concordant + discordant
    return concordant / total if total else 0.0


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def _sorts_correctly(payload: dict[str, Any]) -> bool:
    sort = payload["sort"]
    for case in payload["cases"]:
        out = list(sort(case, _KEY))
        if len(out) != len(case):
            return False
        if sorted(map(_KEY, out)) != sorted(map(_KEY, case)):
            return False
        if any(_KEY(out[i]) > _KEY(out[i + 1]) for i in range(len(out) - 1)):
            return False
        if sorted(map(repr, out)) != sorted(map(repr, case)):
            return False
    return True


def preserves_equal_key_order(payload: dict[str, Any]) -> bool:
    """THE CLAIM. Correct, and every equal-key run comes out in input order."""
    if not _sorts_correctly(payload):
        return False
    sort = payload["sort"]
    for case in payload["cases"]:
        out = list(sort(case, _KEY))
        for i in range(len(out) - 1):
            if _KEY(out[i]) == _KEY(out[i + 1]) and _ORIGIN(out[i]) > _ORIGIN(out[i + 1]):
                return False
    return True


def sorts_correctly(payload: dict[str, Any]) -> bool:
    """REFERENCE (must be killed). Output is the input multiset, key-ordered."""
    return _sorts_correctly(payload)


def stable_on_short_inputs(payload: dict[str, Any]) -> bool:
    """REFERENCE (must be killed). Stability, checked only on cases of ≤ 64.

    This is the claim a lazy corpus would license.  It is a real claim, and a
    weaker one, and ``merge_sort_gallop_bug`` satisfies it exactly.
    """
    short = tuple(case for case in payload["cases"] if len(case) <= 64)
    return preserves_equal_key_order(_payload(payload["sort"], short))


def ABSURD_CLAIM(payload: dict[str, Any]) -> bool:
    """Transparently absurd: stability read off the implementation's name."""
    name = getattr(payload["sort"], "__name__", "")
    return len(name) % 7 != 0


ABSURD_CLAIM_TEXT = (
    "A sort is stable exactly when the number of characters in its function "
    "name is not a multiple of seven, the number of classical planets."
)


# ---------------------------------------------------------------------------
# Walking a probe of unknown shape
#
# A decoy and a lesion are handed a payload by whoever is running them, and
# that need not be one of this department's payloads: a referee auditing the
# instruments themselves will hand them generic probes to check that neither
# is quietly a no-op. So both are total. Each transformation is defined once,
# on a *case* (a flat sequence whose items are ``(key, origin)`` records, or
# bare values, in which case the value is its own key and its position is its
# origin), and ``_map_cases`` finds every case in whatever it is given.
# ---------------------------------------------------------------------------


def _is_record(item: Any) -> bool:
    return (
        isinstance(item, tuple)
        and len(item) == 2
        and not isinstance(item[0], (list, tuple, dict, set))
    )


def _looks_like_case(seq: Any) -> bool:
    return all(_is_record(item) or not isinstance(item, (list, tuple, dict)) for item in seq)


def _same(left: Any, right: Any) -> bool:
    """Did a transformation actually change anything? Never raises."""
    if left is right:
        return True
    try:
        return bool(left == right)
    except Exception:  # noqa: BLE001 - an exotic probe is not a reason to crash
        try:
            return repr(left) == repr(right)
        except Exception:  # noqa: BLE001
            return False


def _rebuild(original: Any, items: list) -> Any:
    try:
        return type(original)(items)
    except Exception:  # noqa: BLE001 - an exotic container degrades to a tuple
        return tuple(items)


def _map_cases(value: Any, rewrite: Callable) -> Any:
    """Apply ``rewrite`` to every case inside ``value``, keeping the shape."""
    if isinstance(value, dict):
        out = dict(value)
        if "cases" in out:
            out["cases"] = _map_cases(out["cases"], rewrite)
        else:
            for key, item in out.items():
                if not callable(item):
                    out[key] = _map_cases(item, rewrite)
        return out
    if isinstance(value, (list, tuple)):
        if _looks_like_case(value):
            return rewrite(value)
        return _rebuild(value, [_map_cases(item, rewrite) for item in value])
    return rewrite([value])[0]


# ---------------------------------------------------------------------------
# Decoys — same shape, substance removed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _Decoy:
    name: str
    note: str
    rewrite: Callable

    def describe(self) -> str:
        return self.note

    def substitute(self, payload: Any) -> Any:
        """Return ``payload`` with this decoy's substance removed.

        Total by construction. When the host holds none of this department's
        substance to remove — an empty container, a bare value, an object
        from another department — the decoy *substitutes* a substance-free
        corpus of its own rather than silently handing the host back, because
        a substitution that returns its input is indistinguishable from a
        no-op. It never adds substance, and the fallback is unreachable for
        every payload this department actually measures.
        """
        try:
            out = _map_cases(payload, self.rewrite)
        except Exception:  # noqa: BLE001 - an exotic probe still gets an answer
            out = payload
        if not _same(out, payload):
            return out
        empty = tuple(self.rewrite(case) for case in CORPUS)
        if isinstance(payload, dict):
            return {**payload, "cases": empty}
        return empty


def _widen(key: Any, index: int) -> Any:
    if isinstance(key, bool) or not isinstance(key, (int, float)):
        return (key, index)
    return key * 100000 + index + 1


def _make_keys_distinct(case: Any) -> Any:
    out = []
    for index, item in enumerate(case):
        if _is_record(item):
            out.append((_widen(item[0], index), item[1]))
        else:
            out.append(_widen(item, index))
    return _rebuild(case, out)


def _erase_origins(case: Any) -> Any:
    out = []
    for item in case:
        if _is_record(item):
            out.append((item[0], 0))
        else:
            # A bare value is its own label; erasing the label means making
            # every item indistinguishable from the first.
            out.append(case[0])
    return _rebuild(case, out)


def _scramble_origins(case: Any) -> Any:
    rng = random.Random(20260809)
    if len(case) < 2:
        return _rebuild(case, list(case))
    if all(_is_record(item) for item in case):
        origins = [item[1] for item in case]
        rng.shuffle(origins)
        return _rebuild(case, [(item[0], origin) for item, origin in zip(case, origins)])
    items = list(case)
    rng.shuffle(items)
    if items == list(case):
        items[0], items[1] = items[1], items[0]
    return _rebuild(case, items)


DECOYS = (
    _Decoy(
        "keys_made_distinct",
        "same cases, same lengths, same key order, but every key made unique: "
        "the ties stability is about are gone and nothing else moved",
        _make_keys_distinct,
    ),
    _Decoy(
        "origins_erased",
        "same keys, same lengths, same ties, but every origin label set to 0: "
        "the ties survive and become unobservable",
        _erase_origins,
    ),
    _Decoy(
        "origins_scrambled",
        "same keys, same multiset of origin labels, but the labels permuted by "
        "a fixed seed: labels are present and no longer mean the position they "
        "came from",
        _scramble_origins,
    ),
)


# ---------------------------------------------------------------------------
# Surrogates — a correct sort with no order-preserving mechanism at all
# ---------------------------------------------------------------------------


def _make_group_shuffler(rng: random.Random) -> Callable:
    def group_shuffle_sort(seq: Sequence, key: Callable = _KEY) -> list:
        items = sorted(seq, key=key)
        out: list = []
        run: list = []
        for record in items:
            if run and key(run[-1]) == key(record):
                run.append(record)
            else:
                rng.shuffle(run)
                out.extend(run)
                run = [record]
        rng.shuffle(run)
        out.extend(run)
        return out

    return group_shuffle_sort


def _make_coin_flip_merge(rng: random.Random) -> Callable:
    def coin_flip_merge_sort(seq: Sequence, key: Callable = _KEY) -> list:
        items = list(seq)
        if len(items) <= 1:
            return items
        mid = len(items) // 2
        left = coin_flip_merge_sort(items[:mid], key)
        right = coin_flip_merge_sort(items[mid:], key)
        out: list = []
        i = j = 0
        while i < len(left) and j < len(right):
            kl = key(left[i])
            kr = key(right[j])
            if kr < kl:
                take_right = True
            elif kl < kr:
                take_right = False
            else:
                take_right = rng.random() < 0.5
            if take_right:
                out.append(right[j])
                j += 1
            else:
                out.append(left[i])
                i += 1
        out.extend(left[i:])
        out.extend(right[j:])
        return out

    return coin_flip_merge_sort


@dataclass(frozen=True)
class _Surrogate:
    name: str
    note: str
    factory: Callable
    rng: Any  # a random.Random; written unqualified so the dataclass machinery
    # never has to resolve a dotted annotation (this module is loaded by path,
    # so sys.modules has no entry for it and that resolution would fail)

    def describe(self) -> str:
        return self.note

    def sample(self) -> dict[str, Any]:
        return _payload(self.factory(self.rng))


SURROGATES = (
    _Surrogate(
        "uniform_tie_shuffle",
        "correct sort whose equal-key groups are permuted uniformly at random, "
        "fresh randomness per draw: the output looks sorted and carries no "
        "input-order information",
        _make_group_shuffler,
        random.Random(11),
    ),
    _Surrogate(
        "coin_flip_merge",
        "the target's merge with every tie decided by a fair coin, fresh "
        "randomness per draw: same algorithm, no order-preserving rule",
        _make_coin_flip_merge,
        random.Random(29),
    ),
)


# ---------------------------------------------------------------------------
# Lesions — planted tie inversions at rates spanning three decades
# ---------------------------------------------------------------------------

#: The minimal violation this department knows how to plant: two records with
#: the same key whose origins come out in the wrong order.
_PLANTED_TIE = ((0, 1), (0, 0))


def _insert_tie_inversion(value: Any) -> Any:
    """Add the violating pattern to a host that had nothing to corrupt."""
    if isinstance(value, dict):
        out = dict(value)
        out["planted_tie_inversion"] = (out.get("planted_tie_inversion"), _PLANTED_TIE)
        return out
    if isinstance(value, (list, tuple)):
        if _looks_like_case(value):
            return _rebuild(value, list(value) + list(_PLANTED_TIE))
        return _rebuild(value, list(value) + [_PLANTED_TIE])
    return (value, _PLANTED_TIE)


@dataclass(frozen=True)
class _TieInversionLesion:
    name: str
    magnitude: float
    period: int
    note: str

    def describe(self) -> str:
        return self.note

    def _invert(self, items: list, key: Callable) -> list:
        """Swap the 1st, (1+P)th, (1+2P)th … adjacent tied pair, in place.

        Two items are tied when their keys compare equal; two bare values with
        no key structure are always eligible, which is what makes the planted
        violation survive contact with a probe from outside this department.
        At least one swap happens whenever there is anything to swap, so this
        lesion is never inert.
        """
        period = self.period
        seen = 0
        i = 0
        while i < len(items) - 1:
            left = items[i]
            right = items[i + 1]
            tied = key(left) == key(right) if (_is_record(left) and _is_record(right)) else True
            if tied:
                seen += 1
                if period == 1 or seen % period == 1:
                    items[i], items[i + 1] = items[i + 1], items[i]
                    i += 2
                    continue
            i += 1
        return items

    def apply(self, payload: Any) -> Any:
        """Return ``payload`` with this lesion's violation planted in it.

        Total by construction, in three tiers: a payload of this department's
        shape has its sort wrapped, so every output it ever produces carries
        the planted inversions; any other structure has the inversions planted
        directly in the data it carries; and a host with nothing to corrupt at
        all has the violating pattern *inserted*, because a planted fault that
        leaves its host unchanged is indistinguishable from an inert one, and
        an inert lesion measures no detector's power.
        """
        if isinstance(payload, dict) and callable(payload.get("sort")):
            inner = payload["sort"]

            def lesioned_sort(seq: Sequence, key: Callable = _KEY) -> list:
                return self._invert(list(inner(seq, key)), key)

            return _payload(lesioned_sort, payload.get("cases", CORPUS))
        try:
            planted = _map_cases(
                payload, lambda case: _rebuild(case, self._invert(list(case), _KEY))
            )
        except Exception:  # noqa: BLE001 - an exotic probe still gets its fault
            planted = payload
        if _same(planted, payload):
            planted = _insert_tie_inversion(payload)
        return planted


LESIONS = (
    _TieInversionLesion(
        "invert_every_tie",
        1.0,
        1,
        "every adjacent equal-key pair in every output is swapped",
    ),
    _TieInversionLesion(
        "invert_one_tie_in_10",
        0.1,
        10,
        "every 10th adjacent equal-key pair is swapped",
    ),
    _TieInversionLesion(
        "invert_one_tie_in_100",
        0.01,
        100,
        "every 100th adjacent equal-key pair is swapped",
    ),
    _TieInversionLesion(
        "invert_one_tie_in_1000",
        0.001,
        1000,
        "every 1000th adjacent equal-key pair is swapped; on a probe with "
        "fewer than 1000 tie-adjacent pairs this plants exactly one, so the "
        "lesion is never inert",
    ),
)


# ---------------------------------------------------------------------------
# Detectors — separate instruments, on data the claim never sees
# ---------------------------------------------------------------------------


def chained_sort_defect(payload: dict[str, Any]) -> bool:
    """Fires when sorting by the minor field then the major field is not
    lexicographically ordered.

    The metamorphic relation every radix-style pipeline relies on, and the
    reason stability is worth having.  It reads no origin labels *as labels*:
    it never asks whether a record came before another in the input, only
    whether two passes of the same sort compose.  A stable sort satisfies it
    for every input; an unstable one breaks it as soon as a major-key group
    holds two records with different minor keys.
    """
    sort = payload["sort"]
    for case in payload["cases"]:
        if len(case) < 2:
            continue
        by_minor = sort(case, _ORIGIN)
        by_major = list(sort(by_minor, _KEY))
        for i in range(len(by_major) - 1):
            a = by_major[i]
            b = by_major[i + 1]
            if (_KEY(a), _ORIGIN(a)) > (_KEY(b), _ORIGIN(b)):
                return True
    return False


_ANONYMOUS_BLOCK = tuple(object() for _ in range(4000))


def equal_key_block_defect(payload: dict[str, Any]) -> bool:
    """Fires when sorting an all-equal block does not return the identity.

    Reads no field of any record: the block is 4000 anonymous objects, the
    key function is the constant 0, and the check is ``is`` position by
    position.  Under a constant key a stable sort is the identity map; any
    displacement at all is instability, observed through a channel the claim
    has no access to.
    """
    sort = payload["sort"]
    out = list(sort(_ANONYMOUS_BLOCK, lambda _record: 0))
    if len(out) != len(_ANONYMOUS_BLOCK):
        return True
    return any(a is not b for a, b in zip(out, _ANONYMOUS_BLOCK))


DETECTORS = (
    NamedDetector(
        name="chained_sort_defect",
        fires=chained_sort_defect,
        probe=_payload(stable_merge_sort),
        note="two-pass metamorphic relation: sort by minor, then by major, and "
        "check lexicographic order — never asks what the input order was",
    ),
    NamedDetector(
        name="equal_key_block_defect",
        fires=equal_key_block_defect,
        probe=_payload(stable_merge_sort),
        note="4000 anonymous objects under a constant key: a stable sort is the "
        "identity map, checked by object identity, reading no field at all",
    ),
)


# ---------------------------------------------------------------------------
# The battery and the department
# ---------------------------------------------------------------------------

TARGET = SortSubject(
    name="stable_merge_sort",
    sort=stable_merge_sort,
    note="merge sort that takes from the right run only on a strictly smaller "
    "key — the genuine article, stable by construction",
)

RIVALS = (
    SortSubject(
        name="merge_sort_right_biased",
        sort=merge_sort_right_biased,
        note="the target with '<' written as '<=' in the merge tie test: same "
        "algorithm, same complexity, same output multiset, no stability",
    ),
    SortSubject(
        name="merge_sort_gallop_bug",
        sort=merge_sort_gallop_bug,
        note="the target exactly, except that merges of combined length > 64 "
        "flip the tie rule: genuinely stable on every small input, so only a "
        "corpus with a large case can refute a claim about it",
    ),
    SortSubject(
        name="reverse_stable_merge_sort",
        sort=reverse_stable_merge_sort,
        note="preserves input order among equal keys perfectly and emits it "
        "backwards: carries all the order information, lacks the property",
    ),
    SortSubject(
        name="selection_sort_swap",
        sort=selection_sort_swap,
        note="textbook selection sort: correct, deterministic, key-only, and "
        "unstable because placing the minimum swaps an unrelated record away",
    ),
    SortSubject(
        name="shell_sort",
        sort=shell_sort,
        note="Shell sort with Knuth gaps: correct, deterministic, key-only, and "
        "unstable for every gap greater than 1",
    ),
)

BATTERY = Battery(
    name="sorting_stability",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "Every subject is a correct comparison sort with the same signature that "
        "orders by key alone; no subject can see the origin labels the verdict is "
        "read off. The rivals differ from the target only in tie handling — the "
        "nearest by one character, the sneakiest only on inputs longer than 64. "
        "Ablation tolerance is 0.5 because the measure is integer-valued, so any "
        "movement at all is a full unit; the null band uses exceedance counts and "
        "no tolerance at all."
    ),
)

PROVENANCE = Provenance(
    authored_by="party07 (sealed blind-authoring experiment; author of both the "
    "sorting implementations and the battery)",
    authored_on="2026-08-09",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=False,
    edited_after_observing_failures=False,
    notes=(
        "One author wrote the target, the rivals and the battery, so this is one "
        "line of evidence, not several: declared as a dependence rather than "
        "hidden. The pass criteria are not tuned numbers — a stable sort scores "
        "exactly 1.0 concordance and the ablation measure is integer-valued, so "
        "the thresholds follow from the definition of stability and were fixed "
        "before anything ran. Claims and detectors observe the subject's output "
        "but no oracle computes its expectation by calling the subject: the "
        "expected order is derived from the definition of stability, and the "
        "detectors are metamorphic and identity-based respectively. "
        "Disclosure behind the edited_after_observing_failures=False "
        "declaration: after the first audit run the decoys and lesions were "
        "made total over probes from outside this department, and the lesions "
        "were given the ability to insert their violating pattern into a host "
        "with nothing to corrupt. No threshold, no claim, no expected verdict, "
        "no rival and no corpus case was changed at any point, the claim "
        "outcomes were identical before and after, and every edit was followed "
        "by a fresh full audit whose count is recorded in NOTES.md."
    ),
)

REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="preserves_equal_key_order",
        claim=preserves_equal_key_order,
        distinguishes=True,
        note="the real claim: fires for the target and for none of the five "
        "rivals, because the corpus carries ties, origin labels, and one case "
        "long enough to expose a bug that only appears above length 64",
    ),
    ReferenceClaim(
        name="sorts_correctly",
        claim=sorts_correctly,
        distinguishes=False,
        note="correctness alone: a true statement about the target that every "
        "rival satisfies as well, so it distinguishes nothing",
    ),
    ReferenceClaim(
        name="stable_on_short_inputs",
        claim=stable_on_short_inputs,
        distinguishes=False,
        note="stability checked only on the cases of length ≤ 64: survives four "
        "rivals and is shared with merge_sort_gallop_bug, which is exactly "
        "stable there — the claim a lazy corpus would have licensed",
    ),
)

DEPARTMENT = Department(
    name="sorting_stability",
    summary=(
        "Is a sorting implementation stable — does it leave records with equal "
        "keys in the order they arrived? Refereed against five correct sorts "
        "that lack the property, three ablations of the corpus, two null models "
        "and four planted tie inversions."
    ),
    battery=BATTERY,
    door="docs/doors/sorting_stability.md",
    modules=("blind/party07/department.py",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery justifies only that a stability claim about one "
        "implementation is being read off its treatment of ties on the declared "
        "corpus — not off correctness, output length, or the mere presence of "
        "labels — and says nothing about its stability on inputs outside that "
        "corpus, its complexity, or any other implementation."
    ),
    provenance=PROVENANCE,
)


if __name__ == "__main__":  # pragma: no cover - author's own bench
    from harness.protocol import run_ablation, run_battery, run_null_band, run_detector

    for reference in REFERENCE_CLAIMS:
        verdict = run_battery(BATTERY, reference.claim, name=reference.name)
        print(f"{verdict.summary()}  [expected distinguishes={reference.distinguishes}] "
              f"-> {verdict.distinguishes}")
    absurd = run_battery(BATTERY, ABSURD_CLAIM, name="ABSURD_CLAIM")
    print(absurd.summary())
    print("   target:", absurd.target, " rivals:", dict(absurd.rivals))

    ablation = run_ablation(BATTERY, tie_evidence, tolerance=0.5, name="tie_evidence")
    print(f"ablation baseline={ablation.baseline:g} decoys="
          f"{ {k: round(v, 3) for k, v in ablation.decoys.items()} } "
          f"survives={ablation.survives} unmoved_by={ablation.unmoved_by}")

    band = run_null_band(BATTERY, tie_concordance, draws=200, name="tie_concordance")
    print(band.summary(), "survives=", band.survives)

    for detector in DETECTORS:
        result = run_detector(BATTERY, detector)
        print(result.summary(), " has_power=", result.has_power,
              " smallest_detected=", result.smallest_detected)
