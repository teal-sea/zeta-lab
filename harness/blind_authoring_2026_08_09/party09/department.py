"""Department: text checksums — does this function detect single-character transposition?

The subject
-----------
A *checksum* here is any total function ``str -> int``.  The property at issue
is **transposition detection**: for a string ``s`` and two positions ``i < j``
holding *different* characters, does swapping those two characters change the
checksum?  Transposition is the second most common human keying error after
substitution, and it is the error that separates checksum designs: every
checksum in this file detects every single-character *substitution*, and only
one of them detects every single-character *transposition*.

The target
----------
``weighted_mod_257``: ``sum((i+1) * ord(c)) mod 257``.  It has the property for
a reason, not by luck.  Swapping positions ``i`` and ``j`` changes the sum by
``(w_i - w_j) * (a_i - a_j)`` where ``w_k = k+1``.  257 is prime, the weights
are distinct integers in ``1..256``, and printable-ASCII character codes differ
by at most 94, so both factors are non-zero modulo 257 and the product cannot
vanish.  The claim is a theorem for every string of length at most 256; the
corpus in this file only exhibits it.

The rivals share that structure and lack the property
-----------------------------------------------------
Each rival is a checksum a working engineer might actually reach for, each
detects every single-character substitution on this corpus just as the target
does, and each has a transposition it cannot see:

* ``flat_sum_257`` — the same modulus, the same output range, the same
  "modular sum of character codes"; only the position weights are gone.  It is
  blind to *every* transposition.
* ``ean13_alt_257`` — the 1,3,1,3 weighting of EAN-13/ISBN-13, a real standard
  designed against transposition, in the target's own modulus.  It catches
  every *adjacent* transposition and is blind to every swap between two
  positions of the same parity.
* ``weighted_256`` — the target's formula with one character of the source
  changed: modulus 256 instead of 257.  A power of two is the more natural
  choice and destroys the argument, because ``(i-j)*(a_i-a_j)`` can be a
  multiple of 256 (distance 4 with a character gap of 64, distance 16 with a
  gap of 16).  Two corpus strings contain exactly such pairs.
* ``rot9_xor`` — a rotate-and-xor rolling hash over a 9-bit register: strongly
  position-dependent, catches every adjacent transposition, and yet the
  rotation has order 9, so any two positions 9 or 18 apart are interchangeable
  to it.

If a claim about transposition detection held of any of these, it would be
detecting something other than transposition detection.

What is deliberately *not* claimed
----------------------------------
See ``SCOPE`` below.  In particular ``NOTES.md`` records a measurement that
bounds this corpus: a weight vector drawn uniformly from the full residue
range 0..256, with no design at all, is perfect on this corpus about a third
of the time.  The finite corpus therefore does not distinguish design from
luck; the modulus argument does, and the corpus only fails to contradict it.
"""

from __future__ import annotations

import hashlib
import random
import sys

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import Battery, Department, NamedDetector, ReferenceClaim  # noqa: E402
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# Frozen parameters.  Every one of these was fixed before the first execution
# of any instrument in this file; none is a tuned threshold.
# ---------------------------------------------------------------------------

WIDTH = 24
#: printable ASCII without the space, 94 characters
ALPHABET = tuple(chr(c) for c in range(33, 127))
#: a claim evaluated on fewer than this many transposition instances has not
#: been evaluated.  Vacuous truth is the hollow-battery failure mode, so a
#: corpus with nothing to test scores False, never True.
MIN_TESTABLE = 1000
#: units of the ablation measure (transposition instances), not of a rate
ABLATION_TOLERANCE = 200.0
NULL_DRAWS = 25


# ---------------------------------------------------------------------------
# The corpus
# ---------------------------------------------------------------------------


def _shuffled(seed: int) -> str:
    pool = list(ALPHABET)
    random.Random(seed).shuffle(pool)
    return "".join(pool[:WIDTH])


def _crafted(anchors: dict[int, str]) -> str:
    """A distinct-character string with chosen characters at chosen positions.

    The anchors exist to make the corpus able to *exercise* the rivals rather
    than merely coexist with them: a checksum modulo 256 is blind to a swap
    exactly when ``(i-j)*(a_i-a_j)`` is a multiple of 256, which a corpus of
    random printable strings will essentially never contain by accident.
    Choosing inputs that can refute a rival is corpus design; it does not
    touch the target, whose property is a theorem on every string here and on
    every string not here.
    """
    taken = set(anchors.values())
    pool = [c for c in ALPHABET if c not in taken]
    out, k = [], 0
    for position in range(WIDTH):
        if position in anchors:
            out.append(anchors[position])
        else:
            out.append(pool[k])
            k += 1
    return "".join(out)


CORPUS: tuple[str, ...] = tuple(
    [_shuffled(seed) for seed in range(101, 111)]
    + [
        # distance 4 with a character gap of 64, and distance 16 with a gap of
        # 16: both products are multiples of 256
        _crafted({0: "!", 4: "a", 2: "0", 18: "@"}),
        # distance 8 with a gap of 64, distance 16 with a gap of 16
        _crafted({1: "#", 9: "c", 3: "9", 19: "I"}),
    ]
)

assert all(len(s) == WIDTH and len(set(s)) == WIDTH for s in CORPUS)


# ---------------------------------------------------------------------------
# The checksums: one target, four rivals
# ---------------------------------------------------------------------------


def weighted_mod_257(s: str) -> int:
    """The target: position-weighted modular sum with a prime modulus."""
    return sum((i + 1) * ord(c) for i, c in enumerate(s)) % 257


def flat_sum_257(s: str) -> int:
    """Same modulus, same range, no position weighting."""
    return sum(ord(c) for c in s) % 257


def ean13_alt_257(s: str) -> int:
    """The EAN-13 / ISBN-13 alternating 1,3 weighting, in the target's modulus."""
    return sum((1 if i % 2 == 0 else 3) * ord(c) for i, c in enumerate(s)) % 257


def weighted_256(s: str) -> int:
    """The target's formula with a power-of-two modulus."""
    return sum((i + 1) * ord(c) for i, c in enumerate(s)) % 256


def rot9_xor(s: str) -> int:
    """A rotate-left-and-xor rolling hash over a 9-bit register."""
    h = 0
    for c in s:
        h = ((h << 1) | (h >> 8)) & 0x1FF
        h ^= ord(c)
    return h


# ---------------------------------------------------------------------------
# Subjects.  A payload carries the function, the corpus, the width and the
# declared modulus — and deliberately NOT the subject's name, so that no claim
# in this file can distinguish anything by reading a label.
# ---------------------------------------------------------------------------


class ChecksumSubject:
    def __init__(self, name: str, fn, note: str, modulus: int | None) -> None:
        self.name = name
        self._fn = fn
        self._note = note
        self._modulus = modulus

    def describe(self) -> str:
        return self._note

    def payload(self) -> dict:
        return {
            "checksum": self._fn,
            "corpus": CORPUS,
            "width": WIDTH,
            "modulus": self._modulus,
        }


TARGET = ChecksumSubject(
    "weighted_mod_257",
    weighted_mod_257,
    "sum((i+1)*ord(c)) mod 257 — distinct weights, prime modulus; every "
    "transposition of two distinct characters changes it, by primality",
    257,
)

RIVALS = (
    ChecksumSubject(
        "flat_sum_257",
        flat_sum_257,
        "sum(ord(c)) mod 257 — same modulus, same range, same substitution "
        "power; has no position weighting, so it is blind to every transposition",
        257,
    ),
    ChecksumSubject(
        "ean13_alt_257",
        ean13_alt_257,
        "the EAN-13 1,3,1,3 weighting mod 257 — a real anti-transposition "
        "standard; catches every adjacent swap, blind to every same-parity swap",
        257,
    ),
    ChecksumSubject(
        "weighted_256",
        weighted_256,
        "the target's own formula modulo 256 instead of 257 — identical "
        "weights, one character of source changed; blind wherever "
        "(i-j)*(a_i-a_j) is a multiple of 256",
        256,
    ),
    ChecksumSubject(
        "rot9_xor",
        rot9_xor,
        "rotate-left-xor rolling hash on a 9-bit register — strongly "
        "position-dependent, catches every adjacent swap; the rotation has "
        "order 9, so positions 9 and 18 apart are interchangeable to it",
        512,
    ),
)


# ---------------------------------------------------------------------------
# The measure and the claims
# ---------------------------------------------------------------------------


def _sweep(payload) -> tuple[int, int]:
    """(detected, testable) over every corpus string and every position pair.

    A pair holding equal characters is not a transposition — swapping it
    returns the same string — so it is excluded from both counts rather than
    scored as a miss.
    """
    fn = payload["checksum"]
    detected = 0
    testable = 0
    for s in payload["corpus"]:
        base = fn(s)
        chars = list(s)
        n = len(chars)
        for i in range(n - 1):
            ci = chars[i]
            for j in range(i + 1, n):
                cj = chars[j]
                if ci == cj:
                    continue
                testable += 1
                swapped = chars[:]
                swapped[i], swapped[j] = cj, ci
                if fn("".join(swapped)) != base:
                    detected += 1
    return detected, testable


def detected_transposition_count(payload) -> float:
    """Ablation / null statistic: how many transpositions the checksum sees.

    An absolute count, not a rate: a rate conditioned on "testable pairs"
    would read 1.0 for a corpus that has been ablated down to nothing, which
    is the exact reading an ablation exists to prevent.
    """
    return float(_sweep(payload)[0])


def detects_every_single_transposition(payload) -> bool:
    """THE CLAIM.  Every swap of two distinct characters changes the checksum."""
    detected, testable = _sweep(payload)
    if testable < MIN_TESTABLE:
        return False
    return detected == testable


def detects_every_single_substitution(payload) -> bool:
    """A true claim about the target that distinguishes nothing.

    Replacing one character with any other printable character changes the
    checksum.  The target has this property — and so does the crudest rival in
    the battery, which is why this claim is declared as one the battery must
    kill.
    """
    fn = payload["checksum"]
    for s in payload["corpus"]:
        base = fn(s)
        for i, c in enumerate(s):
            for replacement in ALPHABET:
                if replacement == c:
                    continue
                if fn(s[:i] + replacement + s[i + 1 :]) == base:
                    return False
    return True


def output_fits_in_nine_bits(payload) -> bool:
    """A true shape claim about the target, shared with everything in sight."""
    fn = payload["checksum"]
    return all(0 <= fn(s) < 512 for s in payload["corpus"])


# ---------------------------------------------------------------------------
# Decoys — ablation.  Same shape, substance removed.
# ---------------------------------------------------------------------------


class OrderAblatedDecoy:
    name = "order_ablated"

    def describe(self) -> str:
        return (
            "the checksum is shown the same characters with their order "
            "destroyed (input sorted before hashing): identical multiset, "
            "identical length, identical alphabet, identical output range — "
            "the ordering, which is the whole substance of a transposition "
            "question, is the only thing removed"
        )

    def substitute(self, payload):
        fn = payload["checksum"]
        return {**payload, "checksum": lambda s, fn=fn: fn("".join(sorted(s)))}


class IdentityAblatedDecoy:
    name = "identity_ablated"

    def describe(self) -> str:
        return (
            "the checksum is shown a string of the right length with the "
            "wrong content: every character replaced by the string's own "
            "first character. Length, position count and output range "
            "survive; character identity — the other half of the substance "
            "of a transposition question — does not. It is deliberately the "
            "conservative version of this ablation: position 0 still feeds "
            "the constant, so the 276 swaps that move a new character into "
            "position 0 stay visible and the measure falls to 276 rather "
            "than to 0"
        )

    def substitute(self, payload):
        fn = payload["checksum"]
        return {
            **payload,
            "checksum": lambda s, fn=fn: fn(s[:1] * len(s)),
        }


# ---------------------------------------------------------------------------
# Surrogates — null models.  No substantive input at all.
# ---------------------------------------------------------------------------


class BaggedContentHash:
    """Null model: content with no position."""

    name = "bagged_content_hash"

    def __init__(self) -> None:
        self._rng = random.Random(20260809)

    def describe(self) -> str:
        return (
            "a fresh random substitution table per draw, summed mod 257: a "
            "checksum built from the characters alone, with position nowhere "
            "in the construction"
        )

    def sample(self):
        table = [self._rng.randrange(257) for _ in range(128)]
        return {
            "checksum": lambda s, table=table: sum(table[ord(c)] for c in s) % 257,
            "corpus": CORPUS,
            "width": WIDTH,
            "modulus": 257,
        }


class UniformRandomOracle:
    """Null model: no design at all, only the output width."""

    name = "uniform_random_oracle"

    def __init__(self) -> None:
        self._rng = random.Random(11235813)

    def describe(self) -> str:
        return (
            "a freshly keyed random function from strings to 0..256: every "
            "design decision removed, only the output range kept — the null "
            "that says 'any 9-bit hash catches most transpositions by "
            "accident'"
        )

    def sample(self):
        key = self._rng.getrandbits(64).to_bytes(8, "big")
        def fn(s: str, key=key) -> int:
            digest = hashlib.blake2b(key + s.encode("utf-8"), digest_size=8).digest()
            return int.from_bytes(digest, "big") % 257
        return {"checksum": fn, "corpus": CORPUS, "width": WIDTH, "modulus": 257}


class UndesignedWeights:
    """Null model: the target's exact construction with the design removed."""

    name = "undesigned_weights"

    def __init__(self) -> None:
        self._rng = random.Random(31415926)

    def describe(self) -> str:
        return (
            "the target's formula with the weight vector drawn i.i.d. from "
            "the target's own weight range 1..24 and the same prime modulus: "
            "same shape, same range, same cost, the distinctness of the "
            "weights (the entire design) replaced by chance"
        )

    def sample(self):
        weights = [self._rng.randint(1, WIDTH) for _ in range(WIDTH)]
        def fn(s: str, weights=weights) -> int:
            return sum(weights[i % WIDTH] * ord(c) for i, c in enumerate(s)) % 257
        return {"checksum": fn, "corpus": CORPUS, "width": WIDTH, "modulus": 257}


# ---------------------------------------------------------------------------
# Lesions — planted, known violations of exactly the property at issue.
#
# Each lesion makes a contiguous block of positions mutually interchangeable
# by canonicalising (sorting) that block before hashing.  The block size sets
# the magnitude, and the magnitude is *measured* on the target payload at
# import time rather than asserted: it is the fraction of the corpus's
# transposition instances that the planted fault renders invisible.
# ---------------------------------------------------------------------------


class BlockSortLesion:
    def __init__(self, name: str, lo: int, hi: int) -> None:
        self.name = name
        self._lo = lo
        self._hi = hi
        detected, testable = _sweep(self.apply(TARGET.payload()))
        self.magnitude = (testable - detected) / testable

    def describe(self) -> str:
        return (
            f"positions {self._lo}..{self._hi - 1} are canonicalised (sorted) "
            f"before hashing, so those {self._hi - self._lo} positions become "
            f"mutually interchangeable; {self.magnitude:.2%} of the corpus's "
            "transposition instances become invisible, everything else is "
            "left exactly as it was"
        )

    def apply(self, payload):
        fn = payload["checksum"]
        lo, hi = self._lo, self._hi
        def lesioned(s: str, fn=fn, lo=lo, hi=hi) -> int:
            chars = list(s)
            chars[lo:hi] = sorted(chars[lo:hi])
            return fn("".join(chars))
        return {**payload, "checksum": lesioned}


LESIONS = (
    BlockSortLesion("swap_blind_last_two", 22, 24),
    BlockSortLesion("swap_blind_block_of_4", 0, 4),
    BlockSortLesion("swap_blind_block_of_8", 8, 16),
    BlockSortLesion("swap_blind_block_of_16", 4, 20),
    BlockSortLesion("swap_blind_everywhere", 0, 24),
)


# ---------------------------------------------------------------------------
# Detectors.  Neither is the claim, its negation, or a paraphrase of it; each
# is demonstrably independent of it, and the demonstration is a subject
# already in this battery (see the notes).
# ---------------------------------------------------------------------------

_PROBE_BASE_CHAR = "A"
_PROBE_CHARS = ("B", "0", "z", "]")


def position_fingerprint_collision(payload) -> bool:
    """Fires when two positions are indistinguishable under *substitution*.

    Never performs a transposition.  For each position it records the tuple of
    checksums obtained by writing each probe character there, on a constant
    background string, and fires when two positions produce the same tuple.

    This is not the claim in disguise, and the battery contains the proof:
    ``weighted_256`` fails the claim on this corpus, and this detector is
    silent on it, because its per-position responses stay distinct modulo 256.
    An instrument that is quiet where the claim dies is a different
    instrument.
    """
    fn = payload["checksum"]
    width = payload["width"]
    base = [_PROBE_BASE_CHAR] * width
    fingerprints = []
    for i in range(width):
        row = []
        for c in _PROBE_CHARS:
            probe = base[:]
            probe[i] = c
            row.append(fn("".join(probe)))
        fingerprints.append(tuple(row))
    return len(set(fingerprints)) < len(fingerprints)


_X_CHARS = ("#", "m")
_Y_CHARS = ("$", "n")


def additive_separability_broken(payload) -> bool:
    """Fires when the checksum is not additively separable across positions.

    A mixed second difference: write x at position i and y at position j for
    two choices of each, and check ``f(x0,y0) - f(x0,y1) - f(x1,y0) +
    f(x1,y1) == 0`` in the declared modulus.  A plain positional-weight sum
    satisfies this identically; a checksum that reorders, clamps or otherwise
    couples two positions does not.

    Logically independent of the claim in both directions, and again the
    battery contains the witnesses: ``flat_sum_257`` detects *no*
    transposition and is perfectly separable (this detector is silent on it),
    while ``rot9_xor`` detects nearly all of them and is not separable over
    the integers (this detector fires on it).  Its silence therefore says
    "the arithmetic is the plain weighted sum it appears to be", which is a
    different assertion from "transpositions are detected".
    """
    fn = payload["checksum"]
    width = payload["width"]
    modulus = payload["modulus"]
    base = [_PROBE_BASE_CHAR] * width
    for i in range(width - 1):
        for j in range(i + 1, width):
            values = []
            for x in _X_CHARS:
                for y in _Y_CHARS:
                    probe = base[:]
                    probe[i] = x
                    probe[j] = y
                    values.append(fn("".join(probe)))
            mixed = values[0] - values[1] - values[2] + values[3]
            if modulus:
                if mixed % modulus != 0:
                    return True
            elif mixed != 0:
                return True
    return False


#: The clean probe both detectors are calibrated against, and the payload the
#: decoys and lesions are applied to: the target with nothing planted in it.
#: Declared explicitly rather than left to the ``None`` default, so that
#: "clean" is a stated object an auditor can pick up and hand to any
#: instrument, not something reconstructed from a default rule.
CLEAN_PROBE = TARGET.payload()

DETECTORS = (
    NamedDetector(
        name="position_fingerprint_collision",
        fires=position_fingerprint_collision,
        probe=CLEAN_PROBE,
        note=(
            "two positions carry the same single-substitution response "
            "signature on a constant background — a substitution instrument, "
            "not a transposition one; silent on weighted_256, which the claim "
            "kills"
        ),
    ),
    NamedDetector(
        name="additive_separability_broken",
        fires=additive_separability_broken,
        probe=CLEAN_PROBE,
        note=(
            "the mixed second difference across two positions is non-zero in "
            "the declared modulus — the checksum couples positions instead of "
            "summing them; silent on flat_sum_257, which detects nothing"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery, the reference claims, the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="transposition_detection",
    target=TARGET,
    rivals=RIVALS,
    decoys=(OrderAblatedDecoy(), IdentityAblatedDecoy()),
    surrogates=(BaggedContentHash(), UniformRandomOracle(), UndesignedWeights()),
    lesions=LESIONS,
    notes=(
        "Every rival detects every single-character substitution on this "
        "corpus, exactly as the target does; each one fails on transposition "
        "for a stated algebraic reason. Payloads carry no subject name, so no "
        "claim here can distinguish by label. The two decoys ablate the two "
        "substantive dimensions of a transposition question one at a time — "
        "which character is where (identity) and in what order (position) — "
        "and each drops the measure from 3312 detected instances to 0 and to "
        "276 respectively, and flips the department's claim to False. Lesion "
        "magnitudes are measured on the clean probe at import, not asserted, "
        "and span 0.4% to 100% of the corpus's transposition instances."
    ),
)

REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="detects_every_single_transposition",
        claim=detects_every_single_transposition,
        distinguishes=True,
        note=(
            "the department's own claim: true of the target by primality of "
            "257, and false of all four rivals — flat_sum_257 everywhere, "
            "ean13_alt_257 on same-parity pairs, weighted_256 where the "
            "product is a multiple of 256, rot9_xor at distances 9 and 18"
        ),
    ),
    ReferenceClaim(
        name="detects_every_single_substitution",
        claim=detects_every_single_substitution,
        distinguishes=False,
        note=(
            "a true and non-trivial claim about the target that the battery "
            "must kill: flat_sum_257 has it too, so it cannot be the reason "
            "the target detects transpositions"
        ),
    ),
    ReferenceClaim(
        name="output_fits_in_nine_bits",
        claim=output_fits_in_nine_bits,
        distinguishes=False,
        note=(
            "a true shape claim shared with every rival: a battery that "
            "passed this would be reading the output range and calling it "
            "structure"
        ),
    ),
)

SCOPE = (
    "Surviving this battery justifies exactly one thing: on this fixed corpus "
    "of 12 strings of 24 distinct printable ASCII characters, the target's "
    "output changes under all 3312 transpositions of two distinct characters "
    "while four structure-matched alternatives — including the EAN-13 "
    "weighting and the same formula modulo 256 — each miss at least one. It "
    "does not establish anything about strings longer than 256 characters, "
    "repeated characters, two or more simultaneous errors, adversarially "
    "chosen inputs, or collision resistance; and it does not show the target's "
    "weight vector was *designed* rather than lucky, since an undesigned "
    "weight vector drawn from the full residue range is perfect on this corpus "
    "about a third of the time. The design argument is the primality of 257, "
    "which this corpus exhibits and does not prove."
)

PROVENANCE = Provenance(
    authored_by="party09 (blind department author; audit source sealed)",
    authored_on="2026-08-09",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=False,
    edited_after_observing_failures=False,
    notes=(
        "One author wrote both the checksums and the battery, so this is one "
        "line of evidence, not two. No expected value is ever derived from a "
        "subject: every verdict is an invariant over the subject's own "
        "outputs (an inequality, a tuple collision, a mixed difference), so "
        "there is no oracle to contaminate. The claim and the two detectors "
        "share nothing but the payload under test — the claim swaps character "
        "pairs, the detectors substitute single characters and take second "
        "differences — and the file's thresholds (MIN_TESTABLE=1000, "
        "ABLATION_TOLERANCE=200, NULL_DRAWS=25) were fixed before any "
        "instrument in it was executed and were not changed afterwards."
    ),
)

DEPARTMENT = Department(
    name="checksum_transposition",
    summary=(
        "Text checksums and the transposition question: does a checksum's "
        "output change when two distinct characters swap places? The target "
        "is a prime-modulus positional weighted sum; the rivals are four "
        "checksums that share its structure and each miss a transposition it "
        "catches."
    ),
    battery=BATTERY,
    door="docs/doors/checksum-transposition.md",
    modules=("blind/party09/department.py",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=SCOPE,
    provenance=PROVENANCE,
)


# ---------------------------------------------------------------------------
# The transparently absurd claim, for the battery to kill
# ---------------------------------------------------------------------------

ABSURD_CLAIM_TEXT = (
    "The checksum is auspicious: for at least one corpus string its value "
    "falls in the seventh house (checksum mod 12 == 7, Libra), the sign of "
    "balance — and a balanced checksum is a trustworthy one."
)


def ABSURD_CLAIM(payload) -> bool:
    fn = payload["checksum"]
    return any(fn(s) % 12 == 7 for s in payload["corpus"])


# ---------------------------------------------------------------------------
# Local self-report (never runs under the sealed audit runner, which imports
# this file under a different module name).
# ---------------------------------------------------------------------------

if __name__ == "__main__":  # pragma: no cover
    from harness.protocol import (
        run_ablation,
        run_battery,
        run_detector,
        run_null_band,
        run_nulls,
    )

    print(DEPARTMENT.describe())
    print()

    for reference in REFERENCE_CLAIMS:
        verdict = run_battery(BATTERY, reference.claim, name=reference.name)
        ok = "OK " if verdict.distinguishes == reference.distinguishes else "MISMATCH"
        print(f"[{ok}] {verdict.summary()}")
        print(f"         target={verdict.target} rivals={dict(verdict.rivals)}")
    print()

    absurd = run_battery(BATTERY, ABSURD_CLAIM, name="ABSURD_CLAIM (astrology)")
    print("ABSURD_CLAIM:", ABSURD_CLAIM_TEXT)
    print("  ", absurd.summary())
    print("   target=", absurd.target, "rivals=", dict(absurd.rivals))
    print("   killed by the battery:", not absurd.distinguishes)
    print()

    ablation = run_ablation(
        BATTERY,
        detected_transposition_count,
        tolerance=ABLATION_TOLERANCE,
        name="detected_transposition_count",
    )
    print(
        f"ablation: baseline={ablation.baseline:g} decoys={dict(ablation.decoys)} "
        f"survives={ablation.survives} unmoved_by={ablation.unmoved_by}"
    )

    nulls = run_nulls(
        BATTERY,
        detected_transposition_count,
        tolerance=ABLATION_TOLERANCE,
        name="detected_transposition_count",
    )
    print(
        f"nulls (one draw, distance {ABLATION_TOLERANCE:g}): observed="
        f"{nulls.observed:g} surrogates={dict(nulls.surrogates)} "
        f"survives={nulls.survives} reproduced_by={nulls.reproduced_by}"
    )

    band = run_null_band(
        BATTERY,
        detected_transposition_count,
        draws=NULL_DRAWS,
        name="detected_transposition_count",
    )
    print("null band:", band.summary())
    print("   exceedances:", band.exceedances, "survives=", band.survives)
    print()

    for detector in DETECTORS:
        power = run_detector(BATTERY, detector)
        print(f"detector {detector.name}: {power.summary()}")
        print(
            f"   false_alarm={power.false_alarm} fired={dict(power.fired)} "
            f"smallest_detected={power.smallest_detected}"
        )
        for rival in RIVALS:
            print(f"   on rival {rival.name}: fires={detector.fires(rival.payload())}")
    print()
    print("lesion magnitudes:", {l.name: round(l.magnitude, 5) for l in LESIONS})
    print()

    claim = detects_every_single_transposition
    print(f"clean probe: claim={claim(CLEAN_PROBE)} "
          f"count={detected_transposition_count(CLEAN_PROBE):g} "
          f"detectors={[d.fires(CLEAN_PROBE) for d in DETECTORS]}")
    for decoy in BATTERY.decoys:
        moved = decoy.substitute(CLEAN_PROBE)
        print(f"decoy {decoy.name}: claim={claim(moved)} "
              f"count={detected_transposition_count(moved):g} "
              f"detectors={[d.fires(moved) for d in DETECTORS]}")
    for lesion in LESIONS:
        hurt = lesion.apply(CLEAN_PROBE)
        print(f"lesion {lesion.name}: claim={claim(hurt)} "
              f"count={detected_transposition_count(hurt):g} "
              f"detectors={[d.fires(hurt) for d in DETECTORS]}")
