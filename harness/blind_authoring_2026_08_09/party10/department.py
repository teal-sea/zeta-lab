"""Department: **rng_period** — does this generator's emitted stream repeat soon?

The toy domain is pseudorandom number generators, and the property at issue is
the crudest failure a generator can have: a *short period*. The department is
built so that the only thing any instrument is allowed to look at is the
emitted byte window. Nothing consults a generator's internal state, its
declared period, or its name — payloads carry no identity at all, so a claim
has no label to read.

Why the rivals are close
------------------------
The target is a 16-bit Galois LFSR read through its high byte. Two of the three
rivals are *the same code with a different tap constant*: same word size, same
step function, same 8-bit truncation, same seed, same window. One 16-bit
integer separates the target (emitted period 372) from the rival whose period
is 65535. If a claim about "short period" fires on that rival, the claim was
reading the shape of a truncated linear generator, not its period, and it
should be embarrassing to have proposed it. The third rival is a full-period
truncated LCG mod 2**16, a different recurrence with the same output shape; it
is there because it carries a famous trap — the low bit of a power-of-two LCG's
output cycles with period 512 no matter how long the generator's period is —
and one of the reference claims walks straight into it.

Criteria were frozen before any generator was run (see NOTES.md); the subject
constants were then searched for until they met those criteria.
"""

from __future__ import annotations

import math
import random
import sys
from collections.abc import Mapping, Sequence

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import Battery, Department, NamedDetector, ReferenceClaim  # noqa: E402
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# Pre-registered constants (frozen before any generator was executed)
# ---------------------------------------------------------------------------

WINDOW = 4096          # emitted values observed per subject
BITS = 8               # output width
SEED = 0xACE1          # one shared seed for every subject
SHORT_PERIOD = 1024    # a stream is "short-period" when its exact period <= this
BIRTHDAY_WINDOW = 64   # for the value-recurrence reference claim
SIGMA = 0.5 / math.sqrt(WINDOW)
DETECTOR_Z = 5.0       # fire at 5 sigma
ABLATION_TOLERANCE = 1.0
NULL_DRAWS = 200
MASK16 = 0xFFFF
MASK64 = (1 << 64) - 1


# ---------------------------------------------------------------------------
# Generators.  Each is a producer: (seed, n) -> tuple of n 8-bit values.
# ---------------------------------------------------------------------------


def _galois_lfsr(taps: int):
    """16-bit Galois LFSR, emitting the high byte of the state."""

    def produce(seed: int, n: int) -> tuple[int, ...]:
        x = seed & MASK16
        out = []
        for _ in range(n):
            lsb = x & 1
            x >>= 1
            if lsb:
                x ^= taps
            out.append((x >> 8) & 0xFF)
        return tuple(out)

    return produce


def _lcg16(a: int, c: int):
    """x <- (a*x + c) mod 2**16, emitting the high byte."""

    def produce(seed: int, n: int) -> tuple[int, ...]:
        x = seed & MASK16
        out = []
        for _ in range(n):
            x = (a * x + c) & MASK16
            out.append((x >> 8) & 0xFF)
        return tuple(out)

    return produce


def _splitmix(seed: int, n: int) -> tuple[int, ...]:
    """A known-good long-period generator; the clean host for the lesions."""
    z = seed & MASK64
    out = []
    for _ in range(n):
        z = (z + 0x9E3779B97F4A7C15) & MASK64
        y = z
        y = ((y ^ (y >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        y = ((y ^ (y >> 27)) * 0x94D049BB133111EB) & MASK64
        y ^= y >> 31
        out.append((y >> 24) & 0xFF)
    return tuple(out)


def _payload(produce, *, window: int = WINDOW, bits: int = BITS, seed: int = SEED) -> dict:
    """The one payload shape every instrument in this department consumes.

    Plain data only — three keys, two ints and a tuple of ints. Deliberately
    carries no name, no label, no declared period and no live generator
    handle: a claim that wanted to cheat would have nothing to read, and every
    role transforms the same emitted window rather than reaching back into the
    generator that produced it.
    """
    return {
        "bits": bits,
        "window": window,
        "outputs": produce(seed, window),
    }


# ---------------------------------------------------------------------------
# Measurements.  Two independent code paths: exact repetition, and bit balance.
# ---------------------------------------------------------------------------


def exact_period(seq) -> int:
    """Smallest p with seq[i] == seq[i+p] for every valid i; len(seq) if none.

    KMP prefix function: p = n - pi[n-1].  This never looks at the generator,
    only at the emitted values.
    """
    n = len(seq)
    if n == 0:
        return 0
    pi = [0] * n
    k = 0
    for i in range(1, n):
        while k and seq[i] != seq[k]:
            k = pi[k - 1]
        if seq[i] == seq[k]:
            k += 1
        pi[i] = k
    return n - pi[-1]


def shortness(payload) -> float:
    """log2(window / exact period): 0 when nothing repeats, larger when it does."""
    outs = payload["outputs"]
    return math.log2(len(outs) / exact_period(outs))


def _bit_fraction(outs, bit: int) -> float:
    return sum((v >> bit) & 1 for v in outs) / len(outs)


def _rewrite(payload, transform):
    """Apply ``transform`` to the emitted window, wherever it is handed to us.

    Every decoy and every lesion here is a transformation of *a sequence of
    emitted values*; the payload dict is only a wrapper. So the roles accept
    the wrapper, a bare sequence of values, or a single value, and give back
    the same kind of thing. A transform that only worked on this department's
    own dict would be untestable by anything that did not already know the
    department, which is the opposite of what a control is for.
    """
    if isinstance(payload, Mapping):
        rewritten = dict(payload)
        if "outputs" in payload:
            rewritten["outputs"] = transform(tuple(payload["outputs"]))
            return rewritten
        for key, value in payload.items():
            if isinstance(value, (list, tuple)) and all(isinstance(v, int) for v in value):
                rewritten[key] = _same_kind(value, transform(tuple(value)))
        return rewritten
    if isinstance(payload, (list, tuple)):
        return _same_kind(payload, transform(tuple(payload)))
    if isinstance(payload, Sequence) and not isinstance(payload, (str, bytes)):
        return _same_kind(list(payload), transform(tuple(payload)))
    if isinstance(payload, bool):
        return payload
    if isinstance(payload, int):
        return transform((payload,))[0]
    return payload


def _same_kind(original, values):
    return list(values) if isinstance(original, list) else tuple(values)




# ---------------------------------------------------------------------------
# Roles
# ---------------------------------------------------------------------------


class Generator:
    """A subject: the target or a rival."""

    def __init__(self, name: str, note: str, produce):
        self.name = name
        self._note = note
        self._produce = produce
        self._cached: dict | None = None

    def describe(self) -> str:
        return self._note

    def payload(self) -> dict:
        if self._cached is None:
            self._cached = _payload(self._produce)
        return dict(self._cached)


class StreamDecoy:
    """A decoy: same payload shape, substantive content replaced."""

    def __init__(self, name: str, note: str, transform):
        self.name = name
        self._note = note
        self._transform = transform

    def describe(self) -> str:
        return self._note

    def substitute(self, payload):
        return _rewrite(payload, self._transform)


class NullStream:
    """A surrogate: a stream drawn from a model with no generator in it."""

    def __init__(self, name: str, note: str, draw, seed: int):
        self.name = name
        self._note = note
        self._draw = draw
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return self._note

    def sample(self):
        return {"bits": BITS, "window": WINDOW, "outputs": self._draw(self._rng, WINDOW)}


class BitLesion:
    """A lesion: a known amount of per-output entropy destroyed."""

    def __init__(self, name: str, note: str, magnitude: float, damage):
        self.name = name
        self._note = note
        self.magnitude = float(magnitude)
        self._damage = damage

    def describe(self) -> str:
        return self._note

    def apply(self, payload):
        return _rewrite(payload, self._damage)


# ---------------------------------------------------------------------------
# Subjects
# ---------------------------------------------------------------------------

TARGET = Generator(
    "lfsr16_taps_e272",
    "16-bit Galois LFSR, taps 0xE272, high byte emitted: the state returns to the "
    "seed after 372 steps, so the emitted window repeats 11 times inside it. Its "
    "bit planes are balanced to 0.005 and it emits 220 of the 256 possible values, "
    "so it does not look degenerate to anything but a repetition test.",
    _galois_lfsr(0xE272),
)

RIVALS = (
    Generator(
        "lfsr16_taps_b400",
        "The same LFSR code, the same word size, the same high-byte truncation and "
        "the same seed — one tap constant different (0xB400, primitive). Period "
        "65535, sixteen times the observed window, so nothing repeats in it. If a "
        "short-period claim fires here it is reading truncated-LFSR shape, not period.",
        _galois_lfsr(0xB400),
    ),
    Generator(
        "lfsr16_taps_fe73",
        "The same LFSR code again, taps 0xFE73: period 13107 — decidedly not maximal, "
        "and still three times the window. Kills the inference 'the period is not "
        "maximal, therefore it is short'.",
        _galois_lfsr(0xFE73),
    ),
    Generator(
        "lcg16_a25173_c13849",
        "A different recurrence with the same output shape: x <- (25173x + 13849) mod "
        "2**16, high byte emitted, full period 65536. Carries the power-of-two LCG "
        "trap — the low bit of its *output* cycles every 512 steps while the generator "
        "itself never repeats in the window.",
        _lcg16(25173, 13849),
    ),
)


# ---------------------------------------------------------------------------
# Decoys — keep the shape, remove the substance the period test reads
# ---------------------------------------------------------------------------


def _shuffle_order(outs):
    base = list(outs)
    random.Random(0xD10).shuffle(base)
    return tuple(base)


def _histogram_iid(outs):
    return tuple(random.Random(0xD20).choices(list(outs), k=len(outs)))


def _phase_jitter(outs):
    """Duplicate 8 values at even spacings, then truncate back to the window.

    4088 of the 4096 emitted values survive, in their original order and with
    their original neighbours; only the phase alignment that makes the
    repetition exact is broken, and it is broken 8 times.
    """
    n = len(outs)
    if n < 2:
        return tuple(outs)
    extra = max(1, min(8, n // 8))
    step = max(1, n // (extra + 1))
    out: list[int] = []
    for i, v in enumerate(outs):
        out.append(v)
        if i and i % step == 0 and len(out) < n + extra:
            out.append(v)
    return tuple(out[:n])


DECOYS = (
    StreamDecoy(
        "order_shuffled",
        "Exactly the same multiset of emitted values in a fixed random order: every "
        "first-order statistic — histogram, mean, bit balance — is preserved bit for "
        "bit; only the order the repetition lives in is destroyed.",
        _shuffle_order,
    ),
    StreamDecoy(
        "histogram_matched_iid",
        "The same window length redrawn i.i.d. from the stream's own empirical byte "
        "histogram: keeps the marginal distribution, keeps nothing sequential.",
        _histogram_iid,
    ),
    StreamDecoy(
        "phase_jittered",
        "The tightest ablation here: 8 emitted values out of 4096 are duplicated at "
        "even spacings, so 99.8% of the values and all local structure survive and "
        "only the phase alignment that makes the repetition exact is broken.",
        _phase_jitter,
    ),
)


# ---------------------------------------------------------------------------
# Surrogates — null models with no generator-under-test in them
# ---------------------------------------------------------------------------


def _uniform_bytes(rng, n):
    return tuple(rng.randrange(256) for _ in range(n))


def _skewed_bytes(rng, n):
    return tuple(min(255, int(abs(rng.gauss(0, 40)))) for _ in range(n))


def _walk_bytes(rng, n):
    v = rng.randrange(256)
    out = []
    for _ in range(n):
        v = (v + rng.randint(-3, 3)) % 256
        out.append(v)
    return tuple(out)


SURROGATES = (
    NullStream(
        "iid_uniform_bytes",
        "White noise: 4096 independent uniform bytes, redrawn on every sample. No "
        "recurrence of any kind, and no generator.",
        _uniform_bytes,
        seed=101,
    ),
    NullStream(
        "iid_skewed_bytes",
        "Independent bytes from a strongly skewed half-normal marginal: heavy value "
        "reuse and a badly non-uniform histogram, still no sequential structure. Shows "
        "the statistic is not reading the histogram.",
        _skewed_bytes,
        seed=202,
    ),
    NullStream(
        "bounded_random_walk",
        "A random walk mod 256 with steps in [-3, 3]: very strong serial correlation, "
        "locally almost constant, and aperiodic. Shows the statistic is not reading "
        "autocorrelation either.",
        _walk_bytes,
        seed=303,
    ),
)


# ---------------------------------------------------------------------------
# Lesions — known entropy destroyed, spanning 0.125 to 8 bits per output
# ---------------------------------------------------------------------------


def _clear_bit0_every(k):
    def damage(outs):
        return tuple(v & 0xFE if i % k == 0 else v for i, v in enumerate(outs))

    return damage


def _clear_bit0(outs):
    return tuple(v & 0xFE for v in outs)


def _clear_low_nibble(outs):
    return tuple(v & 0xF0 for v in outs)


def _freeze(outs):
    return tuple(0x5A for _ in outs)


LESIONS = (
    BitLesion(
        "bit0_stuck_every_8th",
        "The low output bit is forced to 0 on every 8th emitted value: 1/8 of one bit "
        "plane, 0.125 bits per output. The smallest planted fault in the set.",
        0.125,
        _clear_bit0_every(8),
    ),
    BitLesion(
        "bit0_stuck_every_4th",
        "The low output bit is forced to 0 on every 4th emitted value: 0.25 bits per output.",
        0.25,
        _clear_bit0_every(4),
    ),
    BitLesion(
        "bit0_stuck_always",
        "The low output bit is forced to 0 everywhere: a whole bit plane dead, 1 bit "
        "per output. The classic stuck-bit hardware fault.",
        1.0,
        _clear_bit0,
    ),
    BitLesion(
        "low_nibble_stuck",
        "The low four bits are forced to 0: half the word dead, 4 bits per output, and "
        "only 16 of 256 values reachable.",
        4.0,
        _clear_low_nibble,
    ),
    BitLesion(
        "output_frozen",
        "Every emitted value is 0x5A: the whole word dead, 8 bits per output. Total "
        "failure, and the largest planted fault in the set.",
        8.0,
        _freeze,
    ),
)


BATTERY = Battery(
    name="rng_period_battery",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "Rivals: two of the three are the target's own code with one tap constant "
        "changed, so the only difference available to a claim is the period itself. "
        "Decoys strip order while preserving the histogram exactly. Surrogates are "
        "three null models chosen to be extreme in three different directions "
        "(white, skewed, strongly autocorrelated) and periodic in none. Lesions span "
        "0.125 to 8 bits of destroyed entropy per output, a factor of 64."
    ),
)


# ---------------------------------------------------------------------------
# Detector — a genuinely different instrument from the claims
# ---------------------------------------------------------------------------


def monobit_bit_balance(payload) -> bool:
    """Fire when some output bit plane is off balance by more than 5 sigma.

    This is not the claim, its negation, or a paraphrase of it. The two
    dissociate in both directions and the dissociation is measured, not
    asserted: the target has an emitted period of 372 (claim true) and passes
    this detector with its worst bit plane 0.7 sigma off centre, while the
    ``bit0_stuck_always`` lesion applied to a splitmix stream has no repetition
    at all (claim false) and drives this detector to 64 sigma. One reads
    repetition in time; the other reads marginal bit frequency and cannot see
    order at all — it returns the same answer for every permutation of a window.
    """
    outs = payload["outputs"]
    n = len(outs)
    threshold = DETECTOR_Z * 0.5 / math.sqrt(n)
    return any(
        abs(_bit_fraction(outs, b) - 0.5) > threshold for b in range(payload["bits"])
    )


CLEAN_PROBE = _payload(_splitmix)

DETECTORS = (
    NamedDetector(
        name="monobit_bit_balance",
        fires=monobit_bit_balance,
        probe=CLEAN_PROBE,
        note=(
            "Per-bit-plane monobit test at 5 sigma (sigma = 0.5/sqrt(4096) = 0.0078). "
            "Clean probe is a splitmix stream over the same window, whose worst plane "
            "sits 1.9 sigma off centre. Measured power: fires on all five planted "
            "faults, the smallest being 0.125 bits per output (8 sigma). Blind, by "
            "construction, to any fault that leaves every marginal bit frequency at "
            "one half — which is exactly why it is not a stand-in for the period claim."
        ),
    ),
)


# ---------------------------------------------------------------------------
# Reference claims — real claims about generators, verdicts known in advance
# ---------------------------------------------------------------------------


def claim_exact_repeat_within_window(payload) -> bool:
    """The emitted window repeats exactly with some period <= 1024."""
    return exact_period(payload["outputs"]) <= SHORT_PERIOD


def claim_value_recurs_within_64(payload) -> bool:
    """Some emitted value comes back within 64 steps (a birthday collision)."""
    outs = payload["outputs"]
    last: dict[int, int] = {}
    for i, v in enumerate(outs):
        if v in last and i - last[v] < BIRTHDAY_WINDOW:
            return True
        last[v] = i
    return False


def claim_low_output_bit_cycles(payload) -> bool:
    """The low bit of the emitted stream is exactly periodic with period <= 1024."""
    return exact_period(tuple(v & 1 for v in payload["outputs"])) <= SHORT_PERIOD


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="exact_repeat_within_window",
        claim=claim_exact_repeat_within_window,
        distinguishes=True,
        note=(
            "The honest statement of the property: the emitted window returns to its "
            "own beginning within 1024 values. True of the target at period 372, false "
            "of all three rivals, whose periods are 13107, 65535 and 65536. The "
            "battery must pass this or it says no to everything."
        ),
    ),
    ReferenceClaim(
        name="value_recurs_within_64",
        claim=claim_value_recurs_within_64,
        distinguishes=False,
        note=(
            "The birthday fallacy: 'values come back quickly, so the period is short'. "
            "With 8-bit outputs a collision inside 64 samples is near-certain for any "
            "generator whatever, so this fires for the target and for all three rivals. "
            "The battery must kill it."
        ),
    ),
    ReferenceClaim(
        name="low_output_bit_cycles",
        claim=claim_low_output_bit_cycles,
        distinguishes=False,
        note=(
            "The power-of-two LCG trap: 'the low bit of the output cycles every few "
            "hundred steps, so the generator repeats'. True of the target, and equally "
            "true of the full-period LCG rival, whose output low bit cycles every 512 "
            "steps while the generator itself has period 65536. Killed by exactly one "
            "rival, which is what that rival is in the battery for."
        ),
    ),
)


PROVENANCE = Provenance(
    authored_by=(
        "party10, working only from harness/protocol.py, harness/provenance.py and "
        "harness/README.md; no audit source, no existing department, and no test file "
        "was read"
    ),
    authored_on="2026-08-10",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=True,
    edited_after_observing_failures=False,
    notes=(
        "Order of work, which is what the two contamination fields turn on: the "
        "window (4096), the seed (0xACE1), the short-period threshold (1024), the "
        "detector threshold (5 sigma), the lesion magnitudes, the ablation tolerance "
        "(1.0) and the two reference-claim windows (64, 1024) were written down "
        "before a single generator was executed. Generator constants were then "
        "searched for until they met those criteria; no criterion was moved to fit a "
        "generator, and none was moved after seeing an audit result. "
        "independent_of_subject_author is False because one process wrote both the "
        "generators and the battery — the generator families are textbook (Galois "
        "LFSR, LCG, splitmix) but their instantiation here is not independent. "
        "instruments_share_critical_dependency is True on the plain reading: every "
        "instrument reads the same emitted 4096-value window produced by the same "
        "generator code, so the period test and the bit-balance detector are two "
        "statistics over one observation, not two independent observations. "
        "oracle_calls_subject is False in the sense that matters: no measurement "
        "consults a generator's declared period, internal state, or identity — "
        "payloads carry none of the three."
    ),
)


DEPARTMENT = Department(
    name="rng_period",
    summary=(
        "Does this pseudorandom generator's emitted stream repeat within a short "
        "window? 16-bit linear generators observed only through their 8-bit output, "
        "with rivals that differ from the target by a single tap constant."
    ),
    battery=BATTERY,
    door="docs/doors/rng-period.md",
    modules=("blind/party10/department.py",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery shows only that a claim fires on one generator whose "
        "emitted byte stream repeats every 372 values and fires on none of three "
        "long-period generators built from the same recurrence families and read "
        "through the same 8-bit truncation, over one 4096-value window from one seed "
        "(0xACE1); it is not evidence about any other seed, any other window length, "
        "any generator's suitability for cryptography or simulation, or any aspect of "
        "randomness quality other than exact repetition."
    ),
    provenance=PROVENANCE,
)


# ---------------------------------------------------------------------------
# A transparently absurd claim, kept here so the battery can be shown killing it
# ---------------------------------------------------------------------------

ABSURD_CLAIM_TEXT = (
    "A generator has a short period exactly when the sum of its first twelve emitted "
    "values falls in a fire house (0, 4 or 8 modulo twelve), Aries ascendant."
)


def ABSURD_CLAIM(payload) -> bool:
    """Astrology for generators: read the first twelve outputs as a zodiac house."""
    return (sum(payload["outputs"][:12]) % 12) in (0, 4, 8)
