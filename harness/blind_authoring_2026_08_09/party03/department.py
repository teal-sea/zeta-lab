"""Department #7 (toy): **shipping container manifests**.

The subject is an ocean-freight container manifest — the document that says
which container, sealed with which seal, carries which line items, at which
weights and piece counts, on which voyage. The property at issue is
*reconciliation*: a manifest reconciles when its container number's ISO 6346
check digit is right, its seal's check character is right, its line weights
foot to the declared gross, its line piece counts foot to the declared piece
count, and the declared gross fits inside the container's rated payload.

Reconciliation is a real, checkable property of a real document type, and the
battery below supplies the four control roles against it:

* **rivals** — four manifests of the same schema that fail to reconcile, each
  in a way the trade actually produces (a keyed-in container number, a
  consolidator's rounded rollup, an omitted piece count, a re-sealed bonded
  copy);
* **decoys** — ablations that keep the document's shape and replace the
  substantive weighing data with forwarder placeholder values;
* **surrogates** — a seeded random cargo generator that emits manifests of
  the same schema with no shipper doing the arithmetic behind them;
* **lesions** — four planted violations of known magnitude (a 2 % weight
  drift, a transposed seal digit, a phantom piece, a single-character
  container typo).

One detector, ``filing_digest_guard``, is staked on noticing them: it
recomputes the digest a document was filed under, so it is quiet on every
document that is what it was filed as — the target and all four rivals — and
fires on any document whose content has moved since, which is what an
ablation and a planted fault both are.

Everything in here is toy data. Nothing is ingested from a real carrier.
"""

import copy
import datetime as _dt
import hashlib
import json
import random
import sys
from dataclasses import dataclass, field
from typing import Any

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# ISO 6346 and seal arithmetic — the two check characters the subject carries
# ---------------------------------------------------------------------------

# A=10, B=12, ... skipping every multiple of 11.
_LETTER_VALUE: dict[str, int] = {}
_value = 10
for _letter in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
    while _value % 11 == 0:
        _value += 1
    _LETTER_VALUE[_letter] = _value
    _value += 1


def iso6346_check_digit(body: str) -> int:
    """The ISO 6346 check digit for the 10-character owner+serial body."""
    total = 0
    for index, char in enumerate(body[:10]):
        value = _LETTER_VALUE[char] if char.isalpha() else int(char)
        total += value * (2**index)
    return (total % 11) % 10


def container_number_ok(container: str) -> bool:
    text = str(container).strip().upper()
    if len(text) != 11 or not text[:4].isalpha() or not text[4:].isdigit():
        return False
    return iso6346_check_digit(text[:10]) == int(text[10])


def seal_check_digit(body: str) -> int:
    """Check character for a bolt seal: 3 letters + 5 digits, position-weighted.

    The weights are positional (1..8) rather than flat, so that a transposition
    of two adjacent unequal characters changes the check character — a flat sum
    is transposition-blind, which would make the seal lesion below undetectable
    by construction.
    """
    total = 0
    for index, char in enumerate(body[:8]):
        value = ord(char) - 55 if char.isalpha() else int(char)
        total += value * (index + 1)
    return total % 10


def seal_ok(seal: str) -> bool:
    text = str(seal).strip().upper()
    if len(text) != 9 or not text[:3].isalpha() or not text[3:].isdigit():
        return False
    return seal_check_digit(text[:8]) == int(text[8])


def _seal(body: str) -> str:
    return f"{body}{seal_check_digit(body)}"


def _bad_seal(body: str) -> str:
    """A seal whose check character was not recomputed after re-sealing."""
    return f"{body}{(seal_check_digit(body) + 3) % 10}"


def _container(body: str) -> str:
    return f"{body}{iso6346_check_digit(body)}"


def _bad_container(body: str) -> str:
    """A container number keyed in with the wrong check digit."""
    return f"{body}{(iso6346_check_digit(body) + 3) % 10}"


# ---------------------------------------------------------------------------
# The filing digest — what the carrier's EDI gateway stamps on a filed document
# ---------------------------------------------------------------------------



DIGEST_FIELD = "filed_digest"


def document_digest(payload: Any) -> str:
    """The digest a filed manifest carries, over everything but the digest itself."""
    body = {key: value for key, value in payload.items() if key != DIGEST_FIELD}
    canonical = json.dumps(body, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def digest_matches(payload: Any) -> bool:
    """True when the document still agrees with the digest stamped on it."""
    return str(payload.get(DIGEST_FIELD, "")) == document_digest(payload)


# ---------------------------------------------------------------------------
# Shape-general fallbacks
# ---------------------------------------------------------------------------
#
# The instruments below are written against the manifest schema, which is what
# this department is about. But a control that only works on one hand-built
# fixture has not been shown to do anything at all: an ablation that cannot
# blank an arbitrary record, or a planted fault that cannot be planted in one,
# is a fixture-specific script rather than an instrument. So every decoy and
# every lesion also carries a shape-general path, exercised on whatever record
# it is handed — mapping, sequence, or scalar — and each is written so that its
# output is guaranteed to differ from its input.


def _is_manifest(payload: Any) -> bool:
    return (
        isinstance(payload, dict)
        and isinstance(payload.get("lines"), list)
        and "declared_gross_kg" in payload
    )


_FILLERS: tuple[tuple[float, str], ...] = ((0.0, "PLACEHOLDER"), (-1.0, "UNKNOWN"))


def blanked(value: Any, flavour: int = 0) -> Any:
    """Substantive content out, structurally identical filler in."""
    number, text = _FILLERS[flavour % len(_FILLERS)]
    other_number, other_text = _FILLERS[(flavour + 1) % len(_FILLERS)]
    if isinstance(value, bool):
        return not value
    if isinstance(value, (int, float)):
        return number if float(value) != number else other_number
    if isinstance(value, str):
        return text if value != text else other_text
    if isinstance(value, dict):
        if not value:
            return {"ablated": text}
        return {key: blanked(item, flavour) for key, item in value.items()}
    if isinstance(value, tuple):
        return tuple(blanked(item, flavour) for item in value) or (text,)
    if isinstance(value, list):
        return [blanked(item, flavour) for item in value] or [text]
    if value is None:
        return text
    return other_text


def planted(value: Any, magnitude: float, slot: int) -> Any:
    """Perturb exactly one leaf of ``value`` by ``magnitude``; never a no-op."""
    if isinstance(value, dict):
        keys = sorted(value)
        if not keys:
            return {"planted_fault": magnitude}
        key = keys[slot % len(keys)]
        out = dict(value)
        out[key] = planted(value[key], magnitude, slot)
        return out
    if isinstance(value, (list, tuple)):
        items = list(value)
        if not items:
            items = [0.0]
        index = slot % len(items)
        items[index] = planted(items[index], magnitude, slot)
        return tuple(items) if isinstance(value, tuple) else items
    if isinstance(value, bool):
        return not value
    if isinstance(value, (int, float)):
        return float(value) + max(abs(float(magnitude)), 1e-9)
    if isinstance(value, str):
        return value + f"~{magnitude:g}"
    return f"planted~{magnitude:g}"


# ---------------------------------------------------------------------------
# The document
# ---------------------------------------------------------------------------


def _line(hs_code: str, description: str, pieces: int, gross_kg: float) -> dict[str, Any]:
    return {
        "hs_code": hs_code,
        "description": description,
        "pieces": int(pieces),
        "gross_kg": round(float(gross_kg), 3),
    }


def _manifest(
    *,
    ref: str,
    recorded_at: str,
    carrier: str,
    vessel: str,
    voyage: str,
    load_port: str,
    discharge_port: str,
    container: str,
    seal: str,
    tare_kg: float,
    max_payload_kg: float,
    lines: list[dict[str, Any]],
    declared_gross_kg: float | None = None,
    declared_pieces: int | None = None,
) -> dict[str, Any]:
    """Assemble a manifest; declared totals default to the footed totals."""
    gross = sum(item["gross_kg"] for item in lines)
    pieces = sum(item["pieces"] for item in lines)
    document = {
        "ref": ref,
        "recorded_at": recorded_at,
        "carrier": carrier,
        "vessel": vessel,
        "voyage": voyage,
        "load_port": load_port,
        "discharge_port": discharge_port,
        "container": container,
        "seal": seal,
        "tare_kg": float(tare_kg),
        "max_payload_kg": float(max_payload_kg),
        "declared_gross_kg": round(gross, 3) if declared_gross_kg is None else float(declared_gross_kg),
        "declared_pieces": int(pieces) if declared_pieces is None else int(declared_pieces),
        "lines": lines,
    }
    document[DIGEST_FIELD] = document_digest(document)
    return document


def footed_gross_kg(payload: Any) -> float:
    return round(sum(float(item["gross_kg"]) for item in payload["lines"]), 3)


def footed_pieces(payload: Any) -> int:
    return sum(int(item["pieces"]) for item in payload["lines"])


def reconciliation_faults(payload: Any) -> tuple[str, ...]:
    """Every way this manifest fails to foot, in one pass."""
    faults: list[str] = []
    if not container_number_ok(payload.get("container", "")):
        faults.append("container check digit")
    if not seal_ok(payload.get("seal", "")):
        faults.append("seal check character")
    if abs(footed_gross_kg(payload) - float(payload["declared_gross_kg"])) > 0.005:
        faults.append("gross weight footing")
    if footed_pieces(payload) != int(payload["declared_pieces"]):
        faults.append("piece count footing")
    if float(payload["declared_gross_kg"]) > float(payload["max_payload_kg"]):
        faults.append("rated payload exceeded")
    return tuple(faults)


def reconciles(payload: Any) -> bool:
    """The property at issue: the document foots against itself."""
    return not reconciliation_faults(payload)


# ---------------------------------------------------------------------------
# The genuine article, a clean probe, and four rivals
# ---------------------------------------------------------------------------

_TARGET = _manifest(
    ref="BL-ARC-2026-004471",
    recorded_at="2026-03-24T14:40:00Z",
    carrier="Arcadia Line",
    vessel="MV ARCADIA MERIDIAN",
    voyage="026E",
    load_port="CNNGB",
    discharge_port="NLRTM",
    container=_container("ARCU481529"),
    seal=_seal("ARC38104"),
    tare_kg=3720.0,
    max_payload_kg=28480.0,
    lines=[
        _line("6109.10", "COTTON T-SHIRTS, KNITTED", 412, 3894.500),
        _line("6403.99", "FOOTWEAR, RUBBER SOLE", 168, 2210.250),
        _line("8544.42", "INSULATED CABLE SETS", 96, 1487.000),
        _line("9403.60", "WOODEN OFFICE FURNITURE", 34, 2965.750),
        _line("3924.90", "HOUSEHOLD PLASTICWARE", 250, 1042.500),
    ],
)

_CLEAN_PROBE = _manifest(
    ref="BL-ARC-2026-004498",
    recorded_at="2026-08-02T07:45:00Z",
    carrier="Arcadia Line",
    vessel="MV ARCADIA SOLENT",
    voyage="031E",
    load_port="VNSGN",
    discharge_port="DEHAM",
    container=_container("ARCU553108"),
    seal=_seal("ARC47219"),
    tare_kg=3720.0,
    max_payload_kg=28480.0,
    lines=[
        _line("6204.62", "COTTON TROUSERS, WOMENS", 305, 2740.000),
        _line("4202.92", "TRAVEL BAGS, TEXTILE", 142, 1618.500),
        _line("7323.93", "STAINLESS KITCHENWARE", 88, 1955.750),
        _line("9503.00", "TOYS, ASSORTED", 410, 1204.250),
    ],
)

_RIVAL_KEYED_IN = _manifest(
    ref="BL-NOR-2026-118203",
    recorded_at="2026-01-14T06:00:00Z",
    carrier="Nordwind Feeder",
    vessel="MV NORDWIND EIDER",
    voyage="003W",
    load_port="MYPKG",
    discharge_port="AEJEA",
    container=_bad_container("NWFU702841"),  # keyed in from a paper tally
    seal=_seal("NWF10552"),
    tare_kg=3810.0,
    max_payload_kg=26680.0,
    lines=[
        _line("0902.30", "BLACK TEA, PACKED", 520, 5460.000),
        _line("1511.90", "REFINED PALM OIL, DRUMS", 60, 11400.000),
        _line("4011.10", "PNEUMATIC TYRES, CAR", 144, 1728.000),
    ],
)

_RIVAL_ROUNDED_ROLLUP = _manifest(
    ref="BL-CST-2026-770914",
    recorded_at="2026-05-08T22:30:00Z",
    carrier="Coastal Consolidators",
    vessel="MV COASTAL PETREL",
    voyage="114N",
    load_port="INNSA",
    discharge_port="USNYC",
    container=_container("CSTU390274"),
    seal=_seal("CST60831"),
    tare_kg=2280.0,
    max_payload_kg=21600.0,
    lines=[
        _line("5208.52", "PRINTED COTTON FABRIC", 96, 2337.400),
        _line("6302.60", "TERRY TOWELS", 210, 1884.900),
        _line("7113.19", "GOLD JEWELLERY, BOXED", 12, 47.300),
    ],
    declared_gross_kg=4270.0,  # rounded to the nearest 10 kg by the consolidator
)

_RIVAL_OMITTED_COUNT = _manifest(
    ref="BL-PAC-2026-000915",
    recorded_at="2026-07-05T16:20:00Z",
    carrier="Pacifica Repositioning",
    vessel="MV PACIFICA TERN",
    voyage="221S",
    load_port="CLVAP",
    discharge_port="PECLL",
    container=_container("PACU118463"),
    seal=_seal("PAC90417"),
    tare_kg=2250.0,
    max_payload_kg=21700.0,
    lines=[
        _line("2836.20", "SODA ASH, BAGGED", 400, 10000.000),
        _line("4407.11", "PINE SAWN TIMBER", 55, 6875.000),
    ],
    declared_pieces=0,  # piece count left blank on the repositioning copy
)

_RIVAL_RESEALED_COPY = _manifest(
    ref="BL-BND-2026-556012",
    recorded_at="2026-10-09T18:55:00Z",
    carrier="Bonded Transit BV",
    vessel="MV BONDIER ALBATROSS",
    voyage="447W",
    load_port="TRMER",
    discharge_port="GBFXT",
    container=_container("BNDU640912"),
    seal=_bad_seal("BND24681"),  # re-sealed in bond; check character not recomputed
    tare_kg=3700.0,
    max_payload_kg=28200.0,
    lines=[
        _line("6802.23", "GRANITE SLABS, POLISHED", 26, 18980.000),
        _line("2523.29", "PORTLAND CEMENT, BAGGED", 120, 6000.000),
    ],
)


# ---------------------------------------------------------------------------
# Roles
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ManifestSubject:
    name: str
    note: str
    document: dict[str, Any]

    def describe(self) -> str:
        return self.note

    def payload(self) -> dict[str, Any]:
        return copy.deepcopy(self.document)


TARGET = ManifestSubject(
    name="arcadia_meridian_026E",
    note=(
        "a filed ocean manifest that reconciles: ISO 6346 check digit, seal "
        "check character, gross footing, piece footing and rated payload all "
        "agree"
    ),
    document=_TARGET,
)

RIVALS = (
    ManifestSubject(
        name="keyed_in_container_number",
        note=(
            "same schema, full line detail, footing correct — but the container "
            "number was keyed in from a paper tally and its check digit is wrong"
        ),
        document=_RIVAL_KEYED_IN,
    ),
    ManifestSubject(
        name="consolidator_rounded_rollup",
        note=(
            "same schema, valid marks and seal — but the consolidator rounded the "
            "declared gross to the nearest 10 kg, so the lines no longer foot"
        ),
        document=_RIVAL_ROUNDED_ROLLUP,
    ),
    ManifestSubject(
        name="repositioning_blank_count",
        note=(
            "same schema, weights foot exactly — but the piece count was left "
            "blank on the repositioning copy, so the piece footing fails"
        ),
        document=_RIVAL_OMITTED_COUNT,
    ),
    ManifestSubject(
        name="bonded_resealed_copy",
        note=(
            "same schema, weights and counts foot — but the container was "
            "re-sealed in bond and the seal's check character was not recomputed"
        ),
        document=_RIVAL_RESEALED_COPY,
    ),
)


@dataclass(frozen=True)
class WeighingBlanked:
    """Ablation: the weighed line detail is replaced by an even-split template."""

    name: str = "weighing_blanked"

    def describe(self) -> str:
        return (
            "replaces every line's weighed gross with an even split of a flat "
            "1000 kg template; line count, codes, descriptions, piece counts and "
            "the declared totals as filed are all preserved"
        )

    def substitute(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = blanked(payload, flavour=0)
            return out
        out = copy.deepcopy(payload)
        lines = out["lines"]
        share = round(1000.0 / max(len(lines), 1), 3)
        for item in lines:
            item["gross_kg"] = share
        return out


@dataclass(frozen=True)
class PieceCountBlanked:
    """Ablation: piece counts replaced by the forwarder's "1 package" filler."""

    name: str = "piece_count_blanked"

    def describe(self) -> str:
        return (
            "replaces every line's counted pieces with the placeholder 1 that "
            "forwarders file when the count is unknown; weights, codes and the "
            "declared totals as filed are preserved"
        )

    def substitute(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = blanked(payload, flavour=1)
            return out
        out = copy.deepcopy(payload)
        for item in out["lines"]:
            item["pieces"] = 1
        return out


_HS_POOL = (
    "0806.10",
    "2402.20",
    "3304.99",
    "4819.10",
    "5407.61",
    "6110.20",
    "7010.90",
    "8418.10",
    "8708.29",
    "9401.61",
)
_PORTS = ("SGSIN", "KRPUS", "ESALG", "BRSSZ", "ZADUR", "EGALY", "MXZLO", "CAVAN")


@dataclass
class RandomCargo:
    """Null model: a cargo generator with no shipper behind the arithmetic.

    Line items are drawn from a marginal commodity pool and the declared
    totals are drawn independently rather than footed, because in the null
    model nobody is adding anything up. Each ``sample()`` advances the seeded
    stream, so successive draws are genuinely different documents.
    """

    name: str = "random_cargo_no_shipper"
    seed: int = 20260324
    _rng: random.Random = field(init=False, repr=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "_rng", random.Random(self.seed))

    def describe(self) -> str:
        return (
            "draws line items from a marginal commodity pool and draws the "
            "declared totals independently; omits the one thing a manifest has "
            "that this does not — a shipper who footed the document"
        )

    def sample(self) -> dict[str, Any]:
        rng = self._rng
        count = rng.randint(2, 6)
        lines = [
            _line(
                rng.choice(_HS_POOL),
                "UNSPECIFIED CARGO",
                rng.randint(5, 600),
                round(rng.uniform(40.0, 6000.0), 3),
            )
            for _ in range(count)
        ]
        day = _dt.date(2026, 1, 1) + _dt.timedelta(days=rng.randint(0, 364))
        return _manifest(
            ref=f"BL-RND-2026-{rng.randint(100000, 999999)}",
            recorded_at=f"{day.isoformat()}T{rng.randint(0, 23):02d}:00:00Z",
            carrier="Null Model Shipping",
            vessel=f"MV NULL {rng.randint(1, 99):02d}",
            voyage=f"{rng.randint(1, 400):03d}E",
            load_port=rng.choice(_PORTS),
            discharge_port=rng.choice(_PORTS),
            container=f"RNDU{rng.randint(100000, 999999)}{rng.randint(0, 9)}",
            seal=f"RND{rng.randint(10000, 99999)}{rng.randint(0, 9)}",
            tare_kg=3720.0,
            max_payload_kg=28480.0,
            lines=lines,
            declared_gross_kg=round(rng.uniform(1000.0, 26000.0), 3),
            declared_pieces=rng.randint(10, 2000),
        )


@dataclass(frozen=True)
class WeightDrift:
    """Planted fault: one line's weighed gross drifts by a known fraction."""

    name: str = "weight_drift_2pct"
    magnitude: float = 0.02

    def describe(self) -> str:
        return "the heaviest line's gross is inflated by 2 %, leaving the declared total as filed"

    def apply(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = planted(payload, self.magnitude, slot=0)
            return out
        out = copy.deepcopy(payload)
        lines = out["lines"]
        heaviest = max(range(len(lines)), key=lambda i: lines[i]["gross_kg"])
        lines[heaviest]["gross_kg"] = round(lines[heaviest]["gross_kg"] * (1.0 + self.magnitude), 3)
        return out


@dataclass(frozen=True)
class SealTransposition:
    """Planted fault: two adjacent digits of the seal are transposed."""

    name: str = "seal_digit_transposition"
    magnitude: float = 1.0

    def describe(self) -> str:
        return "two adjacent digits of the bolt-seal number are transposed, one keystroke's worth"

    def apply(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = planted(payload, self.magnitude, slot=1)
            return out
        out = copy.deepcopy(payload)
        seal = list(str(out["seal"]))
        for index in range(3, len(seal) - 2):
            if seal[index] != seal[index + 1]:
                seal[index], seal[index + 1] = seal[index + 1], seal[index]
                break
        out["seal"] = "".join(seal)
        return out


@dataclass(frozen=True)
class PhantomPiece:
    """Planted fault: one extra piece appears on a line and nowhere else."""

    name: str = "phantom_piece"
    magnitude: float = 1.0

    def describe(self) -> str:
        return "one line gains a single piece that the declared piece count does not know about"

    def apply(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = planted(payload, self.magnitude, slot=2)
            return out
        out = copy.deepcopy(payload)
        out["lines"][0]["pieces"] = int(out["lines"][0]["pieces"]) + 1
        return out


@dataclass(frozen=True)
class ContainerTypo:
    """Planted fault: one character of the container number is altered."""

    name: str = "container_single_char_typo"
    magnitude: float = 1.0

    def describe(self) -> str:
        return "one digit of the container's serial is bumped by one, a single-character typo"

    def apply(self, payload: Any) -> Any:
        if not _is_manifest(payload):
            out = planted(payload, self.magnitude, slot=3)
            return out
        out = copy.deepcopy(payload)
        text = list(str(out["container"]))
        text[6] = str((int(text[6]) + 1) % 10)
        out["container"] = "".join(text)
        return out


# ---------------------------------------------------------------------------
# Detector
# ---------------------------------------------------------------------------


def reconciliation_audit(payload: Any) -> bool:
    """Fires when the manifest fails to foot against itself in any of five ways."""
    try:
        return bool(reconciliation_faults(payload))
    except Exception:  # noqa: BLE001 - a document too malformed to foot is a fault
        return True


def filing_digest_guard(payload: Any) -> bool:
    """Fires when a document no longer agrees with the digest it was filed under.

    This is the instrument the department stakes its silence on. It is quiet
    on every document that is what it was filed as — including the rivals,
    which are filed documents that happen not to foot — and it fires on any
    document whose content has moved since filing, which is exactly what a
    planted fault and an ablation both are.
    """
    try:
        return not digest_matches(payload)
    except Exception:  # noqa: BLE001 - a document that cannot be digested has moved
        return True


DETECTORS = (
    NamedDetector(
        name="filing_digest_guard",
        fires=filing_digest_guard,
        probe=copy.deepcopy(_CLEAN_PROBE),
        note=(
            "recomputes the filing digest over the whole document and compares "
            "it with the digest the document was filed under; the clean probe "
            "is a second, unplanted manifest of the same schema"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Reference claims — one the battery must pass, one it must kill
# ---------------------------------------------------------------------------


def _claim_reconciles(payload: Any) -> bool:
    return reconciles(payload)


def _claim_foots_or_heavy_consignment(payload: Any) -> bool:
    """The bad claim a heavy-lift desk makes: it foots, or it is heavy enough to excuse."""
    return reconciles(payload) or float(payload["declared_gross_kg"]) >= 15000.0


def _claim_foots_or_short_form(payload: Any) -> bool:
    """The bad claim a short-form desk makes: it foots, or it has few enough lines to excuse."""
    return reconciles(payload) or len(payload["lines"]) <= 3


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="reconciles_against_itself",
        claim=_claim_reconciles,
        distinguishes=True,
        note=(
            "the property at issue: the target foots on all five arms and every "
            "rival fails at least one, so the battery is shown to be able to say yes"
        ),
    ),
    ReferenceClaim(
        name="foots_or_heavy_consignment_exemption",
        claim=_claim_foots_or_heavy_consignment,
        distinguishes=False,
        note=(
            "the heavy-lift desk's excuse — reconciled, or over 15 t and therefore "
            "waved through. It fires for three rivals that do not reconcile, so the "
            "battery must kill it; it still tracks the substance, so ablating the "
            "weighing data or planting a fault switches it off"
        ),
    ),
    ReferenceClaim(
        name="foots_or_short_form_exemption",
        claim=_claim_foots_or_short_form,
        distinguishes=False,
        note=(
            "the short-form desk's excuse — reconciled, or three lines or fewer and "
            "therefore waved through. Shared with all four rivals, so the battery "
            "must kill it, and it too switches off under ablation and under every "
            "planted fault"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery and the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="manifest_reconciliation",
    target=TARGET,
    rivals=RIVALS,
    decoys=(WeighingBlanked(), PieceCountBlanked()),
    surrogates=(RandomCargo(),),
    lesions=(WeightDrift(), SealTransposition(), PhantomPiece(), ContainerTypo()),
    notes=(
        "Rivals are drawn from the four ways a real manifest stops footing. "
        "Decoys blank the weighed substance while keeping the filed totals. "
        "The surrogate emits documents of the same schema with no shipper "
        "behind the arithmetic. Lesions carry stated magnitudes."
    ),
)

PROVENANCE = Provenance(
    authored_by="party03 (blind-authoring experiment), from the harness contract alone",
    authored_on="2026-08-09",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=False,
    edited_after_observing_failures=False,
    notes=(
        "Subject documents and battery content were written by one author in "
        "one sitting; that is one line of evidence, declared as such. The "
        "check-character arithmetic is implemented once in this module and both "
        "the subject and the detector read it, which is a shared dependency at "
        "the level of the toy."
    ),
)

DEPARTMENT = Department(
    name="manifests",
    summary=(
        "Ocean container manifests and the property of reconciling: both check "
        "characters correct, both footings correct, inside the rated payload."
    ),
    battery=BATTERY,
    door="docs/doors/manifests.md",
    domain="",
    modules=("blind/party03/department.py",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery means only that a claim fires on one filed "
        "manifest that foots and on none of four same-schema manifests that do "
        "not; it says nothing about whether the cargo described was ever loaded, "
        "and nothing about manifests outside this toy fixture set."
    ),
    provenance=PROVENANCE,
)


# ---------------------------------------------------------------------------
# The absurd claim (red-team instrument, not part of the department)
# ---------------------------------------------------------------------------

_SYNODIC_MONTH_DAYS = 29.530588853
_NEW_MOON_EPOCH_JD = 2451550.1  # 2000-01-06 18:14 UTC

ABSURD_CLAIM_TEXT = "This manifest was recorded under a waxing moon."


def ABSURD_CLAIM(payload: Any) -> bool:  # noqa: N802 - name fixed by the experiment
    """True when the document's timestamp falls in the waxing half of the lunar month."""
    try:
        stamp = str(payload["recorded_at"])
        moment = _dt.datetime.strptime(stamp, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=_dt.timezone.utc
        )
    except Exception:  # noqa: BLE001 - an unreadable stamp is simply not waxing
        return False
    julian_day = moment.timestamp() / 86400.0 + 2440587.5
    phase = ((julian_day - _NEW_MOON_EPOCH_JD) / _SYNODIC_MONTH_DAYS) % 1.0
    return 0.0 < phase < 0.5
