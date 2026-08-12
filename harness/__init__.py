"""``harness`` — the falsification protocol, with no subject matter in it.

The laboratory's referee, factored out of the laboratory. :mod:`ontology`
answers *where does a lead come from and what may be concluded about it*;
this package answers the prior question, the one that decides whether a
department is a department at all:

    **What could show this claim is not about its subject?**

Four instrument roles are defined in :mod:`harness.protocol`, abstracted from
the four that the laboratory already runs by hand — a rival that shares the
claimed structure but lacks the target property, a decoy that replaces the
substantive input, a surrogate that reproduces the observation from no
substantive input at all, and a lesion that plants a violation so a detector's
power can be measured rather than assumed. A :class:`~harness.protocol.Battery`
bundles them; a :class:`~harness.protocol.Department` is a domain plus the
battery entitled to kill its claims plus the door a reader comes in through.

The admission rule is the repository's honest-scope rule turned into
architecture: **no department without a battery**. A body of work whose claims
nothing in the tree can falsify is not a department, it is a probe, and it
belongs in ``probes/`` where nobody will mistake it for a result.

Everything in this package is domain-agnostic in the strict sense already
established by :mod:`ontology.schema`: it imports nothing from any laboratory
package, names no quantity any laboratory computes, and would work unchanged
for a chemistry lab or a compiler-optimisation search. The seam is enforced by
``tests/test_harness_protocol.py`` the same three ways — an AST import scan, a
clean-interpreter ``sys.modules`` check, and a lexical scan of the source.
Subject matter lives in ``harness/departments/``.
"""

from __future__ import annotations

from harness.protocol import (
    AblationVerdict,
    Battery,
    BatteryError,
    BatteryVerdict,
    ClaimOutcome,
    Decoy,
    Department,
    DepartmentError,
    DetectorVerdict,
    HarnessError,
    Lesion,
    NamedDetector,
    NullBandVerdict,
    NullVerdict,
    PowerVerdict,
    ReferenceClaim,
    Subject,
    Surrogate,
    battery_reasons,
    clear_departments,
    department_reasons,
    get_department,
    list_departments,
    register_department,
    run_ablation,
    run_battery,
    run_detector,
    run_null_band,
    run_nulls,
    run_power,
    unregister_department,
    validate_battery,
    validate_department,
)
from harness.independence import (
    IndependenceError,
    IndependenceReport,
    VerificationPath,
    agreement_bounds,
    compare,
)
from harness.provenance import (
    Provenance,
    contamination_reasons,
    dependence_reasons,
    undeclared_fields,
)

__all__ = [
    "AblationVerdict",
    "Battery",
    "BatteryError",
    "BatteryVerdict",
    "ClaimOutcome",
    "Decoy",
    "Department",
    "DepartmentError",
    "DetectorVerdict",
    "HarnessError",
    "IndependenceError",
    "IndependenceReport",
    "Lesion",
    "NamedDetector",
    "NullBandVerdict",
    "NullVerdict",
    "PowerVerdict",
    "Provenance",
    "ReferenceClaim",
    "Subject",
    "Surrogate",
    "VerificationPath",
    "agreement_bounds",
    "battery_reasons",
    "clear_departments",
    "compare",
    "contamination_reasons",
    "department_reasons",
    "dependence_reasons",
    "get_department",
    "list_departments",
    "register_department",
    "run_ablation",
    "run_battery",
    "run_detector",
    "run_null_band",
    "run_nulls",
    "run_power",
    "undeclared_fields",
    "unregister_department",
    "validate_battery",
    "validate_department",
]
