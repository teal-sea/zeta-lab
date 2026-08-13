"""``telemetry.reconcile`` — where the run record and git disagree.

The archaeology found this repository has strong provenance at the head
(decisions in prose) and at the tail (claim, grade, commit) and nothing joining
them. This module checks the join it now has, and reports **every** way it can
be broken rather than a single verdict.

There is deliberately no aggregate and no score. ``findings`` is a tuple of
sentences a reader can dispute — the same output shape
``harness/independence.py`` and ``harness/protocol.py`` chose, for the same
reason: a boolean here would be read as "provenance is fine".

Severities are advice about reading order, not authority:

``defect``   the record and the repository contradict each other.
``gap``      something was never captured. Common, and not an error by itself.
``note``     legal and worth seeing — a run that produced three commits, say.

One caution that matters in this repository: this clone may be **shallow**, and
`git` cannot distinguish "this commit does not exist" from "this commit is not
in my clone". Findings that depend on commit lookup say ``in this checkout``
and mean it.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from telemetry import gitlink, prompts
from telemetry.registry import corrupt_lines, iter_runs
from telemetry.schema import TERMINAL_STATUSES

__all__ = ["Finding", "FINDING_KINDS", "reconcile", "render_text"]

#: Closed vocabulary. A reconciliation that could invent a category would be
#: unable to say it found nothing new.
FINDING_KINDS: tuple[str, ...] = (
    "corrupt_record",
    "unfoldable_run",
    "duplicate_run_id",
    "interrupted_run",
    "run_without_commit",
    "missing_commit",
    "orphan_commit",
    "commit_mismatch",
    "untrailered_commit",
    "multi_commit_run",
    "prompt_unrecoverable",
    "prompt_local_only",
    "prompt_absent",
)


@dataclass(frozen=True)
class Finding:
    kind: str
    severity: str
    detail: str
    run_id: str | None = None
    commit: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "severity": self.severity,
            "detail": self.detail,
            "run_id": self.run_id,
            "commit": self.commit,
        }


def reconcile(
    root: Path | str,
    repo: Path | str,
    *,
    rev_range: str | None = None,
    limit: int | None = 200,
    require_trailer_since: str | None = None,
) -> tuple[Finding, ...]:
    """Compare the run registry against the repository.

    ``require_trailer_since`` opts into the ``untrailered_commit`` check for a
    range. It is **off by default and must stay that way**: every commit made
    before this system existed has no trailer, and reporting all of them as
    defects would bury the findings that matter. Grandfathered work is not a
    defect.
    """
    findings: list[Finding] = []

    runs: dict[str, Any] = {}
    for run_id, run, error in iter_runs(root):
        for number, reason in corrupt_lines(root, run_id):
            findings.append(
                Finding(
                    "corrupt_record",
                    "defect",
                    f"line {number} of run {run_id} will not parse: {reason}",
                    run_id=run_id,
                )
            )
        if run is None:
            findings.append(
                Finding("unfoldable_run", "defect", f"run {run_id}: {error}", run_id=run_id)
            )
            continue
        if run.run_id != run_id:
            findings.append(
                Finding(
                    "duplicate_run_id",
                    "defect",
                    f"file {run_id}.jsonl carries events for run {run.run_id}",
                    run_id=run_id,
                )
            )
        runs[run.run_id] = run

    commits = gitlink.commit_run_ids(repo, rev_range, limit=limit)

    #: run_id -> commits that declare it
    declared: dict[str, list[str]] = {}
    for sha, info in commits.items():
        for run_id in info["run_ids"]:  # type: ignore[index]
            declared.setdefault(run_id, []).append(sha)

    for run_id, shas in sorted(declared.items()):
        if run_id not in runs:
            findings.append(
                Finding(
                    "orphan_commit",
                    "defect",
                    f"commit {shas[0][:12]} declares Run-Id {run_id}, which has no "
                    f"record in this registry",
                    run_id=run_id,
                    commit=shas[0],
                )
            )
        elif len(shas) > 1:
            findings.append(
                Finding(
                    "multi_commit_run",
                    "note",
                    f"run {run_id} produced {len(shas)} commits "
                    f"({', '.join(s[:8] for s in shas)}) — legal, recorded so it is "
                    f"not read as a duplicate",
                    run_id=run_id,
                )
            )

    for run_id, run in sorted(runs.items()):
        if run.status == "interrupted":
            findings.append(
                Finding(
                    "interrupted_run",
                    "gap",
                    f"run {run_id} started {run.started_at} and never recorded a "
                    f"finish; its outcome, duration and artifacts are unknown and "
                    f"stay unknown",
                    run_id=run_id,
                )
            )

        for sha in run.commits:
            if not gitlink.commit_exists(repo, sha):
                findings.append(
                    Finding(
                        "missing_commit",
                        "defect",
                        f"run {run_id} records commit {sha[:12]}, absent from this "
                        f"checkout (note: a shallow clone can produce this without "
                        f"the commit being lost)",
                        run_id=run_id,
                        commit=sha,
                    )
                )
                continue
            full = gitlink.resolve_commit(repo, sha) or sha
            info = commits.get(full)
            if info is None:
                continue  # outside the scanned range; not a disagreement
            if run_id not in info["run_ids"]:  # type: ignore[index]
                findings.append(
                    Finding(
                        "commit_mismatch",
                        "defect",
                        f"run {run_id} claims commit {sha[:12]}, but that commit's "
                        f"Run-Id trailer says {list(info['run_ids']) or 'nothing'}",
                        run_id=run_id,
                        commit=sha,
                    )
                )

        if run.status in TERMINAL_STATUSES and not run.commits and not declared.get(run_id):
            severity = "note" if run.outcome == "no-change" else "gap"
            findings.append(
                Finding(
                    "run_without_commit",
                    severity,
                    f"run {run_id} finished {run.status}"
                    + (f"/{run.outcome}" if run.outcome else "")
                    + " with no commit recorded and none declaring it"
                    + (
                        " — consistent with its stated outcome"
                        if run.outcome == "no-change"
                        else ""
                    ),
                    run_id=run_id,
                )
            )

        ref = prompts.PromptRef.from_dict(run.prompt or {})
        if run.prompt is None or ref.store == "absent":
            findings.append(
                Finding(
                    "prompt_absent",
                    "gap",
                    f"run {run_id} captured no prompt; what this run was asked is "
                    f"not recoverable",
                    run_id=run_id,
                )
            )
        elif prompts.missing_locally(root, ref):
            findings.append(
                Finding(
                    "prompt_local_only",
                    "gap",
                    f"run {run_id}: prompt {ref.digest[:12]}… is referenced but its "
                    f"text is not in this checkout's store — expected on any fresh "
                    f"clone, since the store is gitignored by design. The digest "
                    f"still verifies for whoever holds the text",
                    run_id=run_id,
                )
            )
        else:
            for reason in prompts.verify_reasons(root, ref):
                findings.append(
                    Finding("prompt_unrecoverable", "defect", f"run {run_id}: {reason}",
                            run_id=run_id)
                )

    if require_trailer_since:
        scoped = gitlink.commit_run_ids(
            repo, f"{require_trailer_since}..HEAD", limit=limit
        )
        for sha, info in sorted(scoped.items()):
            if not info["run_ids"]:  # type: ignore[index]
                findings.append(
                    Finding(
                        "untrailered_commit",
                        "gap",
                        f"commit {sha[:12]} ({info['subject']}) carries no Run-Id "
                        f"trailer",
                        commit=sha,
                    )
                )

    order = {"defect": 0, "gap": 1, "note": 2}
    return tuple(sorted(findings, key=lambda f: (order.get(f.severity, 9), f.kind)))


def render_text(findings: tuple[Finding, ...]) -> str:
    """A plain report. Prints the empty case explicitly rather than nothing."""
    if not findings:
        return "reconciliation: no findings (0 defects, 0 gaps, 0 notes)\n"
    lines = []
    counts = {"defect": 0, "gap": 0, "note": 0}
    for finding in findings:
        counts[finding.severity] = counts.get(finding.severity, 0) + 1
    lines.append(
        f"reconciliation: {counts.get('defect', 0)} defect(s), "
        f"{counts.get('gap', 0)} gap(s), {counts.get('note', 0)} note(s)"
    )
    for finding in findings:
        lines.append(f"  [{finding.severity}] {finding.kind}: {finding.detail}")
    return "\n".join(lines) + "\n"
