"""Tests for ``telemetry/`` — the run registry.

Every test runs against a ``tmp_path`` root and, where git is needed, against a
throwaway repository created inside ``tmp_path``. **Nothing here reads or
writes the live registry, another worktree, a shared cache, or any research
artifact**, which is a requirement of the isolation contract this package was
built under (``telemetry/PREFLIGHT-2026-08-13.md``) and not merely tidiness:
these tests were written while two frontier research sessions were live.

The suite is stdlib + pytest only. It must pass in a checkout with none of the
laboratory's numerical dependencies installed, because the moment telemetry
needs `mpmath` to run is the moment it stops running.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from telemetry import gitlink, prompts  # noqa: E402
from telemetry.cli import main as cli_main  # noqa: E402
from telemetry.reconcile import reconcile  # noqa: E402
from telemetry.registry import (  # noqa: E402
    ENV_ALLOWLIST,
    ENV_DENIED,
    append_event,
    corrupt_lines,
    iter_runs,
    list_run_ids,
    new_run_id,
    probe_context,
    read_run,
    run_path,
    utc_now,
)
from telemetry.schema import (  # noqa: E402
    OUTCOMES,
    STATUSES,
    Event,
    TelemetryError,
    event_reasons,
    fold,
    run_reasons,
    validate_event,
)

RID = "11111111-2222-4333-8444-555555555555"
RID2 = "99999999-8888-4777-8666-555555555555"


def started(run_id: str = RID, at: str = "2026-08-13T10:00:00Z", **payload) -> Event:
    body = {"capture": "contemporaneous", "task": "t"}
    body.update(payload)
    return Event(kind="run_started", run_id=run_id, at=at, payload=body)


def finished(run_id: str = RID, at: str = "2026-08-13T10:05:00Z", **payload) -> Event:
    body = {"status": "completed"}
    body.update(payload)
    return Event(kind="run_finished", run_id=run_id, at=at, payload=body)


# ---------------------------------------------------------------------------
# schema validity
# ---------------------------------------------------------------------------


def test_a_well_formed_start_event_validates() -> None:
    assert event_reasons(started()) == ()


@pytest.mark.parametrize(
    "kwargs,fragment",
    [
        ({"kind": "run_exploded"}, "not one of"),
        ({"run_id": "not-a-uuid"}, "not a lowercase UUID"),
        ({"at": "yesterday"}, "not an ISO-8601"),
        ({"at": "2026-08-13T10:00:00"}, "not an ISO-8601"),  # no offset
    ],
)
def test_malformed_events_are_refused_with_a_reason(kwargs, fragment) -> None:
    event = started()
    event = Event(
        kind=kwargs.get("kind", event.kind),
        run_id=kwargs.get("run_id", event.run_id),
        at=kwargs.get("at", event.at),
        payload=event.payload,
    )
    reasons = event_reasons(event)
    assert any(fragment in r for r in reasons), reasons
    with pytest.raises(TelemetryError):
        validate_event(event)


def test_every_violation_is_reported_at_once_not_one_at_a_time() -> None:
    """House style: three problems must not need three runs to find."""
    bad = Event(kind="nope", run_id="x", at="y", payload={})
    assert len(event_reasons(bad)) >= 3


def test_a_finish_event_cannot_assert_a_non_terminal_status() -> None:
    reasons = event_reasons(finished(status="running"))
    assert any("status" in r for r in reasons)
    reasons = event_reasons(finished(status="interrupted"))
    assert any("status" in r for r in reasons)


def test_an_unknown_outcome_is_refused() -> None:
    assert any("outcome" in r for r in event_reasons(finished(outcome="great")))
    for outcome in OUTCOMES:
        assert event_reasons(finished(outcome=outcome)) == ()


# ---------------------------------------------------------------------------
# the honesty rules
# ---------------------------------------------------------------------------


def test_a_model_without_a_source_is_refused() -> None:
    """A model identity with no stated origin is indistinguishable from a guess."""
    reasons = event_reasons(started(model="claude-opus-5"))
    assert any("model_source" in r for r in reasons)
    assert event_reasons(started(model="claude-opus-5", model_source="declared-by-operator")) == ()


def test_an_estimated_cost_without_a_basis_is_refused() -> None:
    reasons = event_reasons(finished(cost={"estimated_usd": 1.23}))
    assert any("estimate_basis" in r for r in reasons)
    assert finished(cost={"estimated_usd": 1.23, "estimate_basis": "list price x tokens"})
    assert event_reasons(
        finished(cost={"estimated_usd": 1.23, "estimate_basis": "list price x tokens"})
    ) == ()


def test_a_provider_reported_cost_needs_no_basis() -> None:
    assert event_reasons(finished(cost={"provider_usd": 0.42})) == ()


def test_reconstructed_capture_must_cite_its_source() -> None:
    reasons = event_reasons(started(capture="reconstructed"))
    assert any("reconstructed_from" in r for r in reasons)
    assert event_reasons(
        started(capture="reconstructed", reconstructed_from="git log 32e4428..HEAD")
    ) == ()


def test_reconstructed_and_contemporaneous_do_not_render_alike(tmp_path: Path) -> None:
    append_event(tmp_path, started(RID, capture="contemporaneous"))
    append_event(
        tmp_path,
        started(RID2, capture="reconstructed", reconstructed_from="commit messages"),
    )
    a, b = read_run(tmp_path, RID), read_run(tmp_path, RID2)
    assert a.capture == "contemporaneous" and a.reconstructed_from is None
    assert b.capture == "reconstructed" and b.reconstructed_from == "commit messages"
    assert a.as_dict()["capture"] != b.as_dict()["capture"]


# ---------------------------------------------------------------------------
# unknown stays unknown
# ---------------------------------------------------------------------------


def test_missing_optional_telemetry_is_null_and_named_not_defaulted(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    append_event(tmp_path, finished())
    run = read_run(tmp_path, RID)
    for field in (
        "input_tokens", "output_tokens", "cache_read_tokens", "cache_write_tokens",
        "provider_usd", "estimated_usd", "model",
    ):
        assert getattr(run, field) is None, f"{field} was invented"
    unknown = run.unknown_fields()
    assert "input_tokens" in unknown and "provider_usd" in unknown and "model" in unknown
    # and the holes travel with the record, so a reader cannot miss them
    assert set(unknown) <= set(run.as_dict()["unknown_fields"])


def test_zero_tokens_and_absent_tokens_are_different(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    append_event(tmp_path, finished(tokens={"input": 0, "output": 0}))
    run = read_run(tmp_path, RID)
    assert run.input_tokens == 0
    assert "input_tokens" not in run.unknown_fields()


def test_probe_context_never_returns_a_model() -> None:
    """Measured, not assumed: this environment exports no model identifier."""
    assert "model" not in probe_context(None)
    assert "model_id" not in probe_context(None)


def test_the_environment_allowlist_excludes_every_denied_name() -> None:
    assert set(ENV_ALLOWLIST).isdisjoint(set(ENV_DENIED))
    for name in ("CLAUDE_CODE_USER_EMAIL", "GH_TOKEN", "ANTHROPIC_API_KEY"):
        assert name in ENV_DENIED


def test_captured_env_is_allowlisted_so_a_new_secret_cannot_leak_by_default(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("CLAUDE_CODE_USER_EMAIL", "someone@example.com")
    monkeypatch.setenv("A_BRAND_NEW_SECRET", "hunter2")
    monkeypatch.setenv("CLAUDE_CODE_VERSION", "9.9.9")
    env = probe_context(None).get("env", {})
    assert env.get("CLAUDE_CODE_VERSION") == "9.9.9"
    assert "CLAUDE_CODE_USER_EMAIL" not in env
    assert "A_BRAND_NEW_SECRET" not in env


# ---------------------------------------------------------------------------
# append-only behaviour, ids, multiple runs
# ---------------------------------------------------------------------------


def test_appending_never_rewrites_earlier_lines(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    first = run_path(tmp_path, RID).read_text()
    append_event(tmp_path, Event("run_note", RID, "2026-08-13T10:01:00Z", {"note": "n"}))
    append_event(tmp_path, finished())
    text = run_path(tmp_path, RID).read_text()
    assert text.startswith(first)
    assert len(text.splitlines()) == 3


def test_a_run_id_is_claimed_once(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    with pytest.raises(TelemetryError, match="already has a run_started"):
        append_event(tmp_path, started())


def test_new_run_ids_are_unique() -> None:
    ids = {new_run_id() for _ in range(2000)}
    assert len(ids) == 2000


def test_one_file_per_run_so_concurrent_sessions_cannot_collide(tmp_path: Path) -> None:
    for rid in (RID, RID2):
        append_event(tmp_path, started(rid))
    assert sorted(list_run_ids(tmp_path)) == sorted([RID, RID2])
    assert run_path(tmp_path, RID) != run_path(tmp_path, RID2)


def test_multiple_runs_fold_independently(tmp_path: Path) -> None:
    append_event(tmp_path, started(RID))
    append_event(tmp_path, finished(RID, outcome="landed"))
    append_event(tmp_path, started(RID2))
    runs = {rid: run for rid, run, _ in iter_runs(tmp_path)}
    assert runs[RID].status == "completed" and runs[RID].outcome == "landed"
    assert runs[RID2].status == "interrupted"


# ---------------------------------------------------------------------------
# timestamps, duration, interrupted and failed runs
# ---------------------------------------------------------------------------


def test_duration_is_measured_from_two_recorded_instants(tmp_path: Path) -> None:
    append_event(tmp_path, started(at="2026-08-13T10:00:00Z"))
    append_event(tmp_path, finished(at="2026-08-13T10:05:30Z"))
    assert read_run(tmp_path, RID).duration_seconds == pytest.approx(330.0)


def test_an_explicit_duration_wins_over_the_derived_one(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    append_event(tmp_path, finished(duration_seconds=12.5))
    assert read_run(tmp_path, RID).duration_seconds == 12.5


def test_a_run_with_no_finish_is_interrupted_not_completed(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    run = read_run(tmp_path, RID)
    assert run.status == "interrupted"
    assert run.finished_at is None
    assert run.duration_seconds is None  # not guessed from "now"
    assert run.outcome is None


def test_a_failed_run_keeps_its_error_and_exit_code(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    append_event(
        tmp_path,
        finished(status="failed", outcome="crashed", exit_code=127,
                 error={"kind": "OSError", "message": "boom"}),
    )
    run = read_run(tmp_path, RID)
    assert run.status == "failed" and run.exit_code == 127
    assert run.error["message"] == "boom"


def test_a_folded_run_that_contradicts_itself_is_reported() -> None:
    from telemetry.schema import Run

    run = Run(run_id=RID, started_at="2026-08-13T10:00:00Z",
              capture="contemporaneous", status="completed")
    assert any("finished_at" in r for r in run_reasons(run))


def test_every_status_is_reachable_or_declared() -> None:
    assert set(STATUSES) == {"running", "completed", "failed", "interrupted", "aborted"}


# ---------------------------------------------------------------------------
# corrupt records
# ---------------------------------------------------------------------------


def test_a_corrupt_line_is_surfaced_and_does_not_hide_the_others(tmp_path: Path) -> None:
    append_event(tmp_path, started())
    with run_path(tmp_path, RID).open("a", encoding="utf-8") as handle:
        handle.write("{not json at all\n")
    append_event(tmp_path, finished())
    assert read_run(tmp_path, RID).status == "completed"
    bad = corrupt_lines(tmp_path, RID)
    assert len(bad) == 1 and bad[0][0] == 2


def test_a_file_with_no_start_event_is_unfoldable_not_silently_empty(tmp_path: Path) -> None:
    path = run_path(tmp_path, RID)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(finished().as_dict()) + "\n", encoding="utf-8")
    with pytest.raises(TelemetryError, match="no run_started"):
        read_run(tmp_path, RID)
    # and iteration reports it rather than dying on it
    assert [(r, e is not None) for r, _, e in iter_runs(tmp_path)] == [(RID, True)]


def test_folding_an_empty_list_is_refused() -> None:
    with pytest.raises(TelemetryError):
        fold([])


# ---------------------------------------------------------------------------
# prompt provenance
# ---------------------------------------------------------------------------


def test_a_captured_prompt_is_recoverable_and_verifiable(tmp_path: Path) -> None:
    ref = prompts.capture_text(tmp_path, "do the thing", source="operator")
    assert prompts.verify_reasons(tmp_path, ref) == ()
    path = prompts.resolve(tmp_path, ref)
    assert path is not None and path.read_text() == "do the thing"


def test_prompt_storage_is_content_addressed_and_idempotent(tmp_path: Path) -> None:
    a = prompts.capture_text(tmp_path, "same text")
    b = prompts.capture_text(tmp_path, "same text")
    assert a.digest == b.digest
    assert len(list(prompts.prompts_dir(tmp_path).glob("*.txt"))) == 1


def test_a_tampered_prompt_store_is_detected(tmp_path: Path) -> None:
    ref = prompts.capture_text(tmp_path, "original")
    prompts.resolve(tmp_path, ref).write_text("substituted", encoding="utf-8")
    reasons = prompts.verify_reasons(tmp_path, ref)
    assert any("not the text that ran" in r for r in reasons)


def test_a_missing_prompt_store_entry_is_reported_as_unrecoverable(tmp_path: Path) -> None:
    ref = prompts.capture_text(tmp_path, "gone")
    prompts.resolve(tmp_path, ref).unlink()
    assert any("unrecoverable" in r for r in prompts.verify_reasons(tmp_path, ref))


def test_an_external_prompt_needs_a_reference_but_not_local_text(tmp_path: Path) -> None:
    ref = prompts.reference_external("a" * 64, "vault://2026-08-13/brief.md")
    assert prompts.verify_reasons(tmp_path, ref) == ()
    bad = prompts.PromptRef(digest="a" * 64, store="external", ref=None)
    assert any("unfindable" in r for r in prompts.verify_reasons(tmp_path, bad))


def test_an_absent_prompt_is_a_stated_limitation_not_a_defect(tmp_path: Path) -> None:
    assert prompts.verify_reasons(tmp_path, prompts.PromptRef(None, "absent")) == ()


# ---------------------------------------------------------------------------
# git trailer parsing
# ---------------------------------------------------------------------------


def test_the_trailer_round_trips() -> None:
    assert gitlink.parse_run_ids(f"subject\n\n{gitlink.format_trailer(RID)}\n") == (RID,)


def test_trailer_parsing_is_case_insensitive_and_deduplicates() -> None:
    message = f"s\n\nRun-Id: {RID.upper()}\nRun-Id: {RID}\n"
    assert gitlink.parse_run_ids(message) == (RID,)


def test_a_commit_may_declare_two_runs() -> None:
    message = f"s\n\nRun-Id: {RID}\nRun-Id: {RID2}\n"
    assert gitlink.parse_run_ids(message) == (RID, RID2)


def test_a_run_id_mentioned_in_prose_is_not_a_trailer() -> None:
    assert gitlink.parse_run_ids(f"we discussed run {RID} at length") == ()
    assert gitlink.parse_run_ids(f"  Run-Id: {RID} trailing words") == ()


def test_no_trailer_is_empty_not_an_error() -> None:
    assert gitlink.parse_run_ids("plain subject\n\nbody\n") == ()
    assert gitlink.parse_run_ids("") == ()


def test_the_pre_existing_trailers_are_read_as_corroboration() -> None:
    message = (
        "s\n\nCo-Authored-By: Claude Opus 5 <noreply@anthropic.com>\n"
        "Claude-Session: https://claude.ai/code/session_01ABC\n"
        f"Run-Id: {RID}\n"
    )
    corroborating = gitlink.parse_corroborating(message)
    assert corroborating["co_authored_by"] == ("Claude Opus 5 <noreply@anthropic.com>",)
    assert corroborating["claude_session"] == ("https://claude.ai/code/session_01ABC",)
    assert gitlink.parse_run_ids(message) == (RID,)


# ---------------------------------------------------------------------------
# reconciliation, against a real throwaway repository
# ---------------------------------------------------------------------------


@pytest.fixture()
def repo(tmp_path: Path) -> Path:
    """A throwaway git repository. Never the live one."""
    path = tmp_path / "repo"
    path.mkdir()
    run = lambda *a: subprocess.run(  # noqa: E731
        ["git", *a], cwd=path, check=True, capture_output=True, text=True
    )
    run("init", "-q", "-b", "trunk")
    run("config", "user.email", "t@example.com")
    run("config", "user.name", "T")
    (path / "seed.txt").write_text("seed\n")
    run("add", "-A")
    run("commit", "-q", "-m", "seed")
    return path


def commit(repo: Path, name: str, message: str) -> str:
    (repo / name).write_text(name + "\n")
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True, capture_output=True)
    subprocess.run(["git", "commit", "-q", "-m", message], cwd=repo, check=True,
                   capture_output=True)
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                          capture_output=True, text=True).stdout.strip()


def kinds(findings) -> set[str]:
    return {f.kind for f in findings}


def test_a_clean_run_and_commit_reconcile_with_no_findings(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    sha = commit(repo, "a.txt", f"work\n\n{gitlink.format_trailer(RID)}")
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    append_event(root, finished(commits=[sha]))
    assert reconcile(root, repo) == ()


def test_a_commit_claiming_a_nonexistent_run_is_an_orphan(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    commit(repo, "a.txt", f"work\n\n{gitlink.format_trailer(RID)}")
    findings = reconcile(root, repo)
    assert "orphan_commit" in kinds(findings)
    assert all(f.severity == "defect" for f in findings if f.kind == "orphan_commit")


def test_a_run_claiming_a_commit_this_checkout_lacks_is_reported(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    append_event(root, finished(commits=["0" * 40]))
    findings = reconcile(root, repo)
    assert "missing_commit" in kinds(findings)


def test_a_run_and_a_commit_that_name_different_runs_is_a_mismatch(
    tmp_path: Path, repo: Path
) -> None:
    root = tmp_path / "tel"
    sha = commit(repo, "a.txt", f"work\n\n{gitlink.format_trailer(RID2)}")
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    append_event(root, finished(commits=[sha]))
    assert "commit_mismatch" in kinds(reconcile(root, repo))


def test_one_run_producing_several_commits_is_a_note_not_a_defect(
    tmp_path: Path, repo: Path
) -> None:
    root = tmp_path / "tel"
    a = commit(repo, "a.txt", f"first\n\n{gitlink.format_trailer(RID)}")
    b = commit(repo, "b.txt", f"second\n\n{gitlink.format_trailer(RID)}")
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    append_event(root, finished(commits=[a, b]))
    findings = reconcile(root, repo)
    assert "multi_commit_run" in kinds(findings)
    assert not [f for f in findings if f.severity == "defect"]


def test_an_interrupted_run_is_reported_as_a_gap(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    findings = reconcile(root, repo)
    interrupted = [f for f in findings if f.kind == "interrupted_run"]
    assert interrupted and interrupted[0].severity == "gap"


def test_a_finished_run_with_no_commit_is_a_gap_unless_it_said_no_change(
    tmp_path: Path, repo: Path
) -> None:
    root = tmp_path / "tel"
    append_event(root, started(RID, prompt=prompts.capture_text(root, "p").as_dict()))
    append_event(root, finished(RID, outcome="landed"))
    append_event(root, started(RID2, prompt=prompts.capture_text(root, "q").as_dict()))
    append_event(root, finished(RID2, outcome="no-change"))
    by_run = {f.run_id: f for f in reconcile(root, repo) if f.kind == "run_without_commit"}
    assert by_run[RID].severity == "gap"
    assert by_run[RID2].severity == "note"


def test_a_run_with_no_prompt_is_reported_as_a_gap(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    append_event(root, started())
    append_event(root, finished(outcome="no-change"))
    assert "prompt_absent" in kinds(reconcile(root, repo))


def test_a_tampered_prompt_shows_up_in_reconciliation(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    ref = prompts.capture_text(root, "original")
    append_event(root, started(prompt=ref.as_dict()))
    append_event(root, finished(outcome="no-change"))
    prompts.resolve(root, ref).write_text("swapped", encoding="utf-8")
    findings = reconcile(root, repo)
    assert "prompt_unrecoverable" in kinds(findings)
    assert any(f.severity == "defect" for f in findings if f.kind == "prompt_unrecoverable")


def test_grandfathered_commits_are_not_defects_by_default(tmp_path: Path, repo: Path) -> None:
    """Work that predates instrumentation must not drown the real findings."""
    root = tmp_path / "tel"
    for i in range(5):
        commit(repo, f"old{i}.txt", f"pre-telemetry work {i}")
    assert reconcile(root, repo) == ()


def test_the_untrailered_check_is_opt_in_and_scoped(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                          capture_output=True, text=True).stdout.strip()
    commit(repo, "new.txt", "post-telemetry work with no trailer")
    findings = reconcile(root, repo, require_trailer_since=base)
    untrailered = [f for f in findings if f.kind == "untrailered_commit"]
    assert len(untrailered) == 1 and untrailered[0].severity == "gap"


def test_reconciliation_reports_a_corrupt_record(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    append_event(root, started(prompt=prompts.capture_text(root, "p").as_dict()))
    with run_path(root, RID).open("a", encoding="utf-8") as handle:
        handle.write("garbage\n")
    assert "corrupt_record" in kinds(reconcile(root, repo))


# ---------------------------------------------------------------------------
# the CLI, and the record it commits to a public repository
# ---------------------------------------------------------------------------


def test_wrap_emits_start_and_finish_around_a_command(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    code = cli_main(["--root", str(root), "--repo", str(repo), "wrap",
                     "--task", "a bounded task", "--", "true"])
    assert code == 0
    (rid,) = list_run_ids(root)
    run = read_run(root, rid)
    assert run.status == "completed" and run.exit_code == 0
    assert run.duration_seconds is not None and run.duration_seconds >= 0
    assert run.task == "a bounded task"


def test_wrap_records_a_failing_command_as_failed(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    code = cli_main(["--root", str(root), "--repo", str(repo), "wrap",
                     "--task", "fails", "--", "false"])
    assert code == 1
    (rid,) = list_run_ids(root)
    run = read_run(root, rid)
    assert run.status == "failed" and run.outcome == "crashed" and run.exit_code == 1


def test_wrap_collects_the_artifact_it_produced(tmp_path: Path, repo: Path) -> None:
    root = tmp_path / "tel"
    cli_main(["--root", str(root), "--repo", str(repo), "wrap", "--task", "write",
              "--", "sh", "-c", "echo hi > produced.txt"])
    (rid,) = list_run_ids(root)
    paths = {a["path"] for a in read_run(root, rid).artifacts}
    assert "produced.txt" in paths
    digest = next(a["sha256"] for a in read_run(root, rid).artifacts
                  if a["path"] == "produced.txt")
    assert digest and len(digest) == 64


def test_no_run_record_carries_a_machine_local_home_path(tmp_path: Path, repo: Path) -> None:
    """Run records are committed to a public repository.

    `tests/test_repo_hygiene.py` scans tracked `.jsonl` for this shape, and it
    exists because the leak has happened in this tree before. Caught here once
    already: `probe_context` recorded the worktree's absolute path.
    """
    import re

    root = tmp_path / "tel"
    cli_main(["--root", str(root), "--repo", str(repo), "wrap", "--task", "t",
              "--prompt-text", "p", "--", "true"])
    pattern = re.compile(r"(?:/Users/|/home/)[A-Za-z0-9._-]{1,32}")
    for path in (root / "runs").glob("*.jsonl"):
        assert not pattern.search(path.read_text()), f"machine-local path in {path.name}"


def test_the_cli_refuses_a_reconstructed_run_with_no_source(tmp_path: Path, repo: Path) -> None:
    code = cli_main(["--root", str(tmp_path), "--repo", str(repo), "reconstruct",
                     "--task", "old work"])
    assert code == 2
    assert list_run_ids(tmp_path) == []


def test_the_cli_records_a_reconstructed_run_when_it_cites_a_source(
    tmp_path: Path, repo: Path
) -> None:
    code = cli_main(["--root", str(tmp_path), "--repo", str(repo), "reconstruct",
                     "--task", "old work", "--reconstructed-from", "git log 32e4428"])
    assert code == 0
    (rid,) = list_run_ids(tmp_path)
    run = read_run(tmp_path, rid)
    assert run.capture == "reconstructed"
    assert run.reconstructed_from == "git log 32e4428"
