"""Public, read-only Bloch demo for the released verifiers 0.2.1 API."""
import asyncio
import contextvars
import json
import os
from decimal import Decimal
from pathlib import Path

from datasets import Dataset
import verifiers as vf

from .oracle import Oracle, OracleError, parse_target

DEFAULT_ARCHIVE = Path.home() / ".cache" / "bloch-certificate" / "bloch-computations-1.0.0.zip"


class BoundedToolEnv(vf.ToolEnv):
    """Apply the target-query budget per rollout, including parallel rollouts."""

    def __init__(self, *args, **kwargs):
        self._near_queries = contextvars.ContextVar("near_queries", default=0)
        super().__init__(*args, **kwargs)

    async def call_tool(self, tool_name, tool_args, tool_call_id, **kwargs):
        if tool_name == "check_near_target":
            used = self._near_queries.get()
            if used >= 24:
                raise ValueError("near-target query budget exhausted")
            self._near_queries.set(used + 1)
        return await super().call_tool(tool_name, tool_args, tool_call_id, **kwargs)

    async def env_response(self, messages, state, **kwargs):
        token = self._near_queries.set(int(state.get("near_target_queries", 0)))
        try:
            response = await super().env_response(messages, state, **kwargs)
            state["near_target_queries"] = self._near_queries.get()
            return response
        finally:
            self._near_queries.reset(token)


def load_environment(archive_path: str | None = None, split: str = "eval", **kwargs) -> vf.Environment:
    """Four public calibration tasks, not a held-out benchmark or Lean environment."""
    if split != "eval":
        raise ValueError("only the public eval split exists; no disjoint training split")
    archive = Path(archive_path or os.environ.get("BLOCH_ARCHIVE", DEFAULT_ARCHIVE))
    if not archive.exists():
        from .cli import prepare
        prepare(archive)
    oracle = Oracle(archive)
    parser = vf.Parser()

    async def inspect_certificate(profile: str) -> str:
        """Replay a fixed-radius certificate ('fine' or 'coarse') and return its actual output."""
        if profile not in {"fine", "coarse"}:
            raise ValueError("profile must be fine or coarse")
        result = await asyncio.to_thread(oracle.run, profile)
        return json.dumps(result)

    async def check_near_target(target: str, goal: str) -> str:
        """Grade one near-branch probe for goal 'published' or 'cutoff'.

        This uses the exact same floor, positivity gate, and strict cutoff as the
        final reward. BoundedToolEnv permits 24 calls per rollout, enough for a
        1e-10 bisection from the disclosed bracket. No away sector is replayed.
        """
        value = parse_target(json.dumps({"target": target}))
        accepted, _evidence = await asyncio.to_thread(oracle.near_verdict, goal, value)
        return json.dumps({"accepted": accepted, "goal": goal,
                           "scope": "near branch only"})

    async def certificate_reward(completion, info, state, **_kwargs) -> float:
        text = parser.parse_answer(completion)
        try:
            result = await asyncio.to_thread(oracle.grade, info["task_id"], text)
        except OracleError as exc:
            state["bloch_audit"] = {"status": "oracle_error", "reason": str(exc)}
            raise
        state["bloch_audit"] = result
        return result["reward"]

    instructions = (
        'Return your final answer as exactly {"target":"0.decimal_digits"}, with no code fence or prose. '
        "You can query the supplied read-only tools. No shell or arbitrary code execution is available. "
        "These tasks check certificate arithmetic, not the paper's analytic bridge or a new theorem. "
    )
    rows = []
    for task, question in [
        ("fine-reproduce", "Replay the fine fixed-radius certificate and report the midpoint printed for the (C) gain over sqrt(3)/4, with all printed digits."),
        ("coarse-reproduce", "Replay the coarse fixed-radius certificate and report the midpoint printed for the (C) gain over sqrt(3)/4, with all printed digits."),
        ("near-reproduce", "Call check_near_target with goal published. Check that the shipped near-branch gate accepts the published target 0.0153, then submit it. Do not search for a larger value. This does not replay away sectors."),
        ("near-branch-cutoff", "Call check_near_target with goal cutoff. Use the near-branch gate to find an accepted target within 0.0000000001 below its cutoff. The cutoff is between 0.0153 and 0.0154. Do not claim an away-sector or full-theorem result."),
    ]:
        rows.append({"prompt": [{"role": "user", "content": instructions + question}],
                     "answer": "", "info": {"task_id": task}, "task": "bloch-certificate"})
    return BoundedToolEnv(eval_dataset=Dataset.from_list(rows),
                      tools=[inspect_certificate, check_near_target],
                      parser=parser, rubric=vf.Rubric(funcs=[certificate_reward]),
                      max_turns=30, stop_errors=[OracleError], **kwargs)
