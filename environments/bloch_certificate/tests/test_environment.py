"""Exercise the installed verifiers rubric using explicitly supplied test answers."""
import asyncio
import json
import pytest
import verifiers.types as vt
from test_oracle import archive_path
from bloch_certificate import load_environment


def test_real_rubric_scores_all_four_tasks_with_audit_trails():
    env = load_environment(archive_path=str(archive_path()))
    dataset = env.get_eval_dataset()
    assert len(dataset) == 4
    gold = ["0.0114402996202", "0.0113729923988", "0.0153", "0.0153040536"]
    async def check():
        for row, answer in zip(dataset, gold):
            state = dict(row, completion=[{"role": "assistant", "content": json.dumps({"target": answer})}],
                         tool_calls=[], timing={})
            await env.rubric.score_rollout(state)
            assert state["reward"] == 1.0
            assert state["bloch_audit"]["status"] == "accepted"
            state["completion"] = [{"role": "assistant", "content": '{"target":"0.09"}'}]
            await env.rubric.score_rollout(state)
            assert state["reward"] == 0.0
        result = json.loads(await env.tool_map["inspect_certificate"]("fine"))
        assert result["gain"] == gold[0]
        accepted = json.loads(await env.tool_map["check_near_target"]("0.0153040536", "cutoff"))
        assert accepted["accepted"] is True
        rejected = json.loads(await env.tool_map["check_near_target"]("0.0153", "cutoff"))
        assert rejected["accepted"] is False
        published = json.loads(await env.tool_map["check_near_target"]("0.0153", "published"))
        assert published["accepted"] is True
        with pytest.raises(ValueError, match="goal"):
            await env.tool_map["check_near_target"]("0.0153", "other")

        state_a = {"near_target_queries": 23}
        state_b = {"near_target_queries": 0}
        calls_a = [vt.ToolCall(id="a", name="check_near_target", arguments='{"target":"0.0153","goal":"published"}'),
                   vt.ToolCall(id="b", name="check_near_target", arguments='{"target":"0.0153","goal":"published"}')]
        calls_b = [vt.ToolCall(id="c", name="check_near_target", arguments='{"target":"0.0153","goal":"published"}'),
                   vt.ToolCall(id="d", name="check_near_target", arguments='{"target":"0.0153","goal":"published"}')]
        replies_a, replies_b = await asyncio.gather(
            env.env_response([vt.AssistantMessage(tool_calls=calls_a)], state_a),
            env.env_response([vt.AssistantMessage(tool_calls=calls_b)], state_b),
        )
        assert state_a["near_target_queries"] == 24
        assert "budget exhausted" in replies_a[1].content
        assert state_b["near_target_queries"] == 2
        assert all("true" in reply.content for reply in replies_b)

        # Direct calls outside an env_response still fail closed at the same cap.
        env._near_queries.set(0)
        for index in range(24):
            await env.call_tool("check_near_target", {"target": "0.0153", "goal": "published"}, str(index))
        with pytest.raises(ValueError, match="budget exhausted"):
            await env.call_tool("check_near_target", {"target": "0.0153", "goal": "published"}, "overflow")
    asyncio.run(check())
