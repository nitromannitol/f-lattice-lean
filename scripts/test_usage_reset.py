"""Simulate the authorization conditions. This test does not contact Codex."""
from contextlib import nullcontext
import importlib.util
import json
from pathlib import Path
import sqlite3
from tempfile import TemporaryDirectory
from unittest.mock import patch, Mock

spec=importlib.util.spec_from_file_location("usage_reset",Path(__file__).with_name("usage_reset.py"))
watch=importlib.util.module_from_spec(spec)
spec.loader.exec_module(watch)


def simulate(root):
    client=Mock()
    state={}
    def step(left,credit,project=True,goal="active",redeem=True):
        with patch.object(watch,"quota",return_value=(left,[88] if left==0 else [],credit,"account-one")), \
             patch.object(watch,"project_state",return_value=(goal,project)):
            watch.tick(state,redeem)
    with patch.object(watch,"ROOT",root), patch.object(watch,"STATE",root/".work/usage-reset.json"), \
         patch.object(watch,"Account",return_value=nullcontext(client)):
        (root/".work").mkdir()
        (root/".work/thread-id").write_text("the-f-lattice-campaign")
        step(3,1)
        step(0,0)
        step(0,1,project=False)
        step(0,1,goal="paused")
        step(0,1,redeem=False)
        step(0,0,goal="usage_limited")
        assert state["status"] == "awaiting_available_credit"
        step(0,1,project=False,goal="usage_limited")
        assert state["status"] == "awaiting_project_exhaustion"
        step(0,1,goal="usage_limited",redeem=False)
        assert state["status"] == "eligible_read_only_check"
        assert not client.call.called
        client.call.return_value={"outcome":"reset"}
        step(0,1,goal="usage_limited")
        assert client.call.call_count==1
        method,params=client.call.call_args.args
        assert method=="account/rateLimitResetCredit/consume" and params["idempotencyKey"]==state["idempotency_key"]
        with patch.object(watch, "resume_goal") as resume:
            step(100,0,goal="usage_limited")
            step(100,0,goal="usage_limited")
            resume.assert_called_once_with()
        step(100,0)
        step(0,1)
        assert client.call.call_count==1 and state["verified_restoration"]["remaining_percent"]==100
        public=(root/".work/usage-status.json").read_text()
        assert "idempotency_key" not in public and "account_fingerprint" not in public
        # If the reply is lost and the allowance recovers, a later exhaustion still cannot spend twice.
        state.clear(); state.update(pending_redemption=True,idempotency_key="prior-attempt")
        step(100,0)
        step(0,1)
        assert client.call.call_count==1 and state["status"]=="restored_after_unconfirmed_attempt"


def check_window_attribution(root):
    thread = "f-lattice-test"
    with sqlite3.connect(root / "goals_1.sqlite") as conn:
        conn.execute("create table thread_goals (thread_id text, status text)")
        conn.execute("insert into thread_goals values (?, 'usage_limited')", (thread,))
    sessions = root / "sessions/2026/11/21"
    sessions.mkdir(parents=True)
    session_file = sessions / (thread + ".jsonl")
    window = {"used_percent": 100, "resets_at": 89}
    event = {"payload": {"rate_limits": {"limit_id": "codex", "primary": window}}}
    session_file.write_text(json.dumps(event) + "\n")
    pane = Mock(returncode=0, stdout=str(root))
    with patch.object(watch, "CODEX", root), patch.object(watch, "ROOT", root), \
            patch.object(watch.subprocess, "run", return_value=pane):
        for end in (88, 89, 90):
            assert watch.project_state(thread, [end]) == ("usage_limited", True)
        assert watch.project_state(thread, [95]) == ("usage_limited", False)
        window["used_percent"] = 99
        session_file.write_text(json.dumps(event) + "\n")
        assert watch.project_state(thread, [89]) == ("usage_limited", False)


if __name__=="__main__":
    with TemporaryDirectory() as tmp:
        simulate(Path(tmp))
        check_window_attribution(Path(tmp))
    print("Exhaustion, campaign identity, credit availability, read-only checks and one-redemption recovery passed.")
