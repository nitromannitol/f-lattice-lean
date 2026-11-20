"""Simulate the authorization conditions. This test does not contact Codex."""
from contextlib import nullcontext
import importlib.util
from pathlib import Path
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
        assert not client.call.called
        client.call.return_value={"outcome":"reset"}
        step(0,1)
        assert client.call.call_count==1
        method,params=client.call.call_args.args
        assert method=="account/rateLimitResetCredit/consume" and params["idempotencyKey"]==state["idempotency_key"]
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


if __name__=="__main__":
    with TemporaryDirectory() as tmp:
        simulate(Path(tmp))
    print("Exhaustion, campaign identity, credit availability, read-only checks and one-redemption recovery passed.")
