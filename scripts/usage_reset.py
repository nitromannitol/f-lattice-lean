"""One authorized earned-credit redemption for the sandbox F-lattice goal, at exhaustion."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import argparse
import json
import os
import signal
import sqlite3
import subprocess
import time
import uuid
import fcntl

ROOT = Path("/home/nitro/flattice-lean")
CODEX = Path("/home/nitro/.codex")
CLIENT = CODEX/"packages/app-server-daemon/current/bin/codex"
STATE = ROOT/".work/usage-reset.json"


def stamp():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def save(state):
    state["checked_utc"] = stamp()
    tmp=STATE.with_suffix(".tmp")
    tmp.write_text(json.dumps(state,sort_keys=True,indent=2)+"\n")
    os.replace(tmp,STATE)
    public_keys=("checked_utc","status","remaining_percent","available_credits","goal_status",
                 "redeemed_utc","verified_restoration","outcome","last_error")
    public=STATE.with_name("usage-status.json")
    tmp=public.with_suffix(".tmp")
    tmp.write_text(json.dumps({k:state[k] for k in public_keys if k in state},indent=2)+"\\n")
    os.replace(tmp,public)


def timed_out(*_):
    raise TimeoutError("Codex account service timed out")


class Account:
    def __enter__(self):
        self.proc=subprocess.Popen([str(CLIENT),"app-server","--listen","stdio://"],cwd=ROOT,
                                   stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True)
        self.seq=0
        try:
            self.call("initialize",{"clientInfo":{"name":"flattice_monitor","version":"1"},
                                    "capabilities":{"experimentalApi":True}})
            self.write({"method":"initialized"})
        except Exception:
            self.__exit__(None,None,None)
            raise
        return self

    def __exit__(self,*_):
        self.proc.terminate()
        try:
            self.proc.wait(timeout=3)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()

    def write(self,data):
        self.proc.stdin.write(json.dumps(data)+"\n")
        self.proc.stdin.flush()

    def call(self,method,params):
        self.seq+=1
        signal.alarm(35)
        try:
            self.write({"id":self.seq,"method":method,"params":params})
            for line in self.proc.stdout:
                item=json.loads(line)
                if item.get("id")==self.seq:
                    if "error" in item:
                        raise RuntimeError(str(item["error"].get("message","RPC error"))[:230])
                    return item["result"]
            raise RuntimeError("Codex account service disconnected")
        finally:
            signal.alarm(0)


def quota(client):
    result=client.call("account/rateLimits/read",{"excludeResetCreditDetails":False})
    bucket=(result.get("rateLimitsByLimitId") or {}).get("codex") or result["rateLimits"]
    if bucket.get("limitId") not in (None,"codex"):
        raise RuntimeError("Missing the campaign's codex rate-limit bucket")
    windows=[bucket[k] for k in ("primary","secondary") if bucket.get(k)]
    if not windows:
        raise RuntimeError("No current Codex usage windows")
    remaining=min(100-int(w["usedPercent"]) for w in windows)
    ends=[w["resetsAt"] for w in windows if int(w["usedPercent"])>=100]
    credits=result.get("rateLimitResetCredits")
    available=None if credits is None else credits.get("availableCount")
    identity=result.get("accountId")
    if not identity:
        raise RuntimeError("Account identity unavailable")
    return remaining,ends,available,sha256(str(identity).encode()).hexdigest()


def project_state(tid,ends):
    conn=sqlite3.connect("file:"+str(CODEX/"goals_1.sqlite")+"?mode=ro",uri=True)
    try:
        goal=conn.execute("select status from thread_goals where thread_id=?",(tid,)).fetchone()
    finally:
        conn.close()
    if not goal:
        return None,False
    pane=subprocess.run(["tmux","display-message","-p","-t","=flattice-lean:0.0",
                         "#{pane_current_path}"],capture_output=True,text=True)
    if pane.returncode or pane.stdout.strip()!=str(ROOT):
        return goal[0],False
    files=list((CODEX/"sessions").glob("*/*/*/*"+tid+"*.jsonl"))
    exhausted=False
    error_time=None
    if files and ends:
        with max(files,key=lambda p:p.stat().st_mtime).open("rb") as f:
            if f.seek(0,2)>2_000_000:
                f.seek(-2_000_000,2)
                f.readline()
            else:
                f.seek(0)
            for line in f:
                try:
                    e=json.loads(line); p=e.get("payload",{})
                except (ValueError,UnicodeDecodeError):
                    continue
                if not isinstance(p,dict):
                    continue
                limits=p.get("rate_limits") or {}
                if limits.get("limit_id") in (None,"codex") and any(limits.get(k) for k in ("primary","secondary")):
                    exhausted=any((limits.get(k) or {}).get("resets_at") in ends and
                                  (limits.get(k) or {}).get("used_percent",0)>=100 for k in ("primary","secondary"))
                if p.get("type")=="error" and any(t in str(p).lower() for t in ("usage limit","usage_limit","rate_limit_reached")):
                    error_time=e.get("timestamp")
    if error_time:
        age=time.time()-datetime.fromisoformat(error_time.replace("Z","+00:00")).timestamp()
        exhausted=exhausted or 0<=age<3600
    return goal[0], exhausted


def resume_goal():
    target="=flattice-lean:0.0"
    subprocess.run(["tmux","send-keys","-t",target,"-l","/goal resume"],check=True)
    time.sleep(0.7)
    subprocess.run(["tmux","send-keys","-t",target,"Enter"],check=True)


def tick(state,may_redeem):
    tid=(ROOT/".work/thread-id").read_text().strip()
    if state.get("thread_id",tid)!=tid:
        raise ValueError("Campaign thread changed")
    state["thread_id"]=tid
    with Account() as client:
        remain,ends,credit,account=quota(client)
        if state.get("account_fingerprint",account)!=account:
            raise ValueError("The sandbox account changed")
        state.update(account_fingerprint=account,remaining_percent=remain,available_credits=credit,
                     exhausted_window_ends=ends)
        goal,project_exhausted=project_state(tid,ends)
        state["goal_status"]=goal
        if state.get("redeemed_utc"):
            if remain>0:
                state.setdefault("verified_restoration",{"remaining_percent":remain,"utc":stamp()})
                if goal=="blocked" and state.get("goal_at_redemption") in ("active","blocked") and not state.get("resume_sent"):
                    resume_goal()
                    state["resume_sent"]=stamp()
                if goal=="active" or goal=="complete":
                    state["status"]="restored_and_goal_verified"
                else:
                    state["status"]="restored_check_goal"
            else:
                state["status"]="credit_redeemed_checking_allowance"
        elif state.get("pending_redemption") and remain>0:
            state["status"]="restored_after_unconfirmed_attempt"
            state.setdefault("unconfirmed_restoration_utc",stamp())
        elif state.get("unconfirmed_restoration_utc"):
            state["status"]="restored_after_unconfirmed_attempt"
        elif goal not in ("active","blocked"):
            state["status"]="inactive_campaign"
        elif remain>0:
            state["status"]="armed_above_zero"
        elif not project_exhausted:
            state["status"]="awaiting_project_exhaustion"
        elif credit==0 and not state.get("pending_redemption"):
            state["status"]="awaiting_available_credit"
        elif may_redeem:
            state["pending_redemption"]=True
            state.setdefault("idempotency_key",str(uuid.uuid4()))
            state["goal_at_redemption"]=goal
            save(state)  # Save the key before the account mutation, including crash/retry.
            response=client.call("account/rateLimitResetCredit/consume",{"idempotencyKey":state["idempotency_key"]})
            outcome=response["outcome"]
            state["outcome"]=outcome
            if outcome in ("reset","alreadyRedeemed"):
                state["redeemed_utc"]=stamp()
                state["status"]="credit_redeemed_checking_allowance"
            else:
                state["status"]={"noCredit":"awaiting_available_credit","nothingToReset":"service_reports_no_eligible_window"}.get(outcome,outcome)
                state["pending_redemption"]=False
        else:
            state["status"]="eligible_read_only_check"
    state.pop("last_error",None)
    save(state)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--watch",action="store_true")
    args=parser.parse_args()
    signal.signal(signal.SIGALRM,timed_out)
    with (ROOT/".work/usage-reset.lock").open("a") as lock:
        fcntl.flock(lock.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
        state=json.loads(STATE.read_text()) if STATE.exists() else {}
        while True:
            try:
                tick(state,args.watch)
            except (ValueError, OSError, RuntimeError, sqlite3.Error, subprocess.SubprocessError) as exc:
                state["last_error"]=str(exc)[:230]
                save(state)
            print(state.get("checked_utc"),state.get("status"),state.get("remaining_percent"),
                  state.get("available_credits"),state.get("last_error",""),flush=True)
            if (not args.watch or state.get("goal_status")=="complete" or state.get("status") in\n                    ("restored_and_goal_verified","restored_after_unconfirmed_attempt")):
                break
            time.sleep(60)


if __name__=="__main__":
    main()
