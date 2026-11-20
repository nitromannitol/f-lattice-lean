# Running the sandbox campaign

On sandbox, enter **flattice-lean** to attach to the persistent GPT-6.2 Sol xhigh session. Its working directory is /home/nitro/flattice-lean. The launch script uses the installed Codex 0.171 series that successfully submitted a model turn. The original flattice session remains separately accessible. The campaign goal is pinned to the full corrected 2023 draft.

[Current proof status](STATUS.md) · [Mathematical targets](SOURCE-MAP.md) · [Campaign instructions](CAMPAIGN.md)

The local Dropbox project fast-forwards its main branch from sandbox every minute while this Mac is connected. Its .work/sandbox-working directory also gets the uncommitted Lean sources and status notes. The trusted checkpoint window in the sandbox tmux session records each named, tested snapshot requested by the formalizer. For a manual local refresh run scripts/pull_sandbox.sh.

On November 20 the author authorized one earned rate-limit reset when this F-lattice session exhausts the applicable Codex allowance. The sandbox usage-reset window checks the official account service and this session's own use, then redeems one available credit at zero. It preserves the same request key across retries, checks the restored allowance and resumes the F-lattice goal if it stalled on the limit. The account service determines credit availability. The local mirror at .work/usage-status.json records the most recent percentage, available credit count and redemption status. These are shared-account allowances monitored for this project.

To check the guard logic offline, run python3 scripts/test_usage_reset.py. On sandbox, tmux list-windows -t flattice-lean shows the proof agent, checkpoint saver and one-time usage monitor.
