#!/usr/bin/env bash
set -eu
campaign_root=/home/nitro/flattice-lean
export PATH="/home/nitro/.elan/bin:$PATH"
cd "$campaign_root"
if test -s .work/thread-id; then
    read -r campaign_thread < .work/thread-id
    exec /usr/bin/codex resume "$campaign_thread" -m gpt-6.2-sol -c 'model_reasoning_effort="xhigh"' -c 'check_for_update_on_startup=false' --no-alt-screen --sandbox workspace-write --ask-for-approval never -C "$campaign_root"
fi
exec /usr/bin/codex -m gpt-6.2-sol -c 'model_reasoning_effort="xhigh"' -c 'check_for_update_on_startup=false' --no-alt-screen --sandbox workspace-write --ask-for-approval never -C "$campaign_root"
