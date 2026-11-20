#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/.."
mkdir -p .work/sandbox-working
rsync -a --include='/FLatticePaper.lean' --include='/FLatticePaper/***' --include='/checks/***' \
    --include='/docs/***' --include='/audit/***' --include='/STATUS.md' --include='/SOURCE-MAP.md' \
    --exclude='*' sandbox:/home/nitro/flattice-lean/ .work/sandbox-working/
rsync -a sandbox:/home/nitro/flattice-lean/.work/usage-status.json .work/usage-status.json
git fetch --quiet sandbox main
test "$(git branch --show-current)" = main || exit 0
test -z "$(git status --porcelain --untracked-files=normal)" || exit 0
git merge-base --is-ancestor HEAD FETCH_HEAD || exit 0
git merge --ff-only --quiet FETCH_HEAD
