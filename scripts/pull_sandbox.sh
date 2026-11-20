#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/.."
git fetch --quiet sandbox main
test "$(git branch --show-current)" = main || exit 0
test -z "$(git status --porcelain --untracked-files=normal)" || exit 0
git merge-base --is-ancestor HEAD FETCH_HEAD || exit 0
git merge --ff-only --quiet FETCH_HEAD
