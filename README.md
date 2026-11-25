# Integer superharmonic matrices on the F-lattice: Lean formalization

[![CI](https://github.com/nitromannitol/f-lattice-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/nitromannitol/f-lattice-lean/actions/workflows/ci.yml) [![Comparator audit](https://github.com/nitromannitol/f-lattice-lean/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/f-lattice-lean/actions/workflows/comparator.yml)

A Lean 4 formalization of

> Ahmed Bou-Rabee, *Integer superharmonic matrices on the F-lattice*, arXiv:2110.07556,

in its corrected edition, which is pinned in [`paper/`](paper/README.md). The two headline results are the classification of the integer superharmonic matrices and the standard and alternate recurrent odometers.

## Status

The formalization is in progress. [`STATUS.md`](STATUS.md) lists what is proved and the named inputs that the headline theorems still take as hypotheses.

## Building

The toolchain is Lean 4.32.0. Run `lake build` from the repository root, and check the manuscript snapshot with `sha256sum -c paper.sha256`.

The Julia code that produces the tile odometers is in [f-lattice-recursion](https://github.com/nitromannitol/f-lattice-recursion).

## AI disclosure

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI (GPT), under the direction of the author. Every proof is checked by the Lean kernel.
