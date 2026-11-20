# Formalization status

The November 20 corrected edition and its supporting constructor are pinned by [paper.sha256](paper.sha256). [Source correspondence](SOURCE-MAP.md) maps the first Lean results and the remaining paper obligations.

## Checked on Lean 4.32.0

- [Physical graph](FLatticePaper/Graph.lean) defines the horizontal incoming edges at even sites and the vertical incoming edges at odd sites. The Laplacian, induced indegree and incoming boundary use these edges.
- [Rank and comparison](FLatticePaper/Rank.lean) proves `FLatticePaper.IsBurningRank.allowed`, `FLatticePaper.finiteComparison_of_allowed`, and `FLatticePaper.IsBurningRank.finiteComparison`. The rank argument requires both inputs to decrease at a Laplacian $-1$ site and at least one at a Laplacian $0$ site. It proves that every nonempty finite set has an allowed vertex. Finite comparison follows by taking the set of maximizers of the integer difference.
- [Compiled endpoint consumer](FLatticePaper/Endpoint.lean) checks the exact $0/1$ endpoint's checkerboard Laplacian and constructs its decreasing rank on the plane. `FLatticePaper.zeroEndpoint_allowed` and `FLatticePaper.zeroEndpoint_finiteComparison` apply the rank results directly. Both hold without any assumed rank.

Run these checks from the sandbox repository root.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean checks/RankAxioms.lean
sha256sum --quiet -c paper.sha256
```

The `#print axioms` checks for the general allowed and comparison theorems and their endpoint consumers report `[propext, Classical.choice, Quot.sound]`. The distinct-input theorem, endpoint Laplacian and endpoint rank report `[propext, Quot.sound]`.

## Open

The two headline theorems, the literal unbounded tile constructor, the general plane ranks, finite-tile height identification, and occupied-domain period coverage remain open. The recurrence work here proves the direction from allowed sets to pointwise comparison over every finite set. The reverse direction in the paper uses a source strongly connected component and remains open. The endpoint consumer verifies recurrence comparison and superharmonicity at $0/1$ through its explicit rank. The $1/1$ endpoint and endpoint growth, the root and pure-word ranks and the general signed rank and band induction are separate obligations.
