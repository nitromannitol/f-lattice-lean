# Formalization status

The November 20 corrected edition and its supporting constructor are pinned by [paper.sha256](paper.sha256). [Source correspondence](SOURCE-MAP.md) maps the first Lean results and the remaining paper obligations.

## Checked on Lean 4.32.0

- [Physical graph](FLatticePaper/Graph.lean) defines the horizontal incoming edges at even sites and the vertical incoming edges at odd sites. The Laplacian, induced indegree and incoming boundary use these edges.
- [Rank and comparison](FLatticePaper/Rank.lean) proves `FLatticePaper.IsBurningRank.allowed`, `FLatticePaper.finiteComparison_of_allowed`, and `FLatticePaper.IsBurningRank.finiteComparison`. The rank argument requires both inputs to decrease at a Laplacian $-1$ site and at least one at a Laplacian $0$ site. It proves that every nonempty finite set has an allowed vertex. Finite comparison follows by taking the set of maximizers of the integer difference.
- [Compiled endpoint consumer](FLatticePaper/Endpoint.lean) checks the exact $0/1$ endpoint's checkerboard Laplacian and constructs its decreasing rank on the plane. `FLatticePaper.zeroEndpoint_allowed` and `FLatticePaper.zeroEndpoint_finiteComparison` apply the rank results directly. Both hold without any assumed rank.
- [Ordered height rule](FLatticePaper/Construction/OrderedOverlap.lean): `FLatticePaper.Construction.HeightTile.contactShift_eq_of_agrees` and `insert_agrees` check the overlap minimum and the result on the union under the three source comparisons. `insertAll_agrees` uses them in insertion order on the full accumulated supports.
- [Correction height consumer](FLatticePaper/Construction/CorrectionHeight.lean): `FLatticePaper.Construction.HeightTile.insert_correctionHeight_agrees` applies the ordered lemma to a correction, subtracts its maximum, and absorbs the resulting gauge at the outer overlap. The [distinct check](checks/OrderedOverlap.lean) compiles a small strict-overlap example and its normalized reinsertion; this is not a verification of the source's reciprocal pure tile.
- [Alternate midpoint](FLatticePaper/Plane/AlternateMidpoint.lean): `FLatticePaper.isBurningRank_roundedMidpoint` checks the binary Laplacian and lexicographic rank by the exact local input calculation. `FLatticePaper.roundedMidpoint_eq_min_of_slip` proves the min formula given the three-value gap bound.
- [Prescribed even slip](FLatticePaper/Plane/AlternateSlip.lean): `FLatticePaper.isBurningRank_alternateCompanion_midpoint` supplies binary Laplacian of the translated sheet by physical parity, rather than assuming it. [The consumer](checks/AlternateMidpoint.lean) applies that rank to finite comparison. The slip bounds, saddle exclusion and the standard's slip-constrained rank are still genuine proof obligations.
- [Even distinctness calculation](FLatticePaper/Plane/AlternatePeriods.lean): the midpoint-minus-standard increments are $0,-1$ on the two generators, and `FLatticePaper.not_integerAffine_roundedMidpoint_sub_standard` rules out an integer-affine difference from those increments. The standard's period jet, unit Farey determinant and interior slope are explicit inputs; this is not a native-tile identification.
- [Sparse placement and assembly](FLatticePaper/Construction/PlacedAssembly.lean): exact destination-slope placement, distinct rectangular trim and occupied lower-left centering, and placed list assembly with trim followed by max normalization for a correction. `HeightTile.meldCorrection_agrees` consumes ordered agreement and tracks the actual spatial shift and additive gauge. [The placement check](checks/Placement.lean) tests the different origins and a large translation without clipping.

Run these checks from the sandbox repository root.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean checks/RankAxioms.lean
lake env lean checks/OrderedOverlap.lean
lake env lean checks/AlternateMidpoint.lean
lake env lean checks/Placement.lean
sha256sum --quiet -c paper.sha256
```

The `#print axioms` checks for the general allowed and comparison theorems and their endpoint consumers report `[propext, Classical.choice, Quot.sound]`. The distinct-input theorem, endpoint Laplacian and endpoint rank report `[propext, Quot.sound]`.

The ordered insertion, correction, and concrete reinsertion checks report only `[propext, Classical.choice, Quot.sound]`. The test inequality itself uses only `[propext, Quot.sound]`.

The midpoint and slip ranks, finite comparison consumer and even non-affinity check report `[propext, Classical.choice, Quot.sound]`. The rounded-height formulas and the two difference increments report `[propext, Quot.sound]`.

The placement, trim and correction consumers report `[propext, Classical.choice, Quot.sound]`.

The bootstrap, ordered-height and alternate-midpoint milestones landed on `main` at `4dbc1eb`, `dd24414` and `a0df1d2`. With the worker's read-only `.git` mount, submit tested named paths via `python3 scripts/checkpoint.py request` and wait for its receipt before editing those paths again.

## Open

The two headline theorems, the literal unbounded tile constructor, the general plane ranks, source-specific finite-tile height comparisons, and occupied-domain period coverage remain open. The height lemma does not supply the root and pure initializers, the actual shifted sources and ancestor chronology, or the comparisons for them. The recurrence work here proves the direction from allowed sets to pointwise comparison over every finite set. The reverse direction in the paper uses a source strongly connected component and remains open. The endpoint consumer verifies recurrence comparison and superharmonicity at $0/1$ through its explicit rank. The $1/1$ endpoint and endpoint growth, the root and pure-word ranks and the general signed rank and band induction are separate obligations.
