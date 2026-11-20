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
- [Literal initializers](FLatticePaper/Construction/BaseRegisters.lean): `FLatticePaper.Construction.BaseRun.registers` gives both four-register tuples at the empty word and positive pure runs. Each of the eight masks is supported only on its specified occupied integer sites, with nonemptiness proved for all valid denominators. [The initializer check](checks/Initializers.lean) compares all four current occupied height sets at each of the empty, `22` and `33` words against pinned TSV fixtures. These are finite masks, not proofs of the plane initializers.
- [Farey registers and unique birth](FLatticePaper/Farey/RationalBirth.lean): `FLatticePaper.Farey.parentsAt_valid` gives denominator, parity and unit determinant invariants; `existsUnique_rational_birth` proves coverage and uniqueness across both current slots. The inverse is computable, with no denominator cutoff. [Lineage](FLatticePaper/Farey/Lineage.lean) proves that each non-endpoint retained birth lies at a strict prefix of the same word.
- [Correction chronology](FLatticePaper/Construction/Chronology.lean): `splitInitial_word` and `ancestorHistory_current` verify the pure prefix and chronological suffix fold. The two saved histories have their specified constant-digit suffixes and are nonempty at a nonempty prefix. [The consumer](checks/FareyBirth.lean) checks the actual inverse computation, both retained births, and the distinct pre-update sources on a mixed word.
- [Threshold minima](FLatticePaper/Plane/ThresholdMinimum.lean): `FLatticePaper.isBurningRank_leftThreshold` and `isBurningRank_rightThreshold` prove binary Laplacians and strict ranks for every integer threshold from the unit slip bound and the two signed standard ranks. Strict winners use the winning rank; ties have the exact off-band or preferred-sheet comparisons.
- [Tie-band burn](FLatticePaper/Plane/BandBurn.lean): `FLatticePaper.exists_leftThreshold_bandBurnOrder` and `exists_rightThreshold_bandBurnOrder` burn any finite family of classes given the respective rank factorization on the band. They count the two actual input slots even if projected classes coincide. [The diagonal consumer](checks/ThresholdMinimum.lean) proves finite comparison and a band burn for the concrete pair `0` and `x₁ + x₂`. The true ancestor pairs, their signed choices, and their rank periodicity remain separate proof obligations.

Run these checks from the sandbox repository root.

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean checks/RankAxioms.lean
lake env lean checks/OrderedOverlap.lean
lake env lean checks/AlternateMidpoint.lean
lake env lean checks/Placement.lean
lake env lean checks/Initializers.lean
lake env lean checks/FareyBirth.lean
lake env lean checks/ThresholdMinimum.lean
sha256sum --quiet -c paper.sha256
```

The `#print axioms` checks for the general allowed and comparison theorems and their endpoint consumers report `[propext, Classical.choice, Quot.sound]`. The distinct-input theorem, endpoint Laplacian and endpoint rank report `[propext, Quot.sound]`.

The ordered insertion, correction, and concrete reinsertion checks report only `[propext, Classical.choice, Quot.sound]`. The test inequality itself uses only `[propext, Quot.sound]`.

The midpoint and slip ranks, finite comparison consumer and even non-affinity check report `[propext, Classical.choice, Quot.sound]`. The rounded-height formulas and the two difference increments report `[propext, Quot.sound]`.

The placement, trim and correction consumers report `[propext, Classical.choice, Quot.sound]`.

The base-mask and initial-register checks likewise report `[propext, Classical.choice, Quot.sound]`.

The Farey rational coverage, retained birth and inverse consumer checks report `[propext, Classical.choice, Quot.sound]`; the determinant walk, initial split and nonempty saved word checks report only `[propext]`.

The threshold ranks, band orders and concrete consumers report `[propext, Classical.choice, Quot.sound]`; the left tie comparison reports `[propext, Quot.sound]`.

The bootstrap, ordered-height, alternate-midpoint, placement, initializer and Farey chronology milestones landed on `main` at `4dbc1eb`, `dd24414`, `a0df1d2`, `7056241`, `d08b018` and `acea381`. With the worker's read-only `.git` mount, submit tested named paths via `python3 scripts/checkpoint.py request` and wait for its receipt before editing those paths again.

## Open

The two headline theorems, the literal unbounded mixed-word constructor, the general plane ranks, source-specific finite-tile height comparisons, and occupied-domain period coverage remain open. The ordered height lemma does not supply the actual shifted sources or their geometric comparisons. The recurrence work here proves the direction from allowed sets to pointwise comparison over every finite set. The reverse direction in the paper uses a source strongly connected component and remains open. The endpoint consumer verifies recurrence comparison and superharmonicity at $0/1$ through its explicit rank. The $1/1$ endpoint and endpoint growth, the root and pure-word plane ranks and the general signed rank and band induction are separate obligations.

Next constructor dependencies: use the Farey registers and distinct saved histories in the slot offsets, and connect the ordinary and corrected source lists to placed assembly. For the plane proof, connect the threshold calculation to the actual earlier harmonically conjugate parent pair, and obtain its unit bounds and both signed ranks from the genuine boundary and cut arguments, not as hypotheses on a final source root.
