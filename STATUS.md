# Formalization status

## Primary track · Corrected October 2023 manuscript

The November 20 corrected edition and its supporting constructor are pinned by [paper.sha256](paper.sha256). [Source correspondence](SOURCE-MAP.md) maps the checked Lean declarations and the remaining paper obligations.

### Checked on Lean 4.32.0

- [Physical graph](FLatticePaper/Graph.lean) defines the horizontal incoming edges at even sites and the vertical incoming edges at odd sites. The Laplacian, induced indegree and incoming boundary use these edges.
- [Rank and comparison](FLatticePaper/Rank.lean) proves `FLatticePaper.IsBurningRank.allowed`, `FLatticePaper.finiteComparison_of_allowed`, and `FLatticePaper.IsBurningRank.finiteComparison`. The rank argument requires both inputs to decrease at a Laplacian $-1$ site and at least one at a Laplacian $0$ site. It proves that every nonempty finite set has an allowed vertex. Finite comparison follows by taking the set of maximizers of the integer difference.
- [Exact recurrence criterion](FLatticePaper/Plane/Recurrence.lean): `FLatticePaper.recurrent_iff_allowed` proves both directions of `prop:recurrence` for superharmonic integer fields, via the source strong component in the reverse direction. The recurrence declaration uses the exact finite strong-connectivity and global competitor premises.
- [Endpoint consumers](FLatticePaper/Endpoint.lean): `zeroEndpoint_recurrent` and `oneEndpoint_recurrent` prove recurrence of both literal endpoint fields. Their checkerboard Laplacians supply their ranks with no assumed rank; their quadratic growth is separate.
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
- [Arithmetic and physical rotations](FLatticePaper/Plane/RecurrenceRotation.lean): `Farey.rotate_parentsAt` swaps digits 2 and 3, preserving depth and exchanging parity registers. `Recurrent.quarterTurn` uses the exact recurrence criterion to prove superharmonicity and recurrence across the parity-correct physical rotation and arbitrary integer harmonic correction. `IsConstrainedBurningRank.quarterTurn` also transports rank choices. [The consumer](checks/QuarterTurn.lean) checks the rotated mixed birth and checks physical recurrence and finite comparison on a rotated endpoint with a nonzero correction.

- [Unbounded native evaluator](FLatticePaper/Construction/Native.lean): exact ordinary and corrected standard/alternate schedules, both lengths and sides of correction, seventh-source restoration, actual pre-update saved payloads, and final occupied lower-left centering. `evaluateNative_base` proves all literal initial runs succeed; `evaluateNativeState_history` proves saved chronology on successful evaluations. [The check](checks/Native.lean) matches the occupied sites and heights of all 31 pinned fixtures. This is not a proof of all-word mixed success.
- [Schedule consumers](FLatticePaper/Construction/PlacedSchedule.lean): `eval_ok_iff`, `eval_tile_agrees` and `eval_correction_agrees` link the exact assembled output to chronological contact and ordered height comparison, including trim and the correction's max-zero gauge.

- [Period lattice and root coverage](FLatticePaper/Construction/NativeCoverage.lean): `Fraction.integralLattice_eq_span` identifies the actual integer-action lattice, and `mem_modifiedDeck_iff_integral_even` checks its physical parity sublattice. `evaluateNative_empty_covers` verifies the complete quotient on the occupied supports of all eight literal root registers. This is a kernel-checked finite certificate, not a fixture test or a statement about all pure lengths.
- [Affine period and growth](FLatticePaper/Plane/PeriodCocycle.lean): `generator_period_formula`, `generator_periods_affine` and `generator_periods_growth` derive the exact law, bounded tilted remainder and uniform quadratic error from the two prescribed generator identities. `eq_of_covered_generator_periods` proves uniqueness from actual native support coverage and equal generator increments.
- [Endpoint odometers](FLatticePaper/Plane/EndpointGrowth.lean): `checkerboard_endpoints` checks superharmonicity, recurrence and quadratic growth of both literal endpoint fields at their prescribed matrices. [The consumers](checks/Periods.lean) use the matrix-lattice equality for an arbitrary generated birth and the growth theorem at the even root slope.

- [Symbolic reciprocal staircase coverage](FLatticePaper/Construction/StaircaseCoverage.lean): `stairEven_cover` and `stairEvenAlt_cover` prove the two covers for every odd denominator at least three, using the half-shifted real cell and the literal occupied mask, with the $d=3$ alternate rail exception handled by a true transverse period. `evaluateNative_threes_even_covers` consumes both results for the actual even outputs of every nonempty pure-3 run; [the consumer](checks/StaircaseCoverage.lean) instantiates a 200-letter word without enumerating its support.
- [Symbolic near-one staircase coverage](FLatticePaper/Construction/StaircaseCoverage.lean) uses `BaseMask.mem_stairOdd_raw_iff` and `BaseMask.mem_stairOddAlt_raw_iff` to transport the actual raw supports by their respective quarter-turn translations. `stairOdd_cover` and `stairOddAlt_cover` transport the period span with the swapped, signed generators and then apply the constructor's trim. `evaluateNative_twos_odd_covers` checks both native odd outputs for every nonempty pure-2 run. The staircase consumer checks both symbolic native results and their 200-letter instances, with only `[propext, Classical.choice, Quot.sound]`.

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
lake env lean checks/QuarterTurn.lean
lake env lean checks/Native.lean
lake env lean checks/Periods.lean
lake env lean checks/StaircaseCoverage.lean
sha256sum --quiet -c paper.sha256
```

The `#print axioms` checks for the general allowed and comparison theorems and their endpoint consumers report `[propext, Classical.choice, Quot.sound]`. The distinct-input theorem, endpoint Laplacian and endpoint rank report `[propext, Quot.sound]`.

The ordered insertion, correction, and concrete reinsertion checks report only `[propext, Classical.choice, Quot.sound]`. The test inequality itself uses only `[propext, Quot.sound]`.

The midpoint and slip ranks, finite comparison consumer and even non-affinity check report `[propext, Classical.choice, Quot.sound]`. The rounded-height formulas and the two difference increments report `[propext, Quot.sound]`.

The placement, trim and correction consumers report `[propext, Classical.choice, Quot.sound]`.

The base-mask and initial-register checks likewise report `[propext, Classical.choice, Quot.sound]`.

The Farey rational coverage, retained birth and inverse consumer checks report `[propext, Classical.choice, Quot.sound]`; the determinant walk, initial split and nonempty saved word checks report only `[propext]`.

The threshold ranks, band orders and concrete consumers report `[propext, Classical.choice, Quot.sound]`; the left tie comparison reports `[propext, Quot.sound]`.

The exact recurrence criterion, rotation transports, and endpoint recurrence consumers report `[propext, Classical.choice, Quot.sound]`. The $1/1$ Laplacian uses `[propext, Quot.sound]`, and the birth rotation involution only `[propext]`.

The constructor schedule checks, exact lattice and period proofs, kernel-checked root coverage, endpoint odometer consumers and symbolic reciprocal staircase covers report only `[propext, Classical.choice, Quot.sound]`.

The bootstrap, ordered-height, alternate-midpoint, placement, initializer, Farey chronology, threshold, recurrence/rotation and native evaluator milestones landed on `main` at `4dbc1eb`, `dd24414`, `a0df1d2`, `7056241`, `d08b018`, `acea381`, `ab4c8ca`, `f2cf9be` and `2546d52`. The matrix and period laws, root coverage and endpoint growth landed at `8501715`. The symbolic reciprocal staircase cover landed at `68e33d2`. With the worker's read-only `.git` mount, submit tested named paths via `python3 scripts/checkpoint.py request` and wait for its receipt before editing those paths again.

### Open

The two headline theorems, all-word success of mixed evaluation, general plane ranks, source-specific finite-tile height comparisons, and the remaining pure and mixed occupied-domain coverage stay open. The ordered height lemma does not prove the geometric comparisons of the actual shifted sources. The root and pure-word plane ranks and the general signed rank and band induction are separate obligations.

The next constructor dependency is the doubled-ladder cover, followed by the native support and height comparisons for each mixed schedule. For the plane proof, establish the literal plane initializers and connect the threshold calculation to the actual earlier harmonically conjugate parent pair, deriving its unit bounds and both signed ranks from the boundary and cut arguments.

## GeneralK track · Recurrence on the F-lattice and its generalizations

The separate `FLatticePaper.GeneralK` track covers every integer $k\ge2$. It follows the [November 20 request](docs/GENERAL-K-FOLLOWUP.md) and the [GeneralK source correspondence](docs/GENERAL-K-SOURCE-MAP.md). The local sibling snapshot has its own [checksum manifest](docs/general-k.sha256). The corrected October 2023 manuscript remains the primary campaign.

### Proof queue

1. Define the physical operator, prove the equivalence between finite strongly connected comparison, absence of a forbidden set, and absence of a finite legal lowering. Prove the chain test with both endpoint bits, their coincidence at $k=2$, and the explicit forbidden interval with two black interior sites.
2. Classify all residue-only binary charges, construct a physical height for every charge pattern, and give explicit finite countersets when two residues are black.
3. Prove least integer concave completion, the exact retained comparison and its zero-operator case. Derive the scalar odometers and the integer weighted-trace classification, including the leftmost-column argument and the interior case.
4. Prove termination and exact acceptance at every refinement scale for the real growth set, including the boundary criterion. The source makes no critical-circle classification claim.
5. Track the sibling's $k=2$ staircase and Farey results against their own hypotheses and coordinates. The primary open items above track the literal native identification, coverage and mixed-word induction.

The GeneralK statements are queued. The primary checked results listed above concern the corrected October 2023 manuscript.
