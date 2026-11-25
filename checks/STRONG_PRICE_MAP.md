# STRONG_PRICE_AND_ALTERNATE_STEP §§1–3 against Lean

Status key: PROVED (Lean theorem here or in main), NAMED (a structure field or hypothesis that the producer must supply), OPEN (neither).

## §1 Unrounded primitive P
- P nonincrease on allowed edges (two-level range, W1 unit transfer): NAMED — `OldPolicyData.priceNonincreasing` (OldPolicy.lean);
  the range is the field `StrongEstimates.priceRange`; the W1 unit transfer is `W1Forced` (W1Forcing, W1Phase).
- V star: P = c0 when both sources equal h0: PROVED — `StrongPriceValues.price_eq_cutPrice_of_harmonic` (from
  `W1Lower.delta_eq_price`, `harmonicGrid_shift_price`). The source facts (h0 strips) are NAMED (`zeroStripInterval`, h0 strip).
- H star, one two-level P span (parity s-bounds): OPEN (not in Lean).
- Canonical P nonincrease on H (w = z, w = U+I−z): OPEN.
- |δP| ≤ 1 and no (−1,+1) pair: NAMED — `HasUnitPrice` and `NoPriceSaddle` fields (StrongResidual, StrongEstimates); the producers are §§1–3.

## §2 Strong D on the bulk
- Closed E as the parity rectangle: OPEN as an equivalence; `closedPolygon` is the object used by the `priceRange` field.
- D+(E) ⊂ {0,1,2}, D−(E) ⊂ {−2,−1,0}: NAMED — `StarArgumentInputs.base` (StarRangeArgument.lean; the archive's recurrent-M
  boundary comparison). PROVED from `base`: `star_range_of_argument`, `unit_jump_of_argument`, `laplacian_starDiff`.
- Slip range 0 ≤ D_1 ≤ 2 on E: PROVED from `StrongEstimates` of the conjugate — `slipRange_of_strong` (TieReduce.lean).
- Recurrence of M = min(A, C) (the note's requirement 1): PROVED — `StrongPriceValues.sheetMin_recurrent_of_strong`: from
  `StrongEstimates (conjWord word)`, `i3_sheetLocalInputs_of_strong` (sheet unit, permitA/noA, permitC/noC),
  `constrainedRank_of_variant` (the A and C burning ranks) and `sheetMin_binary_recurrent_of_chain`. No new input beyond the
  conjugate's strong estimates.
- Rounded J bulk monotonicity: PROVED given D monotone — `StrongPriceValues.roundedSlip_mono` (J = ⌈D/2⌉ is monotone in D).
- The white slip comparison D_η(y) ≤ D_η(z) on the selected edge: NAMED — `OldPolicyData.rawSlipNonincreasing`.
- Negative and positive chart analysis (ψ±, S, common primary chart, exits): OPEN.

## §3 Free edges and the full stars
- H full stars D± = 0 by the zero strip: OPEN.
- V full stars: saturation and the triple of consecutive integers with even endpoints: OPEN (`star_range_of_argument` uses only `base`).
- Difference of binary Laplacians gives unit jumps: PROVED (`laplacian_starDiff`, `unit_jump_of_argument`).

## §4 (not in this task) chain gap, two-rank lemma: NAMED — `OldPolicyData.chainNonincreasing`, `StrongResidual.F2F3_policy`.
## §5 (not in this task) sewn alternate: OPEN.
