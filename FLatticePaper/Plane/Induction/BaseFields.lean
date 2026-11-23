import FLatticePaper.Plane.Induction.StrongInduction
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosStripFacts
import FLatticePaper.Plane.Induction.Packet

/-! Task 41: the base words of the strong estimates.

The packets at the base words are proved: the reciprocal packet at `3^k` (`reciprocal_packet`) and the twos packet at `2^(k+1)`
(`twos_packet_standard`, with the twos zero and harmonic strips). What remains of the base is named here:

* `BaseSlip u`: the slip fields (unit slip, no even saddle, slip range) of `StrongEstimates u`;
* `StrongResidual u`: the residual fields (price range and unit and no-saddle, drifts, zero strip and even line, policy).

Both are checked numerically at the base words (`3^k`, `k ≤ 4`, including the root; `2^k`, `k ≤ 3`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The slip fields of the strong estimates of a word (named base input). -/
structure BaseSlip (u : Word) : Prop where
  F1_unitSlip : HasUnitSlip (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  F1_noSlipSaddle : NoEvenSlipSaddle (standardField u) (fun z => standardField u (z + (frameAt u).shortShift))
  slipRange : ∀ z ∈ (frameAt u).closedPolygon,
    0 ≤ (frameAt u).slip (standardField u) 1 z ∧ (frameAt u).slip (standardField u) 1 z ≤ 2

/-- **The strong estimates of the pure word `3^k`**, from its reciprocal packet and the named base inputs. -/
theorem StrongEstimates.of_base_pure (k : ℕ) (hs : BaseSlip (List.replicate k Digit.three))
    (hr : StrongResidual (List.replicate k Digit.three)) :
    StrongEstimates (List.replicate k Digit.three) :=
  { packet := reciprocal_packet k
    slipRange := hs.slipRange
    priceRange := hr.priceRange
    priceDrift := hr.priceDrift
    slipDrift := hr.slipDrift
    zeroStripInterval := hr.zeroStripInterval
    zeroEvenLine := hr.zeroEvenLine
    F1_unitSlip := hs.F1_unitSlip
    F1_noSlipSaddle := hs.F1_noSlipSaddle
    F1_unitPrice := hr.F1_unitPrice
    F1_noPriceSaddle := hr.F1_noPriceSaddle
    F2F3_policy := hr.F2F3_policy }

/-- **The strong estimates of the two-power word `2^(k+1)`**, from its twos packet and the named base inputs. -/
theorem StrongEstimates.of_base_two (k : ℕ) (hs : BaseSlip (List.replicate (k + 1) Digit.two))
    (hr : StrongResidual (List.replicate (k + 1) Digit.two)) :
    StrongEstimates (List.replicate (k + 1) Digit.two) :=
  { packet := twos_packet_standard k (fun _ hz ht => twos_zero_strip k hz ht)
      (fun _ hz hs => twos_harm_strip k hz hs)
    slipRange := hs.slipRange
    priceRange := hr.priceRange
    priceDrift := hr.priceDrift
    slipDrift := hr.slipDrift
    zeroStripInterval := hr.zeroStripInterval
    zeroEvenLine := hr.zeroEvenLine
    F1_unitSlip := hs.F1_unitSlip
    F1_noSlipSaddle := hs.F1_noSlipSaddle
    F1_unitPrice := hr.F1_unitPrice
    F1_noPriceSaddle := hr.F1_noPriceSaddle
    F2F3_policy := hr.F2F3_policy }

end FLatticePaper.Induction
