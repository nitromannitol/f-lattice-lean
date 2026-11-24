import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.StrongUnitPrice
import FLatticePaper.Plane.Induction.F2F3Pure
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.TieReduce

/-!
# The strong residual of a proper word from the conjugate's strong estimates (task w1: the residual, field by field)

`strongResidual_of_conj`: `StrongResidual word` from `StrongEstimates (conjWord word)` and four named inputs. Every other field is
derived from the packet of the word, which is itself derived from the conjugate's strong estimates (`packet_of_strong`):

* `priceRange` from `priceRange_of_conjugate`, with the boundary bound `hbd` named;
* `priceDrift` and `slipDrift` from the packet's periods (`ChildFrame.price_kernel`, `price_transverse`, `slip_kernel`,
  `slip_transverse`);
* `zeroStripInterval` from `zeroStripInterval_of_packet`;
* `zeroEvenLine` from `zeroEvenLine_field`, with the even seed `hseed` named;
* `F1_unitPrice`, `F1_noPriceSaddle` from `unitPrice_and_noSaddle`, with the star classification `hcls` named;
* `F2F3_policy` from `rankWithIncrements_of_strict_hull`, with the policy and the strict rank `hpol` named.

The survey of the four named inputs is in `reports/w1-strong-residual-step.md`.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The strong residual of a proper word from the conjugate's strong estimates.** The named inputs are the boundary price bound
`hbd`, the even seed `hseed`, the star classification `hcls`, and the policy with a strict rank `hpol`. -/
theorem strongResidual_of_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hseed : ∀ w : Site, ¬ EvenSite w →
      (frameAt word).sGrade w = 2 - 3 * (frameAt word).child.den + (frameAt word).child.num →
        standardField word w = harmonicGrid w)
    (hcls : FLatticePaper.StrongUnitPrice.StarClassified (frameAt word) (standardField word))
    (hpol : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ (policy : Site → Site → Prop) (R : Site → ℤ) (cU cV : ℤ),
      RetainQuota (standardField word) policy ∧
      NonincreasingAlong ((frameAt word).chainPotential (standardField word) η) policy ∧
      NonincreasingAlong ((frameAt word).price (standardField word)) policy ∧
      NonincreasingAlong ((frameAt word).roundedSlip (standardField word) η) policy ∧
      (∀ z, R (z + (frameAt word).child.modifiedDeck.kernel) = R z + cU) ∧
      (∀ z, R (z + (frameAt word).child.modifiedDeck.transverse) = R z + cV) ∧
      (∀ x i, policy x i → R i < R x)) :
    StrongResidual word := by
  have hpk : (frameAt word).Packet (standardField word) := FLatticePaper.Induction.packet_of_strong h hSE
  have hPR := FLatticePaper.StrongPriceInputs.priceRange_of_conjugate h hSE hbd
  have hPU : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) z - 1 :=
    fun z => (frameAt word).price_kernel (standardField word) hpk.periods z
  have hPV : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) z :=
    fun z => (frameAt word).price_transverse (standardField word) hpk.periods z
  have hSU : ∀ η : ℤ, ∀ z, (frameAt word).slip (standardField word) η
      (z + (frameAt word).child.modifiedDeck.kernel) = (frameAt word).slip (standardField word) η z :=
    fun η z => (frameAt word).slip_kernel (standardField word) hpk.periods η z
  have hSV : ∀ η : ℤ, ∀ z, (frameAt word).slip (standardField word) η
      (z + (frameAt word).child.modifiedDeck.transverse) = (frameAt word).slip (standardField word) η z + 2 * η :=
    fun η z => (frameAt word).slip_transverse (standardField word) hpk.periods η z
  have hZE := FLatticePaper.W1ZeroStrip.zeroEvenLine_field word hpk hPR hPU hPV hseed
  have hU := FLatticePaper.StrongUnitPrice.unitPrice_and_noSaddle (frameAt word) (standardField word) hPR hPV hcls
  refine
    { priceRange := hPR
      priceDrift := fun z => ⟨by linarith [hPU z], by linarith [hPV z]⟩
      slipDrift := fun η _ z => ⟨by linarith [hSU η z], by linarith [hSV η z]⟩
      zeroStripInterval := FLatticePaper.W1ZeroStrip.zeroStripInterval_of_packet word hpk
      zeroEvenLine := hZE
      F1_unitPrice := hU.1
      F1_noPriceSaddle := hU.2
      F2F3_policy := ?_ }
  intro η hη
  obtain ⟨policy, R, cU, cV, hq, hΦ, hP, hJ, hRU, hRV, hstrict⟩ := hpol η hη
  refine ⟨policy, hq, hΦ, fun a c ha hc => ?_⟩
  refine FLatticePaper.EPolicy.rankWithIncrements_of_strict_hull hη (P := (frameAt word).price (standardField word))
    (J := (frameAt word).roundedSlip (standardField word) η) hPU hPV ?_ ?_ (fun x y hxy => ⟨hP x y hxy, hJ x y hxy⟩)
    hRU hRV hstrict a c ha hc
  · intro z
    have := hSU η z
    unfold ChildFrame.roundedSlip
    omega
  · intro z
    have := hSV η z
    unfold ChildFrame.roundedSlip
    omega

end FLatticePaper.Induction
