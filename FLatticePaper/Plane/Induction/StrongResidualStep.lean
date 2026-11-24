import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.StrongUnitPrice
import FLatticePaper.Plane.Induction.F2F3Pure
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.StarClassify
import FLatticePaper.Plane.Induction.SeedTransverse
import FLatticePaper.Farey.Numerators

/-!
# The strong residual of a proper word from the conjugate's strong estimates (task w1: the residual, field by field)

`strongResidual_of_conj`: `StrongResidual word` from `StrongEstimates (conjWord word)` and four named inputs. Every other field is
derived from the packet of the word, which is itself derived from the conjugate's strong estimates (`packet_of_strong`):

* `priceRange` from `priceRange_of_conjugate`, with the boundary bound `hbd` named;
* `priceDrift` and `slipDrift` from the packet's periods (`ChildFrame.price_kernel`, `price_transverse`, `slip_kernel`,
  `slip_transverse`);
* `zeroStripInterval` from `zeroStripInterval_of_packet`;
* `zeroEvenLine` from `zeroEvenLine_field`, with the even seed `hseed` named;
* `F1_unitPrice`, `F1_noPriceSaddle` from `unitPrice_and_noSaddle`, with the star classification derived (`hcls` is no longer named);
* `F2F3_policy` from `rankWithIncrements_of_strict_hull`, with the policy and the strict rank `hpol` named.

The survey of the four named inputs is in `reports/w1-strong-residual-step.md`.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The strong residual of a proper word from the conjugate's strong estimates.** The named inputs are the boundary price bound
`hbd`, the even seed check `hseed0`, and the policy with a strict rank `hpol` (the star classification is derived; it needs a digit other than `two` too).

`hcls` is no longer an input: the star classification is derived (`StarClassified`, from `starClassified_of_grades`) for every word with
a digit other than `three` and a digit other than `two` (the proper, non-two-power words), from the strips of the packet. The derivation
uses the arithmetic of the Farey recursion: `3 ≤ child.num` (`current_even_num_ge_three`) and `4 ≤ child.den − child.num`
(`current_even_diff_ge_four`). The grade covering that proves it is `StarCover.box_cover`.

`hseed0` is one check (SeedTransverse): the difference `standardField word − harmonicGrid` is invariant under the transverse vector
(proved: the packet's transverse constant is `−(T + L)/2`, the harmonic constant), and the odd seed line is one transverse class `z0 + Z·V`
(proved from the coprimality of the child fraction). So the seed holds on the whole odd seed line once it holds at one odd seed site `z0`.
That single check is the named input.
-/
theorem strongResidual_of_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (h2 : ∃ x ∈ word, x ≠ Digit.two)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hseed0 : ∃ z0 : Site, ¬ EvenSite z0 ∧
      (frameAt word).sGrade z0 = 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ∧
        standardField word z0 = harmonicGrid z0)
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
  obtain ⟨z0, hz0o, hz0s, hz0c⟩ := hseed0
  obtain ⟨a, b, ha, hb⟩ := FLatticePaper.PriceDeck.child_odd_witness (frameAt word)
  have hTe := FLatticePaper.StrongUnitPrice.periodDenominator_even_of (frameAt word) a b ha hb
  have hseed := FLatticePaper.Induction.SeedTransverse.seed_of_check (frameAt word) (standardField word) hpk a ha z0
    hz0s hz0o hz0c (by omega) (by omega) (by omega) hTe
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
  have hn3 : 3 ≤ (frameAt word).child.num := FLatticePaper.Farey.current_even_num_ge_three word h
  have hd4 : 4 ≤ (frameAt word).child.den - (frameAt word).child.num :=
    FLatticePaper.Farey.current_even_diff_ge_four word h2
  have hcls := FLatticePaper.StrongUnitPrice.starClassified_of_grades (frameAt word) (standardField word) hn3 hd4 hpk.strips
  have hU := FLatticePaper.StrongUnitPrice.unitPrice_and_noSaddle (frameAt word) (standardField word) hPR hPU hPV hcls
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
