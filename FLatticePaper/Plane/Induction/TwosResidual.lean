import FLatticePaper.Plane.Induction.TwosPriceE
import FLatticePaper.Plane.Induction.TwosDrifts
import FLatticePaper.Plane.Induction.TwosZeroStrip
import FLatticePaper.Plane.Induction.TwosZeroEven
import FLatticePaper.Plane.Induction.TwosUnitPrice
import FLatticePaper.Plane.Induction.TwosNoPriceSaddle
import FLatticePaper.Plane.Induction.TwosBaseSlip
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.F2F3Pure

/-!
# The twos base: `StrongResidual (2^(k+1))` from its policy field, and from the twos games with rank

`strongResidual_twos_of_policy`: the twos analogue of `strongResidual_threes_of_policy`. Every field of `StrongResidual (2^(k+1))` is a
twos lemma of main (`twos_priceRange_E`, the drifts of `TwosDrifts`, `twos_zeroStripInterval`, `twos_zeroEvenLine`, `twos_unitPrice`,
`twos_noPriceSaddle`), except the policy field `F2F3_policy`, which is the hypothesis.

`twos_F2F3_of_gamesWithRank`: the policy field follows from the twos games with a deck rank (`GamesWithRank (2^(k+1))`): the policy and the
monotone price and rounded slip come from `policy_of_gamesWithRank`, the drifts of price and slip are the twos drifts, and the rank with
increments is `rankWithIncrements_of_strict_hull`.

`strongResidual_twos_of_games`: so `StrongResidual (2^(k+1))` follows from `GamesWithRank (2^(k+1))` alone.
-/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **`StrongResidual` at the twos word `2^(k+1)`, from the policy field alone** (the twos analogue of `strongResidual_threes_of_policy`). -/
theorem strongResidual_twos_of_policy (k : ℕ)
    (hpol : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
      RetainQuota (standardField (List.replicate (k + 1) Digit.two)) policy ∧
        NonincreasingAlong ((frameAt (List.replicate (k + 1) Digit.two)).chainPotential
          (standardField (List.replicate (k + 1) Digit.two)) η) policy ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements policy (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel
            (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse (-a) (c * η)) :
    StrongResidual (List.replicate (k + 1) Digit.two) where
  priceRange := fun z hz => twos_priceRange_E k z hz
  priceDrift := fun z => ⟨twos_price_drift_kernel k z, twos_price_drift_transverse k z⟩
  slipDrift := fun η hη z => ⟨twos_slip_drift_kernel k η z, twos_slip_drift_transverse k η hη z⟩
  zeroStripInterval := twos_zeroStripInterval k
  zeroEvenLine := twos_zeroEvenLine k
  F1_unitPrice := twos_unitPrice k
  F1_noPriceSaddle := twos_noPriceSaddle k
  F2F3_policy := hpol

/-- **The policy field of the twos word from its games with a deck rank.** -/
theorem twos_F2F3_of_gamesWithRank (k : ℕ) (h : GamesWithRank (List.replicate (k + 1) Digit.two)) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → ∃ policy : Site → Site → Prop,
      RetainQuota (standardField (List.replicate (k + 1) Digit.two)) policy ∧
        NonincreasingAlong ((frameAt (List.replicate (k + 1) Digit.two)).chainPotential
          (standardField (List.replicate (k + 1) Digit.two)) η) policy ∧
        ∀ a c : ℤ, 0 < a → 0 < c →
          RankWithIncrements policy (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel
            (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse (-a) (c * η) := by
  intro η hη
  obtain ⟨policy, R, cU, cV, hq, hchain, hP, hJ, hRU, hRV, hstr⟩ := policy_of_gamesWithRank h η hη
  refine ⟨policy, hq, hchain, fun a c ha hc => ?_⟩
  have hPU : ∀ z, (frameAt (List.replicate (k + 1) Digit.two)).price
      (standardField (List.replicate (k + 1) Digit.two))
      (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) z - 1 := fun z => by
    have := twos_price_drift_kernel k z
    linarith
  have hPV : ∀ z, (frameAt (List.replicate (k + 1) Digit.two)).price
      (standardField (List.replicate (k + 1) Digit.two))
      (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate (k + 1) Digit.two)).price
        (standardField (List.replicate (k + 1) Digit.two)) z := fun z => by
    have := twos_price_drift_transverse k z
    linarith
  have hJU : ∀ z, (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip
      (standardField (List.replicate (k + 1) Digit.two)) η
      (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip
        (standardField (List.replicate (k + 1) Digit.two)) η z := fun z => by
    have := twos_slip_drift_kernel k η z
    unfold ChildFrame.roundedSlip
    omega
  have hJV : ∀ z, (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip
      (standardField (List.replicate (k + 1) Digit.two)) η
      (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip
        (standardField (List.replicate (k + 1) Digit.two)) η z + η := fun z => by
    have := twos_slip_drift_transverse k η hη z
    unfold ChildFrame.roundedSlip
    omega
  exact FLatticePaper.EPolicy.rankWithIncrements_of_strict_hull hη (P := (frameAt (List.replicate (k + 1) Digit.two)).price
      (standardField (List.replicate (k + 1) Digit.two)))
    (J := (frameAt (List.replicate (k + 1) Digit.two)).roundedSlip (standardField (List.replicate (k + 1) Digit.two)) η)
    hPU hPV hJU hJV (fun x y hxy => ⟨hP x y hxy, hJ x y hxy⟩) hRU hRV hstr a c ha hc

/-- **`StrongResidual` at the twos word `2^(k+1)`, from its twos games with a deck rank.** -/
theorem strongResidual_twos_of_games (k : ℕ) (h : GamesWithRank (List.replicate (k + 1) Digit.two)) :
    StrongResidual (List.replicate (k + 1) Digit.two) :=
  strongResidual_twos_of_policy k (twos_F2F3_of_gamesWithRank k h)

end FLatticePaper.Induction
