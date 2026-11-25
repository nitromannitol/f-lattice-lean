import FLatticePaper.Plane.EarlierChainPrice
import FLatticePaper.Plane.Induction.PriceReflect
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.BaseMembership
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.OddFreeH
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.I3Application
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.SheetFacts

/-! Task w3, step 2 (the earlier trace at the conjugate), the values on the conjugate's free V cut.

Primes are for the conjugate frame `F' = frameAt (conjWord word)`, with `G = standardField (conjWord word)`, its creator shift
`σ' = shortShift`, its price displacement `v' = parentShift`, and `η = (frameAt word).eps`.

* `E1` (`earlierP_eq_price_add`): the earlier chain price is `Φ'_η(z) = P'(z) + D'_η(z − v')`, where
  `D'_η(y) = G y − G(y + ησ')`; it uses the orientation `ε_old = ε'` (`hEps`, checked on all proper words) and `a·σ' = 0`.
* `E2` (`price_vAt`, `price_one_add`): `P'(V'_j) = c₀'` for every `j` (`price_on_freeV`, zero transverse drift), and
  `P'((1,0) + m V') = c₀'` (`hTraceConj` at `(1,0)`, which is a free H point of the conjugate). -/

namespace FLatticePaper.EarlierV

open Farey FLatticePaper FLatticePaper.Induction

/-- **E1: the chain identity.** With the orientation of the earlier birth prefix equal to the conjugate's orientation. -/
theorem eps_old_eq_conj (word : Word) : (frameAt (oddBirthPrefix word)).eps = (frameAt (conjWord word)).eps :=
  (i3_eps_swap (oddBirthPrefix word)).symm

theorem earlierP_eq_price_add {word : Word} (z : Site) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps z =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z +
        (standardField (conjWord word) ((z - (frameAt (conjWord word)).parentShift)) -
          standardField (conjWord word) ((z - (frameAt (conjWord word)).parentShift) +
            (frameAt word).eps • (frameAt (conjWord word)).shortShift)) := by
  unfold FLatticePaper.earlierChainPrice Farey.earlierChainShift ChildFrame.price ChildFrame.parentSlope
  unfold ChildFrame.parentShift ChildFrame.shortShift Fraction.transverseGrade
  rw [eps_old_eq_conj word]
  set e' := (frameAt (conjWord word)).eps with he'
  set η := (frameAt word).eps with hη
  set D' := (frameAt (conjWord word)).parents.odd.den with hD'
  set N' := (frameAt (conjWord word)).parents.odd.num with hN'
  have hsite : z + (2 * η * e' * D' - e' * (N' - D'), 2 * η * e' * N' - e' * (N' + D')) =
      (z - (e' * (N' - D'), e' * (N' + D'))) + η • (2 * e' * D', 2 * e' * N') := by
    ext <;> simp <;> ring
  rw [hsite]
  ring

/-- The conjugate's transverse deck is its `Vdeck` (`(num − den, num + den)`). -/
theorem transverse_eq_vdeck (C : ChildFrame) : C.child.modifiedDeck.transverse = Vdeck C := by
  rw [PriceReflect.transverse_vec]
  rfl

/-- **E2a:** the conjugate's price is `c₀'` at every point of the labelled free V cut, for every ordinate `j ∈ ℤ`. -/
theorem price_vAt_eq {word : Word} (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (j : ℤ) :
    (frameAt (conjWord word)).price (standardField (conjWord word)) (FreeEnum.vAt (frameAt (conjWord word)) base j) =
      (frameAt (conjWord word)).cutPrice := by
  set C := frameAt (conjWord word) with hC
  have hp : 0 < FreeEnum.period C := FreeEnum.period_pos C
  have hvA : FreeEnum.vAt C base j = base (j % FreeEnum.period C) + (j / FreeEnum.period C) • Vdeck C := by
    unfold FreeEnum.vAt
    ext <;> simp
  have hmem := (hbase (j % FreeEnum.period C) (Int.emod_nonneg _ hp.ne') (Int.emod_lt_of_pos _ hp)).1
  rw [hvA, ← transverse_eq_vdeck C, ChainDeck.price_transverse_mul C hSE.packet (j / FreeEnum.period C)]
  exact PriceDeck.price_on_freeV C (standardField (conjWord word)) hSE.packet.strips hmem

/-- **E2b:** `P'((1,0) + m V') = c₀'`, from the conjugate's trace at the free H point `(1,0)` and the transverse drift. -/
theorem price_one_add {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
      (frameAt (conjWord word)).price (standardField (conjWord word)) w =
        (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1))
    (m : ℤ) :
    (frameAt (conjWord word)).price (standardField (conjWord word))
        (((1 : ℤ), (0 : ℤ)) + m • Vdeck (frameAt (conjWord word))) =
      (frameAt (conjWord word)).cutPrice := by
  set C := frameAt (conjWord word) with hC
  have hone : ((1 : ℤ), (0 : ℤ)) ∈ C.freeH := by
    have hz := origin_mem_freeV (frameAt word)
    have hN1 := frameAt_odd_num_pos h
    obtain ⟨hD, hN0, hNle, hodd⟩ := FLatticePaper.NativeGrade.odd_parent_facts (frameAt word)
    have hm := BaseMembership.base_mem_freeH h hz (le_refl 0) (by omega)
      (by
        rcases (frameAt word).eps_unit with he | he
        · right
          omega
        · left
          exact he)
    have e : ((1 : ℤ) + ((0 : ℤ), (0 : ℤ)).2, -((0 : ℤ), (0 : ℤ)).1) = ((1 : ℤ), (0 : ℤ)) := by
      simp
    rw [e] at hm
    exact hm
  rw [← transverse_eq_vdeck C, ChainDeck.price_transverse_mul C hSE.packet m]
  rw [hTraceConj _ hone, if_pos rfl]
  ring

end FLatticePaper.EarlierV
