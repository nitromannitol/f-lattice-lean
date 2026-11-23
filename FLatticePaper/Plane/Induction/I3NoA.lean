import FLatticePaper.Plane.Induction.I3Restricted
import FLatticePaper.Plane.Induction.I3Permits

/-! Task 38: the restricted no-fort condition of the sheet `A` (the field `noA` of `SheetLocalInputs`).

The earlier word's rank (the phase-`η` policy, weights `(1, 1)`) pulled back by the quarter turn is a constrained burning rank
for the `Ξ`-permits: its quota, its strict decrease along the policy, and the monotonicity of the policy inside the
`Ξ`-permit relation. Its increments along the deck of the word are `η` and `1`, the increments of the grade `i3aGrade`
(from the price and slip drifts of the earlier word). The least-rank argument then gives `RestrictedNoFort`.

The lattice identities `mulI(K_odd) = T_child`, `mulI(T_odd) = −K_child` hold for an odd parent (`i3_mulI_kernel_odd`,
`i3_mulI_transverse_odd`, from the modified decks). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The quarter-turn offset is affine: `Z (x + k) = Z x + mulI k`. -/
theorem i3Z_add (x k : Site) : i3Z (x + k) = i3Z x + mulI k := by
  unfold i3Z mulI
  ext
  · simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [Prod.fst_add, Prod.snd_add]
    ring

/-- For an odd fraction, `mulI` of the kernel of the modified deck is the transverse of the rotated fraction. -/
theorem i3_mulI_kernel_odd (f : Fraction) (hodd : f.Odd) :
    mulI f.modifiedDeck.kernel = f.rotate.modifiedDeck.transverse := by
  have h1 : (f.num + f.den) % 2 = 1 := hodd
  have hr : f.rotate = ⟨f.den - f.num, f.den + f.num⟩ := Fraction.rotate_of_odd hodd
  have hm : f.periodMultiplicity = 2 := by
    unfold Fraction.periodMultiplicity
    exact if_neg (by omega)
  have hm' : (⟨f.den - f.num, f.den + f.num⟩ : Fraction).periodMultiplicity = 1 := by
    unfold Fraction.periodMultiplicity
    exact if_pos (by show ((f.den - f.num) + (f.den + f.num)) % 2 = 0; omega)
  rw [hr]
  simp only [mulI, Fraction.modifiedDeck, Fraction.unmodifiedDeck, hm, hm']
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- For an odd fraction, `mulI` of the transverse of the modified deck is minus the kernel of the rotated fraction. -/
theorem i3_mulI_transverse_odd (f : Fraction) (hodd : f.Odd) :
    mulI f.modifiedDeck.transverse = -f.rotate.modifiedDeck.kernel := by
  have h1 : (f.num + f.den) % 2 = 1 := hodd
  have hr : f.rotate = ⟨f.den - f.num, f.den + f.num⟩ := Fraction.rotate_of_odd hodd
  have hm' : (⟨f.den - f.num, f.den + f.num⟩ : Fraction).periodMultiplicity = 1 := by
    unfold Fraction.periodMultiplicity
    exact if_pos (by show ((f.den - f.num) + (f.den + f.num)) % 2 = 0; omega)
  rw [hr]
  simp only [mulI, Fraction.modifiedDeck, Fraction.unmodifiedDeck, hm']
  refine Prod.ext ?_ ?_ <;> simp
  ring

/-- The kernel of the word's odd deck, rotated by `mulI`, is the transverse period of the earlier child. -/
theorem i3_child_kernel {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) :
    mulI (parentsAt word).odd.modifiedDeck.kernel =
      (frameAt (conjWord word)).child.modifiedDeck.transverse := by
  have hc : (frameAt (conjWord word)).child = (parentsAt word).odd.rotate := frameAt_conj_child hw
  rw [hc]
  exact i3_mulI_kernel_odd _ (parentsAt_valid word).odd_parity

/-- The transverse of the word's odd deck, rotated by `mulI`, is minus the kernel of the earlier child. -/
theorem i3_child_transverse {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) :
    mulI (parentsAt word).odd.modifiedDeck.transverse =
      -(frameAt (conjWord word)).child.modifiedDeck.kernel := by
  have hc : (frameAt (conjWord word)).child = (parentsAt word).odd.rotate := frameAt_conj_child hw
  rw [hc]
  exact i3_mulI_transverse_odd _ (parentsAt_valid word).odd_parity

/-- The grade `i3aGrade` is the price plus the rounded slip at the quarter-turned site. -/
theorem i3aGrade_eq (word : Word) (x : Site) :
    i3aGrade word x = (frameAt (conjWord word)).price (standardField (conjWord word)) (i3Z x) +
      (frameAt (conjWord word)).roundedSlip (standardField (conjWord word)) (frameAt word).eps (i3Z x) := by
  unfold i3aGrade ChildFrame.cutGrade i3Z
  ring

/-- The grade increases by the chain sign `η = eps(word)` along the kernel of the word's odd deck. -/
theorem i3aGrade_kernel {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongEstimates (conjWord word))
    (x : Site) :
    i3aGrade word (x + (parentsAt word).odd.modifiedDeck.kernel) = i3aGrade word x + (frameAt word).eps := by
  have hid := i3_child_kernel hw
  have hη := (frameAt word).eps_unit
  have hz : i3Z (x + (parentsAt word).odd.modifiedDeck.kernel) =
      i3Z x + (frameAt (conjWord word)).child.modifiedDeck.transverse := by
    rw [i3Z_add, hid]
  rw [i3aGrade_eq, i3aGrade_eq, hz]
  have hp := (hS.priceDrift (i3Z x)).2
  have hs := (hS.slipDrift (frameAt word).eps hη (i3Z x)).2
  unfold ChildFrame.roundedSlip
  omega

/-- The grade increases by `1` along the transverse of the word's odd deck. -/
theorem i3aGrade_transverse {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongEstimates (conjWord word))
    (x : Site) :
    i3aGrade word (x + (parentsAt word).odd.modifiedDeck.transverse) = i3aGrade word x + 1 := by
  have hid := i3_child_transverse hw
  have hη := (frameAt word).eps_unit
  have hz : i3Z (x + (parentsAt word).odd.modifiedDeck.transverse) =
      i3Z x + -(frameAt (conjWord word)).child.modifiedDeck.kernel := by
    rw [i3Z_add, hid]
  rw [i3aGrade_eq, i3aGrade_eq, hz]
  have hp := (hS.priceDrift (i3Z x + -(frameAt (conjWord word)).child.modifiedDeck.kernel)).1
  rw [neg_add_cancel_right] at hp
  have hs := (hS.slipDrift (frameAt word).eps hη (i3Z x + -(frameAt (conjWord word)).child.modifiedDeck.kernel)).1
  rw [neg_add_cancel_right] at hs
  unfold ChildFrame.roundedSlip
  omega

/-- **The restricted no-fort condition of the sheet `A`** at a proper word, from the strong estimates of the earlier word: the
constrained rank of the `Ξ`-permits, with increments `η` and `1` along the odd deck, which are the increments of `i3aGrade`. -/
theorem i3_noA_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (h : StrongEstimates (conjWord word)) :
    RestrictedNoFort (quarterTurnField (standardField (conjWord word))) (i3aGrade word)
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) := by
  have hη := (frameAt word).eps_unit
  obtain ⟨policy, hq, hmono, hrank⟩ := h.F2F3_policy (frameAt word).eps hη
  obtain ⟨rk, lam, hlam, hstrict, hU, hV⟩ := hrank 1 1 zero_lt_one zero_lt_one
  have hK : ∀ x, rk (i3Z (x + (parentsAt word).odd.modifiedDeck.kernel)) - rk (i3Z x) =
      lam * (i3aGrade word (x + (parentsAt word).odd.modifiedDeck.kernel) - i3aGrade word x) := by
    intro x
    rw [i3aGrade_kernel hw h x, i3Z_add, i3_child_kernel hw, hV (i3Z x)]
    ring
  have hT : ∀ x, rk (i3Z (x + (parentsAt word).odd.modifiedDeck.transverse)) - rk (i3Z x) =
      lam * (i3aGrade word (x + (parentsAt word).odd.modifiedDeck.transverse) - i3aGrade word x) := by
    intro x
    rw [i3aGrade_transverse hw h x, i3Z_add, i3_child_transverse hw]
    have hU' := hU (i3Z x + -(frameAt (conjWord word)).child.modifiedDeck.kernel)
    rw [neg_add_cancel_right] at hU'
    have e : i3aGrade word x + 1 - i3aGrade word x = 1 := by ring
    rw [e]
    linarith
  have hbin : ∀ c, laplacian (quarterTurnField (standardField (conjWord word))) c = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) c = 0 :=
    fun c => quarterTurnField_binary h.packet.binary c
  have hT_perm := i3_retainQuota_quarterTurn _ policy hq
  have hcon_T : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word)))
      (fun x => rk (i3Z x)) (fun c i => policy (i3Z c) (i3Z i)) :=
    isConstrainedBurningRank_of_strict_quota hbin hT_perm (fun c i _ hp => hstrict (i3Z c) (i3Z i) hp)
  have hle : ∀ c i, (fun c i => policy (i3Z c) (i3Z i)) c i →
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c) c i := by
    intro c i hp
    show sheetChainPotential word (standardField (conjWord word)) i ≤
      sheetChainPotential word (standardField (conjWord word)) c
    rw [i3_sheet_eq_chainPotential, i3_sheet_eq_chainPotential]
    exact hmono (i3Z c) (i3Z i) hp
  have hcon := IsConstrainedBurningRank.mono hcon_T hle
  have hint : (parentsAt word).odd.InUnitInterval := (parentsAt_valid word).odd_bounds
  exact restrictedNoFort_of_constrained_rankGrade (Fraction.det_modifiedDeck_pos hint) (fun x => rk (i3Z x)) lam hlam
    hcon hK hT

end FLatticePaper.Induction
