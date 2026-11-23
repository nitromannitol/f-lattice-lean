import FLatticePaper.Plane.Induction.TwosReciprocal
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.W1Hc

/-! Task 54 (1): the base value of the W0 exception. The reciprocal field `reciprocalField k` (the standard field of `3^k`,
child `1/(2k+3)`) takes the value `−1` at the canonical point `(1, −2)` (PAIR_INDUCTION, W0 exception: `G_(1/D)(2D+1) = −1`).
Proof: the deck reduction `(1, −2) = (2−m, m−1) + combine 0 (−1)` with `m = 2k+3` (`reciprocalField_reduction`), the literal
staircase value `stairEvenValue m (2−m, m−1) = −(k+1)(2k+1) + 1 − m` (no corner, the minimum is `1 − m`), and
`stairEvenConstantV m = −m(m+3)/2`, `transverseGrade (1/m) y = m y₂ − y₁`, `periodDenominator (1/m) = m² + 2m − 1`. -/

namespace FLatticePaper.W1Hexc

open Farey FLatticePaper FLatticePaper.Induction Construction
open FLatticePaper.W1Seeds

theorem reciprocal_canonical (k : ℕ) : reciprocalField k (1, -2) = -1 := by
  have hk : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hy : ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) ∈
      (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hpar : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  have hred : ((1 : ℤ), (-2 : ℤ)) = ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) +
      (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine 0 (-1) := by
    simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, PeriodDeck.combine, Fraction.unmodifiedDeck, hpar]
    ring_nf
  have h := reciprocalField_reduction k hy hred
  have hc : ¬ BaseMask.StairEvenCorner (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) := by
    unfold BaseMask.StairEvenCorner
    omega
  have hval : BaseMask.stairEvenValue (2 * (k : ℤ) + 3) ((2 - (2 * (k : ℤ) + 3)), ((2 * (k : ℤ) + 3) - 1)) =
      -((k + 1) * (2 * (k : ℤ) + 1)) + 1 - (2 * (k : ℤ) + 3) := by
    unfold BaseMask.stairEvenValue
    rw [if_neg hc]
    have hdiv : ((2 * (k : ℤ) + 3) - 1) * (((2 * (k : ℤ) + 3) - 1) - 1) / 2 = (k + 1) * (2 * (k : ℤ) + 1) := by
      rw [show ((2 * (k : ℤ) + 3) - 1) * (((2 * (k : ℤ) + 3) - 1) - 1) = 2 * ((k + 1) * (2 * (k : ℤ) + 1)) by ring]
      exact Int.mul_ediv_cancel_left _ two_ne_zero
    rw [hdiv, min_eq_left (by omega)]
    ring
  have hcV : stairEvenConstantV (2 * (k : ℤ) + 3) = -((2 * (k : ℤ) + 3) * (k + 3)) := by
    rw [stairEvenConstantV_eq]
    congr 1
    rw [show (2 * (k : ℤ) + 3) * ((2 * (k : ℤ) + 3) + 3) = 2 * ((2 * (k : ℤ) + 3) * (k + 3)) by ring]
    exact Int.mul_ediv_cancel_left _ two_ne_zero
  rw [hval, hcV] at h
  simp only [Fraction.transverseGrade, Fraction.periodDenominator] at h
  have key : 2 * reciprocalField k (1, -2) = 2 * (-1) := by
    rw [h]
    ring
  linarith

/-- The parent registers of `2^k`: the odd register is `k/(k+1)`, the even register is `1/1`. -/
theorem parentsAt_replicate_two (k : ℕ) :
    (parentsAt (List.replicate k Digit.two)).odd = ⟨(k : ℤ), (k : ℤ) + 1⟩ ∧
      (parentsAt (List.replicate k Digit.two)).even = ⟨1, 1⟩ := by
  induction k with
  | zero =>
    simp only [List.replicate_zero]
    exact ⟨by show root.odd = _; simp [root], by show root.even = _; simp [root]⟩
  | succ k ih =>
    obtain ⟨ho, he⟩ := ih
    rw [List.replicate_succ', parentsAt_append_singleton]
    constructor
    · show (parentsAt (List.replicate k Digit.two)).current .odd = _
      simp only [Parents.current, Parents.combine, ho, he]
      congr 1 <;> push_cast <;> ring
    · exact he

/-- The current odd fraction determines the word (the birth injectivity of `parentsAt_injective`). -/
theorem current_odd_injective {a b : Word} (h : (parentsAt a).current .odd = (parentsAt b).current .odd) : a = b := by
  have hodd : Birth.fraction (a, .odd) = Birth.fraction (b, .odd) := by
    change (parentsAt a).current .odd = (parentsAt b).current .odd
    exact h
  exact congrArg Prod.fst (Birth.fraction_injective hodd)

/-- **The W0 exception word.** If the odd parent of a proper word `w` is `(D−1)/D` with `D − 2 = k`, its odd birth prefix is
`2^k`, so its conjugate is the pure-3 word `3^k` (the base case of PAIR_INDUCTION's W0 exception). -/
theorem oddBirthPrefix_exception {w : Word} (hw : ∃ x ∈ w, x ≠ Digit.three) (k : ℕ)
    (hk : (frameAt w).parents.odd.den = (k : ℤ) + 2) (hN : (frameAt w).parents.odd.num = (k : ℤ) + 1) :
    oddBirthPrefix w = List.replicate k Digit.two := by
  apply current_odd_injective
  rw [← parentsAt_odd_eq hw]
  have h1 : (parentsAt (List.replicate k Digit.two)).current .odd = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
    obtain ⟨ho, he⟩ := parentsAt_replicate_two k
    simp only [Parents.current, Parents.combine, ho, he]
    congr 1 <;> push_cast <;> ring
  rw [h1]
  have hodd : (parentsAt w).odd = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
    have hd : (frameAt w).parents.odd = (parentsAt w).odd := rfl
    rw [← hd]
    ext
    · exact hN
    · exact hk
  exact hodd


/-- The kernel of the reciprocal child `1/m`, `m = 2k+3`, is `(m, 1)` (its multiplicity is one). -/
theorem reciprocal_kernel (k : ℕ) : (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.kernel = (2 * (k : ℤ) + 3, 1) := by
  have hpar : (1 + (2 * (k : ℤ) + 3)) % 2 = 0 := by omega
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hpar, Fraction.unmodifiedDeck]

/-- The reciprocal field is periodic under its kernel `(m, 1)` (zero character). -/
theorem reciprocal_periodic (k : ℕ) : Function.Periodic (reciprocalField k) (2 * (k : ℤ) + 3, 1) := by
  intro z
  have h := (reciprocalField_spec k).2.1 z
  rw [reciprocal_kernel k, add_zero] at h
  exact h

/-- **hExc (the W0 exception value, discharged).** For a proper word `w` with `ε = −1` and `D − N = 1`, the conjugate is
`3^k` (`k = D − 2`), and `Fp(y*) = h0(y*) − 1` at the reduced point `y*`: the reduced point is the canonical point `(1, −2)`
shifted by `(δ − 2)` kernels, `δ = d − n`, and `reciprocal_canonical` gives `−1`. -/
theorem hExc_exception {w : Word} (hw : ∃ x ∈ w, x ≠ Digit.three)
    (hE : (frameAt w).eps = -1) (hX : (frameAt w).parents.odd.den - (frameAt w).parents.odd.num = 1) :
    quarterTurnField (standardField (conjWord w)) ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) = harmonicGrid ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) - 1 := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := (frameAt w).child_facts
  have hchild3 : 3 ≤ (frameAt w).child.num := child_num_ge_three hw
  have hN0 : 0 ≤ (frameAt w).parents.odd.num := (frameAt w).valid.odd_bounds.2.1
  have hc : (frameAt w).parents.odd.num * (frameAt w).child.den - (frameAt w).parents.odd.den * (frameAt w).child.num = -1 := by
    have h := (frameAt w).eps_eq
    rw [hE] at h
    linarith
  have hD2 : 2 ≤ (frameAt w).parents.odd.den := by
    by_contra hlt
    have h1 : (frameAt w).parents.odd.den = 1 := by omega
    have h2 : (frameAt w).parents.odd.num = 0 := by omega
    rw [h1, h2] at hc
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (frameAt w).parents.odd.den - 2 :=
    ⟨((frameAt w).parents.odd.den - 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hkD : (frameAt w).parents.odd.den = (k : ℤ) + 2 := by omega
  have hkN : (frameAt w).parents.odd.num = (k : ℤ) + 1 := by omega
  have hpref := oddBirthPrefix_exception hw k hkD hkN
  have hconj : conjWord w = List.replicate k Digit.three := by
    unfold conjWord
    rw [hpref, List.map_replicate]
    rfl
  rw [hconj, standardField_threes]
  unfold quarterTurnField
  rw [quarterTurn_site]
  have hZ : ((-(((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)), (-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num) - 1) : Site) = (1, -2) + (((frameAt w).child.den - (frameAt w).child.num - 2)) •
      ((2 * (k : ℤ) + 3), 1) := by
    rw [hkD, hkN] at hc ⊢
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_mk, smul_eq_mul]
      linear_combination (-1 : ℤ) * hc
    · simp only [Prod.snd_add, Prod.smul_mk, smul_eq_mul]
      linear_combination hc
  have hG := reciprocal_periodic k
  have hper := hG.zsmul ((frameAt w).child.den - (frameAt w).child.num - 2) (1, -2)
  rw [← hZ] at hper
  rw [hper, reciprocal_canonical]
  ring

/-- **hC with no named input (task 54).** The sign at the seed point for a proper word from the conjugate's packet alone. -/
theorem hC_full {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hpk : (frameAt (conjWord w)).Packet (standardField (conjWord w))) :
    0 ≤ (frameAt w).sheetC (quarterTurnField (standardField (conjWord w))) (seedPoint (frameAt w)) :=
  W1Hc.hC_of_packet hproper hpk (fun hE hX => hExc_exception hproper hE hX)

/-- **The even seed from the packet, with every named input discharged except the inherited seed of the conjugate (task 54).** -/
theorem even_zero_full {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hpar : SeedFields (conjWord w))
    (hconj : (frameAt (conjWord w)).Packet (standardField (conjWord w)))
    (hO : OpenInputs w) :
    ∀ z : Site, EvenSite z →
      (frameAt w).tGrade z = 2 - ((frameAt w).child.den + (frameAt w).child.num) → standardField w z = 0 :=
  W1Hc.even_zero_of_packet_hc hproper hpar hconj hO (fun hE hX => hExc_exception hproper hE hX)

/-- **The odd-field sheet identity by transport (task 54, item 3).** The odd field of an even word `w` is
`quarterTurnField (standardField w) = G_w∘Z + h0`; transporting `standardField_eq_sheetMin` of `w` through
`quarterTurn_eq` gives its sheet identity on `Z⁻¹E_w`, with the offers of `w` (the odd parent field `Fp_w`, not the
even parent field of the PAIR odd-child step). -/
theorem odd_field_sheet_transport {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hM : RespectsPeriodsOn (frameAt w).child (frameAt w).coherentConstantU (frameAt w).coherentConstantV
      (frameAt w).closedPolygon ((frameAt w).sheetMin (quarterTurnField (standardField (conjWord w)))))
    (x : Site) (hx : QuarterTurn.counterclockwise.mapSite (0, -1) x ∈ (frameAt w).closedPolygon) :
    quarterTurnField (standardField w) x =
      (frameAt w).sheetMin (quarterTurnField (standardField (conjWord w)))
        (QuarterTurn.counterclockwise.mapSite (0, -1) x) + harmonicGrid x := by
  have key := standardField_eq_sheetMin hproper hx hM
  show standardField w (QuarterTurn.counterclockwise.mapSite (0, -1) x) + harmonicGrid x = _
  rw [key]

end FLatticePaper.W1Hexc
