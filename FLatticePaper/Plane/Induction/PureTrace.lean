import FLatticePaper.Plane.Induction.PureBasePrice
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.ReciprocalInputs
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Construction.BaseMasks

/-! Task w3, B: the trace of the pure words `3^k`.

The reciprocal field agrees with the stair-even tile (`reciprocalField_spec`), whose height is `stairEvenValue`. The free H arc of
the reciprocal frame `1/(2k+3)` is `{(a,0) : 1 ≤ a ≤ d}` (the polygon inequalities with `t = a − d m`, `s = (d+1)t + m T`). On the arc,
`P(a,0) = F(a,0) − F(a−1,1) = min(a−1,0) − min(a−2,0)`, which is `1` at `a = 1` and `0` otherwise, and the cut price is `1`. -/

namespace FLatticePaper.PureTrace

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Construction

theorem field_at_tile (k : ℕ) (p : Site) (hp : p ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites) :
    reciprocalField k p = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) p := by
  have h := (reciprocalField_spec k).1 ⟨p, hp⟩
  rw [BaseMask.stairEven_raw_height] at h
  simpa using h.symm

theorem cutPrice_threes (k : ℕ) : (frameAt (List.replicate k Digit.three)).cutPrice = 1 := by
  have hN := frameAt_threes_parentSlope k (1, 0)
  have hD := frameAt_threes_parentSlope k (0, 1)
  unfold ChildFrame.parentSlope at hN hD
  simp only [] at hN hD
  have hnum : (frameAt (List.replicate k Digit.three)).parents.odd.num = 0 := by
    have := hN
    simp at this
    exact this
  have hden : (frameAt (List.replicate k Digit.three)).parents.odd.den = 1 := by
    have := hD
    simp at this
    linarith
  unfold ChildFrame.cutPrice Fraction.periodDenominator
  rw [frameAt_threes_eps, hnum, hden]
  norm_num

/-- The free H arc of `1/(2k+3)` lies on the row `y = 0` with abscissae `1..2k+3`. -/
theorem freeH_reciprocal (k : ℕ) {z : Site} (hz : z ∈ (reciprocalFrame k).freeH) :
    z.2 = 0 ∧ 1 ≤ z.1 ∧ z.1 ≤ 2 * (k : ℤ) + 3 := by
  obtain ⟨-, -, -, -, hT⟩ := (reciprocalFrame k).child_facts
  have hc := reciprocalFrame_child k
  have hnum : (reciprocalFrame k).child.num = 1 := by rw [hc]
  have hden : (reciprocalFrame k).child.den = 2 * (k : ℤ) + 3 := by rw [hc]
  obtain ⟨hcp, -, hspec⟩ := hz
  have hT' : (reciprocalFrame k).child.periodDenominator =
      (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3) + 2 * (2 * (k : ℤ) + 3) - 1 := by
    rw [hT, hnum, hden]
    ring
  -- the polygon: the s-grade lies in `[3 − d, T + d − 1]` (both parities)
  have hs : 3 - (2 * (k : ℤ) + 3) ≤ (reciprocalFrame k).sGrade z ∧
      (reciprocalFrame k).sGrade z ≤ (reciprocalFrame k).child.periodDenominator + (2 * (k : ℤ) + 3) - 1 := by
    unfold ChildFrame.closedPolygon at hcp
    simp only [Set.mem_setOf_eq] at hcp
    by_cases he : EvenSite z
    · rw [if_pos he] at hcp
      constructor <;> omega
    · rw [if_neg he] at hcp
      constructor <;> omega
  -- the t-grade lies in `[1, d]`
  have ht : 1 ≤ (reciprocalFrame k).tGrade z ∧ (reciprocalFrame k).tGrade z ≤ 2 * (k : ℤ) + 3 := by
    unfold ChildFrame.hSpectrum at hspec
    rw [hnum, hden] at hspec
    omega
  -- the identity `s = (d+1) t + m T`
  have hid : (reciprocalFrame k).sGrade z = (2 * (k : ℤ) + 3 + 1) * (reciprocalFrame k).tGrade z +
      z.2 * ((2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3) + 2 * (2 * (k : ℤ) + 3) - 1) := by
    unfold ChildFrame.sGrade ChildFrame.tGrade
    rw [hnum, hden]
    ring
  rw [hT'] at hs
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hTnn : (0 : ℤ) ≤ (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3) + 2 * (2 * (k : ℤ) + 3) - 1 := by nlinarith
  have hz2 : z.2 = 0 := by
    rcases lt_trichotomy z.2 0 with hm | hm | hm
    · exfalso
      have h1 : (2 * (k : ℤ) + 3 + 1) * (reciprocalFrame k).tGrade z ≤ (2 * (k : ℤ) + 3 + 1) * (2 * (k : ℤ) + 3) :=
        mul_le_mul_of_nonneg_left ht.2 (by omega)
      have h2 : 0 ≤ (-z.2 - 1) * ((2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3) + 2 * (2 * (k : ℤ) + 3) - 1) :=
        mul_nonneg (by omega) hTnn
      nlinarith
    · exact hm
    · exfalso
      have h1 : (2 * (k : ℤ) + 3 + 1) * 1 ≤ (2 * (k : ℤ) + 3 + 1) * (reciprocalFrame k).tGrade z :=
        mul_le_mul_of_nonneg_left ht.1 (by omega)
      have h2 : 0 ≤ (z.2 - 1) * ((2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 3) + 2 * (2 * (k : ℤ) + 3) - 1) :=
        mul_nonneg (by omega) hTnn
      nlinarith
  have htz : (reciprocalFrame k).tGrade z = z.1 := by
    unfold ChildFrame.tGrade
    rw [hnum, hden, hz2]
    ring
  rw [htz] at ht
  exact ⟨hz2, ht.1, ht.2⟩

/-- The stair-even corner indicator at the row `(a, 0)` with `a ≥ 1` is zero. -/
theorem corner_row (d a : ℤ) (ha : 1 ≤ a) (hd : 3 ≤ d) : ¬ BaseMask.StairEvenCorner d (a, 0) := by
  unfold BaseMask.StairEvenCorner
  intro h
  rcases h with h | h <;> (simp at h; try omega)

/-- The stair-even corner indicator at `(a − 1, 1)` with `1 ≤ a ≤ d` is zero. -/
theorem corner_second (d a : ℤ) (ha' : a ≤ d) :
    ¬ BaseMask.StairEvenCorner d (a - 1, 1) := by
  unfold BaseMask.StairEvenCorner
  intro h
  rcases h with h | h <;> (simp at h; try omega)

theorem value_row (d a : ℤ) (ha : 1 ≤ a) (hd : 3 ≤ d) : BaseMask.stairEvenValue d (a, 0) = min (a - 1) 0 := by
  unfold BaseMask.stairEvenValue
  rw [if_neg (corner_row d a ha hd)]
  simp

theorem value_second (d a : ℤ) (ha' : a ≤ d) :
    BaseMask.stairEvenValue d (a - 1, 1) = min (a - 2) 0 := by
  unfold BaseMask.stairEvenValue
  rw [if_neg (corner_second d a ha')]
  have e : a - 1 - 1 = a - 2 := by ring
  simp [e]

/-- **The trace of the pure word `3^k`.** On the free H arc `(a,0)`, `P = 1` at `a = 1` and `0` otherwise. -/
theorem traceAt_threes (k : ℕ) : TraceFromPsi.TraceAt (List.replicate k Digit.three) := by
  unfold TraceFromPsi.TraceAt
  intro z hz
  obtain ⟨a, b⟩ := z
  have hfr : frameAt (List.replicate k Digit.three) = reciprocalFrame k := rfl
  have hz' := hz
  rw [hfr] at hz'
  obtain ⟨hb, ha1, ha2⟩ := freeH_reciprocal k hz'
  simp only at hb ha1 ha2
  subst hb
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have mz : ((a, 0) : Site) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hp' : ((a - 1, 1) : Site) ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  have hsub : ((a, 0) : Site) - ((1 : ℤ), (-1 : ℤ)) = (a - 1, 1) := by
    ext <;> simp
  rw [standardField_threes, price_threes, cutPrice_threes, hsub, field_at_tile k _ mz, field_at_tile k _ hp',
    value_row _ _ ha1 hd, value_second _ _ ha2]
  by_cases h1 : a = 1
  · subst h1
    norm_num
  · have hne : ((a, 0) : Site) ≠ ((1 : ℤ), (0 : ℤ)) := by
      intro e
      apply h1
      exact congrArg Prod.fst e
    rw [if_neg hne, min_eq_right (show (0 : ℤ) ≤ a - 1 by omega), min_eq_right (show (0 : ℤ) ≤ a - 2 by omega)]
    norm_num

end FLatticePaper.PureTrace
