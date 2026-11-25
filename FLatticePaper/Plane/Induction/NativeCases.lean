import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.Binary

/-! Task 72 / Q28, cases 2 and 3 of the native both-free exclusion. Two native free representatives `w0`, `w1` (free H or free V) with
`t(w1) − t(w0) + 2η = T k` (`NativeCongruence.t_congruence`), the `P`-displacement `h` at `w0` (`prescribedH`/`prescribedV` at `w0`) and the
`Q`-choice at `w1` equal to `−h`: these are impossible. The V-grade ranges are `ArcRanges.arc_even_range` / `arc_odd_range`, the endpoint
grades `tGrade_vFirst` / `tGrade_vLast`, the H spectrum is `hSpectrum`. -/

namespace FLatticePaper.NativeCases

open FLatticePaper FLatticePaper.Induction

/-- The grade parity of a site: `t ≡ x + y (mod 2)` for odd child numerator and denominator. -/
theorem tGrade_parity (frame : ChildFrame) (w : Site) : frame.tGrade w % 2 = (w.1 + w.2) % 2 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  unfold ChildFrame.tGrade
  rw [ha, hb]
  have e : (2 * a + 1) * w.1 - (2 * b + 1) * w.2 = 2 * (a * w.1 - b * w.2) + (w.1 - w.2) := by ring
  rw [e]
  omega

/-- The H-spectrum of an even free H site: `2 ≤ t ≤ L − 2`. -/
theorem freeH_even_bounds (frame : ChildFrame) {w : Site} (hw : w ∈ frame.freeH) (he : EvenSite w) :
    2 ≤ frame.tGrade w ∧ frame.tGrade w ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨-, -, hs⟩ := hw
  unfold ChildFrame.hSpectrum at hs
  have hp := tGrade_parity frame w
  have he' : (w.1 + w.2) % 2 = 0 := he
  rcases hs with h | h
  · exact ⟨h.2.1, h.2.2⟩
  · omega

/-- The H-spectrum of an odd free H site: `n ≤ t ≤ d`. -/
theorem freeH_odd_bounds (frame : ChildFrame) {w : Site} (hw : w ∈ frame.freeH) (ho : ¬ EvenSite w) :
    frame.child.num ≤ frame.tGrade w ∧ frame.tGrade w ≤ frame.child.den := by
  obtain ⟨-, -, hs⟩ := hw
  unfold ChildFrame.hSpectrum at hs
  have hp := tGrade_parity frame w
  have ho' : ¬ (w.1 + w.2) % 2 = 0 := ho
  rcases hs with h | h
  · omega
  · exact ⟨h.2.1, h.2.2⟩

/-- A multiple of the period `T` cannot lie strictly between `0` and `T`. -/
theorem mul_period_not_between (T k : ℤ) (hT : 0 < T) (h1 : 0 < T * k) (h2 : T * k < T) : False := by
  rcases le_or_gt k 0 with hk | hk
  · nlinarith
  · have : 1 ≤ k := hk
    nlinarith

/-- A multiple of the period `T` cannot lie in `[0, L]` for `L < T` unless it is `0`. -/
theorem mul_period_zero_of_small (T k L : ℤ) (hT : 0 < T) (hL : L < T) (h1 : 0 ≤ T * k) (h2 : T * k ≤ L) : T * k = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · nlinarith
  · simp [hk]
  · nlinarith

/-- A multiple of `T > 2` is not `±2`. -/
theorem period_mul_ne_pm_two (T k : ℤ) (hT : 2 < T) (h : T * k = 2 ∨ T * k = -2) : False := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk1 : k ≤ -1 := by omega
    rcases h with h | h <;> nlinarith
  · subst hk
    rcases h with h | h <;> simp at h
  · have hk1 : 1 ≤ k := by omega
    rcases h with h | h <;> nlinarith

/-- **Case 3, V against H.** A free V point `w0` and a free H point `w1` of the same parity, with `t(w1) − t(w0) + 2η = T k`, cannot have
the H-choice of `w1` (sign `−η`) equal to the opposite of the V-choice at `w0` (sign `η`). -/
theorem native_VH_false (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {w0 w1 : Site}
    (hw0 : w0 ∈ frame.freeV) (hw1 : w1 ∈ frame.freeH) (hpar : EvenSite w0 ↔ EvenSite w1) (k : ℤ)
    (hk : frame.tGrade w1 - frame.tGrade w0 + 2 * η = frame.child.periodDenominator * k)
    (hq : frame.prescribedH (-η) w1 = -(frame.prescribedV η w0)) : False := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hTL : frame.child.den + frame.child.num < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hTpos : 0 < frame.child.periodDenominator := by linarith
  have hηb : -1 ≤ η ∧ η ≤ 1 := by
    rcases hη with h | h <;> rw [h] <;> norm_num
  by_cases he0 : EvenSite w0
  · -- even V and even H
    have he1 : EvenSite w1 := hpar.mp he0
    have hpre1 : frame.prescribedH (-η) w1 = (1, 0) := BothFreeGrades.prescribedH_even_east frame (-η) w1 he1
    by_cases hF : w0 = vFirst
    · rw [hF, BothFreeGrades.prescribedV_vFirst, hpre1] at hq
      have h1 := congrArg Prod.fst hq
      norm_num at h1
    by_cases hL' : w0 = frame.vLast
    · have hne : vFirst ≠ frame.vLast := fun h => hF (hL'.trans h.symm)
      rw [hL', BothFreeGrades.prescribedV_vLast frame η hne, hpre1] at hq
      have h1 := congrArg Prod.fst hq
      have hη1 : η = -1 := by
        rcases hη with h | h
        · rw [h] at h1
          norm_num at h1
        · exact h
      have hmv := BothFreeGrades.tGrade_vLast frame
      have hm := freeH_even_bounds frame hw1 he1
      rw [hL', hmv] at hk
      rw [hη1] at hk
      have hpos : 0 < frame.child.periodDenominator * k := by linarith
      have hlt : frame.child.periodDenominator * k < frame.child.periodDenominator := by linarith
      exact mul_period_not_between frame.child.periodDenominator k hTpos hpos hlt
    · have hint := ArcRanges.arc_even_range frame hw0 he0 hF hL'
      have hm := freeH_even_bounds frame hw1 he1
      have hpos : 0 < frame.child.periodDenominator * k := by linarith
      have hlt : frame.child.periodDenominator * k < frame.child.periodDenominator := by linarith
      exact mul_period_not_between frame.child.periodDenominator k hTpos hpos hlt
  · -- odd V and odd H: the congruence excludes it
    have ho1 : ¬ EvenSite w1 := fun h => he0 (hpar.mpr h)
    have hint := ArcRanges.arc_odd_range frame hw0 he0
    have hm := freeH_odd_bounds frame hw1 ho1
    have hpos : 0 < frame.child.periodDenominator * k := by linarith
    have hlt : frame.child.periodDenominator * k < frame.child.periodDenominator := by linarith
    exact mul_period_not_between frame.child.periodDenominator k hTpos hpos hlt

/-- The H-prescription on an odd site: `(0, −η)` at `hFirst`, `(0, 1)` otherwise. -/
theorem prescribedH_odd_eq (frame : ChildFrame) (η : ℤ) {w : Site} (ho : ¬ EvenSite w) :
    frame.prescribedH η w = if w = hFirst then (0, -η) else (0, 1) := by
  unfold ChildFrame.prescribedH
  by_cases h1 : w = hFirst
  · simp [h1]
  · by_cases h2 : w = frame.hLast
    · simp [h2]
    · simp [h1, h2, ho]

/-- **Case 2, H against H.** Two free H points `w0`, `w1` of the same parity, with `t(w1) − t(w0) + 2η = T k`, cannot have the H-choice of
`w1` (sign `−η`) equal to the opposite of the H-choice of `w0` (sign `η`). -/
theorem native_HH_false (frame : ChildFrame) {η : ℤ} (hη : η = 1 ∨ η = -1) {w0 w1 : Site}
    (hw0 : w0 ∈ frame.freeH) (hw1 : w1 ∈ frame.freeH) (hpar : EvenSite w0 ↔ EvenSite w1) (k : ℤ)
    (hk : frame.tGrade w1 - frame.tGrade w0 + 2 * η = frame.child.periodDenominator * k)
    (hq : frame.prescribedH (-η) w1 = -(frame.prescribedH η w0)) : False := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hTL : frame.child.den + frame.child.num < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hTpos : 0 < frame.child.periodDenominator := by linarith
  have hηb : -1 ≤ η ∧ η ≤ 1 := by
    rcases hη with h | h <;> rw [h] <;> norm_num
  by_cases he0 : EvenSite w0
  · -- even H and even H: both choices are east, which are opposite only if they cancel
    have he1 : EvenSite w1 := hpar.mp he0
    rw [BothFreeGrades.prescribedH_even_east frame (-η) w1 he1,
      BothFreeGrades.prescribedH_even_east frame η w0 he0] at hq
    have h1 := congrArg Prod.fst hq
    norm_num at h1
  · have ho1 : ¬ EvenSite w1 := fun h => he0 (hpar.mpr h)
    have hm0 := freeH_odd_bounds frame hw0 he0
    have hm1 := freeH_odd_bounds frame hw1 ho1
    rw [prescribedH_odd_eq frame (-η) ho1, prescribedH_odd_eq frame η he0] at hq
    by_cases hF0 : w0 = hFirst
    · by_cases hF1 : w1 = hFirst
      · -- both at hFirst: the grades agree, so the congruence gives 2η = T k, impossible
        rw [hF0, hF1, sub_self] at hk
        have hT2 : 2 < frame.child.periodDenominator := by linarith
        rcases hη with h | h
        · exact period_mul_ne_pm_two frame.child.periodDenominator k hT2 (Or.inl (by linarith))
        · exact period_mul_ne_pm_two frame.child.periodDenominator k hT2 (Or.inr (by linarith))
      · -- w0 = hFirst (choice (0, -η)), w1 ordinary (choice (0,1)): the second component forces η = 1
        rw [hF0, if_neg hF1] at hq
        simp only [if_true] at hq
        have hη1 : η = 1 := by
          have h2 := congrArg Prod.snd hq
          simp at h2
          omega
        rw [hF0, BothFreeGrades.tGrade_hFirst frame] at hk
        rw [hη1] at hk
        have hpos : 0 < frame.child.periodDenominator * k := by linarith
        have hlt : frame.child.periodDenominator * k < frame.child.periodDenominator := by linarith
        exact mul_period_not_between frame.child.periodDenominator k hTpos hpos hlt
    · by_cases hF1 : w1 = hFirst
      · -- w1 = hFirst (choice (0, η)), w0 ordinary (choice (0,1)): the second component forces η = -1
        rw [hF1, if_neg hF0] at hq
        simp only [if_true] at hq
        have hη1 : η = -1 := by
          have h2 := congrArg Prod.snd hq
          simp at h2
          omega
        rw [hF1, BothFreeGrades.tGrade_hFirst frame] at hk
        rw [hη1] at hk
        have hpos : 0 < frame.child.periodDenominator * (-k) := by nlinarith
        have hlt : frame.child.periodDenominator * (-k) < frame.child.periodDenominator := by nlinarith
        exact mul_period_not_between frame.child.periodDenominator (-k) hTpos hpos hlt
      · rw [if_neg hF1, if_neg hF0] at hq
        have h1 := congrArg Prod.snd hq
        norm_num at h1

end FLatticePaper.NativeCases
