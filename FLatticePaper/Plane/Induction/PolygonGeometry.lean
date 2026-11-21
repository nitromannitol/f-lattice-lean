import FLatticePaper.Plane.Induction.Sheets

namespace FLatticePaper.Induction
open Farey

namespace ChildFrame
variable (frame : ChildFrame)

/-- The arithmetic of the even child: `0 < n < d - 2`-type bounds, `d ≥ 3`, and `T = d² + 2dn − n²`. -/
theorem child_facts :
    0 < frame.child.num ∧ frame.child.num < frame.child.den ∧ 2 ≤ frame.child.den - frame.child.num ∧
      3 ≤ frame.child.den ∧
      frame.child.periodDenominator
        = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
  have hint : frame.child.Interior := frame.valid.current_interior .even
  have hev : frame.child.Even := frame.child_even
  obtain ⟨hn, hnd⟩ := hint
  unfold Fraction.Even at hev
  refine ⟨hn, hnd, by omega, by omega, rfl⟩

/-- Membership in `E` in terms of the parity and the grades. -/
theorem mem_closedPolygon_iff (z : Site) :
    z ∈ frame.closedPolygon ↔
      (EvenSite z ∧ 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
          frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧ 0 ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∨
      (¬ EvenSite z ∧ frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
          frame.tGrade z ≤ frame.child.den ∧ 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
  unfold ChildFrame.closedPolygon
  by_cases h : EvenSite z
  · simp only [Set.mem_setOf_eq, if_pos h]
    exact ⟨fun h' => Or.inl ⟨h, h'⟩, fun h' => h'.elim (fun h2 => h2.2) (fun h2 => absurd h h2.1)⟩
  · simp only [Set.mem_setOf_eq, if_neg h]
    exact ⟨fun h' => Or.inr ⟨h, h'⟩, fun h' => h'.elim (fun h2 => absurd h2.1 h) (fun h2 => h2.2)⟩

/-- Membership of a translate `z + i U + j V` in `E`, in the grades of `z`. -/
theorem mem_translate_iff (z : Site) (i j : ℤ) :
    z + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon ↔
      (EvenSite z ∧ 2 - frame.child.periodDenominator ≤ frame.tGrade z - j * frame.child.periodDenominator ∧
          frame.tGrade z - j * frame.child.periodDenominator ≤ frame.child.den + frame.child.num - 2 ∧
          0 ≤ frame.sGrade z + i * frame.child.periodDenominator ∧
          frame.sGrade z + i * frame.child.periodDenominator ≤
            frame.child.periodDenominator + 2 * frame.child.num) ∨
      (¬ EvenSite z ∧ frame.child.num - frame.child.periodDenominator ≤
          frame.tGrade z - j * frame.child.periodDenominator ∧
          frame.tGrade z - j * frame.child.periodDenominator ≤ frame.child.den ∧
          2 - frame.child.den + frame.child.num ≤ frame.sGrade z + i * frame.child.periodDenominator ∧
          frame.sGrade z + i * frame.child.periodDenominator ≤
            frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
  rw [frame.mem_closedPolygon_iff, frame.evenSite_add_combine, frame.tGrade_add_combine,
    frame.sGrade_add_combine]

end ChildFrame

/-- The inequalities of the parity rectangle, for `0 < n < d`, `2 ≤ d − n`, `d ≥ 3`. -/
theorem T_bounds {N D : ℤ} (hN : 0 < N) (hdiff : 2 ≤ D - N) (hD : 3 ≤ D) :
    D + N - 4 < D ^ 2 + 2 * D * N - N ^ 2 ∧ D - N < D ^ 2 + 2 * D * N - N ^ 2 ∧
      2 * N + 2 ≤ D ^ 2 + 2 * D * N - N ^ 2 ∧ 2 * D - 4 < D ^ 2 + 2 * D * N - N ^ 2 ∧
      D - N + 2 ≤ D ^ 2 + 2 * D * N - N ^ 2 ∧ 2 * D - 2 * N - 2 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by
  have e : D ^ 2 + 2 * D * N - N ^ 2 = (D - N - 2) * (D + N) + 2 * (D + N) + 2 * (D * N) := by ring
  have h1 : 0 ≤ (D - N - 2) * (D + N) := mul_nonneg (by omega) (by omega)
  have h3 : 3 * N ≤ D * N := by nlinarith
  rw [e]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- A two-sided bound on an integer multiple of `T` in a window of width below `2T`. -/
theorem abs_le_one_of_mul (i T W : ℤ) (hT : 0 < T) (h1 : i * T ≤ W) (h2 : -(i * T) ≤ W)
    (hW : W < 2 * T) : -1 ≤ i ∧ i ≤ 1 := by
  constructor
  · by_contra h
    have h' := not_le.mp h
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -i - 2 by omega) hT.le]
  · by_contra h
    have h' := not_le.mp h
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ i - 2 by omega) hT.le]

/-- Some `j ∈ {-1, 0, 1}` moves `t0` into a window `[A, B]` of width at least `T - 1`, provided `t0` is
within one period of the window. -/
theorem exists_small_shift (t0 A B T : ℤ) (hw : A + T ≤ B + 1) (hrange : A - T ≤ t0 ∧ t0 ≤ B + T) :
    ∃ j : ℤ, (j = -1 ∨ j = 0 ∨ j = 1) ∧ A ≤ t0 - j * T ∧ t0 - j * T ≤ B := by
  have h : (A ≤ t0 ∧ t0 ≤ B) ∨ (A ≤ t0 - T ∧ t0 - T ≤ B) ∨ (A ≤ t0 + T ∧ t0 + T ≤ B) := by
    omega
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, Or.inr (Or.inl rfl), by linarith, by linarith⟩
  · exact ⟨1, Or.inr (Or.inr rfl), by linarith, by linarith⟩
  · exact ⟨-1, Or.inl rfl, by linarith, by linarith⟩

namespace ChildFrame
variable (frame : ChildFrame)

theorem tGrade_sub_x (z : Site) :
    frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
  unfold ChildFrame.tGrade
  ring

theorem tGrade_add_x (z : Site) :
    frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
  unfold ChildFrame.tGrade
  ring

theorem sGrade_sub_x (z : Site) :
    frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

theorem sGrade_add_x (z : Site) :
    frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

theorem tGrade_sub_y (z : Site) :
    frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
  unfold ChildFrame.tGrade
  ring

theorem tGrade_add_y (z : Site) :
    frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
  unfold ChildFrame.tGrade
  ring

theorem sGrade_sub_y (z : Site) :
    frame.sGrade (z.1, z.2 - 1) = frame.sGrade z - (frame.child.den - frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

theorem sGrade_add_y (z : Site) :
    frame.sGrade (z.1, z.2 + 1) = frame.sGrade z + (frame.child.den - frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

end ChildFrame

/-- Duplicate pairs of `E`: two sites of `E` in one deck class differ by at most one generator in each direction,
and a nonzero shift places them in the opposite bands. -/
theorem ChildFrame.closedPolygon_pair (frame : ChildFrame) {z : Site} {i j : ℤ}
    (hz : z ∈ frame.closedPolygon) (hz' : z + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon) :
    (i = -1 ∨ i = 0 ∨ i = 1) ∧ (j = -1 ∨ j = 0 ∨ j = 1) ∧
    (j = 1 → (if EvenSite z then 2 else frame.child.num) ≤ frame.tGrade z) ∧
    (j = -1 → frame.tGrade z ≤ (if EvenSite z then frame.child.den + frame.child.num - 2 else frame.child.den) -
      frame.child.periodDenominator) ∧
    (i = 1 → frame.sGrade z ≤ (if EvenSite z then 2 * frame.child.num
      else frame.child.den + frame.child.num - 2)) ∧
    (i = -1 → frame.child.periodDenominator + (if EvenSite z then 0 else 2 - frame.child.den + frame.child.num)
      ≤ frame.sGrade z) := by
  obtain ⟨hN, hND, hdiff, hD3, hTdef⟩ := frame.child_facts
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := T_bounds hN hdiff hD3
  have hTpos : 0 < frame.child.periodDenominator := by
    rw [hTdef]
    linarith [hT2]
  rw [frame.mem_closedPolygon_iff] at hz
  rw [frame.mem_translate_iff] at hz'
  by_cases hE : EvenSite z
  · rcases hz with ⟨-, t1, t2, s1, s2⟩ | ⟨hO, -⟩
    · rcases hz' with ⟨-, t1', t2', s1', s2'⟩ | ⟨hO', -⟩
      · have hj := abs_le_one_of_mul j frame.child.periodDenominator
          (frame.child.den + frame.child.num - 2 - (2 - frame.child.periodDenominator)) hTpos (by linarith)
          (by linarith) (by linarith)
        have hi := abs_le_one_of_mul i frame.child.periodDenominator
          (frame.child.periodDenominator + 2 * frame.child.num - 0) hTpos (by linarith) (by linarith)
          (by linarith)
        refine ⟨by omega, by omega, fun hj1 => ?_, fun hj1 => ?_, fun hi1 => ?_, fun hi1 => ?_⟩
        · subst hj1
          simp only [if_pos hE]
          linarith
        · subst hj1
          simp only [if_pos hE]
          linarith
        · subst hi1
          simp only [if_pos hE]
          linarith
        · subst hi1
          simp only [if_pos hE]
          linarith
      · exact absurd hE hO'
    · exact absurd hE hO
  · rcases hz with ⟨hE', -⟩ | ⟨-, t1, t2, s1, s2⟩
    · exact absurd hE' hE
    · rcases hz' with ⟨hE', -⟩ | ⟨-, t1', t2', s1', s2'⟩
      · exact absurd hE' hE
      · have hj := abs_le_one_of_mul j frame.child.periodDenominator
          (frame.child.den - (frame.child.num - frame.child.periodDenominator)) hTpos (by linarith)
          (by linarith) (by linarith)
        have hi := abs_le_one_of_mul i frame.child.periodDenominator
          (frame.child.periodDenominator + frame.child.den + frame.child.num - 2 -
            (2 - frame.child.den + frame.child.num)) hTpos (by linarith) (by linarith) (by linarith)
        refine ⟨by omega, by omega, fun hj1 => ?_, fun hj1 => ?_, fun hi1 => ?_, fun hi1 => ?_⟩
        · subst hj1
          simp only [if_neg hE]
          linarith
        · subst hj1
          simp only [if_neg hE]
          linarith
        · subst hi1
          simp only [if_neg hE]
          linarith
        · subst hi1
          simp only [if_neg hE]
          linarith

/-- Every input of a site of `E` lies in a translate of `E` by at most one generator in each direction. -/
theorem ChildFrame.input_mem_translate (frame : ChildFrame) {z u : Site}
    (hz : z ∈ frame.closedPolygon) (hu : Edge u z) :
    ∃ i j : ℤ, (i = -1 ∨ i = 0 ∨ i = 1) ∧ (j = -1 ∨ j = 0 ∨ j = 1) ∧
      u + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon := by
  obtain ⟨hN, hND, hdiff, hD3, hTdef⟩ := frame.child_facts
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := T_bounds hN hdiff hD3
  rw [frame.mem_closedPolygon_iff] at hz
  rcases hz with ⟨hE, t1, t2, s1, s2⟩ | ⟨hO, t1, t2, s1, s2⟩
  · rcases hu with hu | hu
    · -- `u = (z.1 - 1, z.2)`: the input is horizontal, so `u` is odd
      have hu' : u = (z.1 - 1, z.2) := by simpa [incomingNeg, hE] using hu
      subst hu'
      have hpar : ¬ EvenSite (z.1 - 1, z.2) := by
        unfold EvenSite at hE ⊢
        dsimp only
        omega
      have ht0 := frame.tGrade_sub_x z
      have hs0 := frame.sGrade_sub_x z
      obtain ⟨j, hj, hjA, hjB⟩ := exists_small_shift (frame.tGrade (z.1 - 1, z.2))
        (frame.child.num - frame.child.periodDenominator) frame.child.den frame.child.periodDenominator
        (by linarith) (by rw [ht0]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨i, hi, hiA, hiB⟩ := exists_small_shift (frame.sGrade (z.1 - 1, z.2))
        (2 - frame.child.den + frame.child.num)
        (frame.child.periodDenominator + frame.child.den + frame.child.num - 2) frame.child.periodDenominator
        (by linarith) (by rw [hs0]; exact ⟨by linarith, by linarith⟩)
      refine ⟨-i, j, by omega, hj, ?_⟩
      rw [frame.mem_translate_iff]
      exact Or.inr ⟨hpar, hjA, hjB, by linarith, by linarith⟩
    · -- `u = (z.1 + 1, z.2)`
      have hu' : u = (z.1 + 1, z.2) := by simpa [incomingPos, hE] using hu
      subst hu'
      have hpar : ¬ EvenSite (z.1 + 1, z.2) := by
        unfold EvenSite at hE ⊢
        dsimp only
        omega
      have ht0 := frame.tGrade_add_x z
      have hs0 := frame.sGrade_add_x z
      obtain ⟨j, hj, hjA, hjB⟩ := exists_small_shift (frame.tGrade (z.1 + 1, z.2))
        (frame.child.num - frame.child.periodDenominator) frame.child.den frame.child.periodDenominator
        (by linarith) (by rw [ht0]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨i, hi, hiA, hiB⟩ := exists_small_shift (frame.sGrade (z.1 + 1, z.2))
        (2 - frame.child.den + frame.child.num)
        (frame.child.periodDenominator + frame.child.den + frame.child.num - 2) frame.child.periodDenominator
        (by linarith) (by rw [hs0]; exact ⟨by linarith, by linarith⟩)
      refine ⟨-i, j, by omega, hj, ?_⟩
      rw [frame.mem_translate_iff]
      exact Or.inr ⟨hpar, hjA, hjB, by linarith, by linarith⟩
  · rcases hu with hu | hu
    · -- `u = (z.1, z.2 - 1)`: the input is vertical, so `u` is even
      have hu' : u = (z.1, z.2 - 1) := by simpa [incomingNeg, hO] using hu
      subst hu'
      have hpar : EvenSite (z.1, z.2 - 1) := by
        unfold EvenSite at hO ⊢
        dsimp only
        omega
      have ht0 := frame.tGrade_sub_y z
      have hs0 := frame.sGrade_sub_y z
      obtain ⟨j, hj, hjA, hjB⟩ := exists_small_shift (frame.tGrade (z.1, z.2 - 1))
        (2 - frame.child.periodDenominator) (frame.child.den + frame.child.num - 2)
        frame.child.periodDenominator (by linarith) (by rw [ht0]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨i, hi, hiA, hiB⟩ := exists_small_shift (frame.sGrade (z.1, z.2 - 1)) 0
        (frame.child.periodDenominator + 2 * frame.child.num) frame.child.periodDenominator
        (by linarith) (by rw [hs0]; exact ⟨by linarith, by linarith⟩)
      refine ⟨-i, j, by omega, hj, ?_⟩
      rw [frame.mem_translate_iff]
      exact Or.inl ⟨hpar, hjA, hjB, by linarith, by linarith⟩
    · -- `u = (z.1, z.2 + 1)`
      have hu' : u = (z.1, z.2 + 1) := by simpa [incomingPos, hO] using hu
      subst hu'
      have hpar : EvenSite (z.1, z.2 + 1) := by
        unfold EvenSite at hO ⊢
        dsimp only
        omega
      have ht0 := frame.tGrade_add_y z
      have hs0 := frame.sGrade_add_y z
      obtain ⟨j, hj, hjA, hjB⟩ := exists_small_shift (frame.tGrade (z.1, z.2 + 1))
        (2 - frame.child.periodDenominator) (frame.child.den + frame.child.num - 2)
        frame.child.periodDenominator (by linarith) (by rw [ht0]; exact ⟨by linarith, by linarith⟩)
      obtain ⟨i, hi, hiA, hiB⟩ := exists_small_shift (frame.sGrade (z.1, z.2 + 1)) 0
        (frame.child.periodDenominator + 2 * frame.child.num) frame.child.periodDenominator
        (by linarith) (by rw [hs0]; exact ⟨by linarith, by linarith⟩)
      refine ⟨-i, j, by omega, hj, ?_⟩
      rw [frame.mem_translate_iff]
      exact Or.inl ⟨hpar, hjA, hjB, by linarith, by linarith⟩

end FLatticePaper.Induction
