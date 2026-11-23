import FLatticePaper.Plane.Induction.CollarLeft

/-! Task 72 (hcollar, band (a), the right class). A strict right centre `c` (not bottom, not top, not left, with a free V
witness `v − U`) has its lower-left square `squareCorners (c1 − 1) (c2 − 1)` strict.

The upper `t` bounds come from `¬BottomArc` and the lower `t` bounds from `¬TopArc` (as in the left class). The right
witness gives the lower `s` bound: `s(U) = T`, so `s(v − U) ≥ 2 − d + n` forces `s(c) ≥ T + 2 − 3d + n`. -/

namespace FLatticePaper.CollarRight

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CollarBottomCases
  FLatticePaper.CollarBottomSquare FLatticePaper.CollarTop FLatticePaper.CollarGlue FLatticePaper.AndOrRank
  FLatticePaper.CollarLeft FLatticePaper.W1CollarFrame

/-- The upper and lower `t` bounds of an even strict centre that is neither bottom nor top. -/
theorem t_bounds_even (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hcE : EvenSite c)
    (hB : ¬ BottomArc frame c) (hT : ¬ TopArc frame c) :
    frame.child.num * c.1 - frame.child.den * c.2 < frame.child.num - frame.child.den ∧
      2 * frame.child.den -
          (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) <
        frame.child.num * c.1 - frame.child.den * c.2 := by
  obtain ⟨hn0, -, hd2, -, hpoly⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hcE' : (c.1 + c.2) % 2 = 0 := hcE
  obtain ⟨-, hcu, hcs1, hcs2⟩ := (strict_even_iff _ _ c hcE).mp hcS
  have hpc := t_parity frame.child.num frame.child.den c.1 c.2 hnodd hdodd
  have hz : StrictInterior frame.child.num frame.child.den (frame.centre - c) :=
    (strict_reflect_centre frame c).mpr hcS
  have hzsum : (frame.centre - c).1 + (frame.centre - c).2 =
      3 * frame.child.num + frame.child.den - (c.1 + c.2) := by
    rw [centre_eq]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have htz : frame.tGrade (frame.centre - c) =
      (frame.child.den + frame.child.num) -
        (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) -
          (frame.child.num * c.1 - frame.child.den * c.2) := by
    rw [tGrade_centre_sub frame c, hpoly]
    simp only [ChildFrame.tGrade]
  have hzE : EvenSite (frame.centre - c) := by
    unfold EvenSite
    omega
  have hzE' : ((frame.centre - c).1 + (frame.centre - c).2) % 2 = 0 := hzE
  have hzt := (strict_even_iff _ _ (frame.centre - c) hzE).mp hz
  have hzp := t_parity frame.child.num frame.child.den (frame.centre - c).1 (frame.centre - c).2 hnodd hdodd
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    apply hB
    exact bottomArc_of_even frame hcS hcE (by show frame.child.num - frame.child.den ≤ frame.child.num * c.1 - frame.child.den * c.2; linarith)
      (by
        show frame.child.num * c.1 - frame.child.den * c.2 ≤ 0
        generalize frame.child.num * c.1 - frame.child.den * c.2 = τ at *
        omega)
  · by_contra hcon
    rw [not_lt] at hcon
    apply hT
    apply topArc_of_bottom_centre frame
    apply bottomArc_of_even frame hz hzE
    · show frame.child.num - frame.child.den ≤ frame.tGrade (frame.centre - c)
      linarith
    · show frame.child.num * (frame.centre - c).1 - frame.child.den * (frame.centre - c).2 ≤ 0
      have hzt2 := hzt.2.1
      generalize frame.child.num * (frame.centre - c).1 - frame.child.den * (frame.centre - c).2 = τ at *
      omega

/-- The upper and lower `t` bounds of an odd strict centre that is neither bottom nor top. -/
theorem t_bounds_odd (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hcO : ¬ EvenSite c)
    (hB : ¬ BottomArc frame c) (hT : ¬ TopArc frame c) :
    frame.child.num * c.1 - frame.child.den * c.2 < 2 - frame.child.den ∧
      2 * frame.child.den + frame.child.num - 2 -
          (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) <
        frame.child.num * c.1 - frame.child.den * c.2 := by
  obtain ⟨hn0, -, hd2, -, hpoly⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hcO' : (c.1 + c.2) % 2 = 1 := by
    unfold EvenSite at hcO
    omega
  obtain ⟨-, -, -, -⟩ := (strict_odd_iff _ _ c hcO).mp hcS
  have hz : StrictInterior frame.child.num frame.child.den (frame.centre - c) :=
    (strict_reflect_centre frame c).mpr hcS
  have hzsum : (frame.centre - c).1 + (frame.centre - c).2 =
      3 * frame.child.num + frame.child.den - (c.1 + c.2) := by
    rw [centre_eq]
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have htz : frame.tGrade (frame.centre - c) =
      (frame.child.den + frame.child.num) -
        (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) -
          (frame.child.num * c.1 - frame.child.den * c.2) := by
    rw [tGrade_centre_sub frame c, hpoly]
    simp only [ChildFrame.tGrade]
  have hzO : ¬ EvenSite (frame.centre - c) := by
    unfold EvenSite
    omega
  constructor
  · by_contra hcon
    rw [not_lt] at hcon
    apply hB
    exact bottomArc_of_odd frame hcS hcO
      (by show 2 - frame.child.den ≤ frame.child.num * c.1 - frame.child.den * c.2; linarith)
  · by_contra hcon
    rw [not_lt] at hcon
    apply hT
    apply topArc_of_bottom_centre frame
    apply bottomArc_of_odd frame hz hzO
    show 2 - frame.child.den ≤ frame.tGrade (frame.centre - c)
    linarith

/-- The membership in the lower-left square `squareCorners (c1 − 1) (c2 − 1)`. -/
theorem square_mem_LL (c : Site) (x y : ℤ) :
    (x, y) ∈ squareCorners (c.1 - 1) (c.2 - 1) ↔
      (x = c.1 - 1 ∧ y = c.2 - 1) ∨ (x = c.1 ∧ y = c.2 - 1) ∨ (x = c.1 - 1 ∧ y = c.2) ∨ (x = c.1 ∧ y = c.2) := by
  simp [squareCorners, Prod.ext_iff]

/-- The lower-left corners of an even right centre (grades). -/
theorem right_corners_even (n d T a b : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcE : (a + b) % 2 = 0)
    (hcs2 : (d + n) * a + (d - n) * b < T)
    (hA : n * a - d * b < n - d) (hB : 2 * d - T < n * a - d * b)
    (hS : 2 * n + 2 * d < (d + n) * a + (d - n) * b) :
    StrictInterior n d (a - 1, b - 1) ∧ StrictInterior n d (a, b - 1) ∧ StrictInterior n d (a - 1, b) := by
  have hT5 : 5 * d + n - 2 < T := by rw [hT]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [strict_even_iff n d (a - 1, b - 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a, b - 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a - 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The lower-left corners of an odd right centre (grades). -/
theorem right_corners_odd (n d T a b : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcO : (a + b) % 2 = 1)
    (hcs2 : (d + n) * a + (d - n) * b < T + (2 - d + n))
    (hA : n * a - d * b < 2 - d) (hB : 2 * d + n - 2 - T < n * a - d * b)
    (hS : 3 * d + n - 2 < (d + n) * a + (d - n) * b) :
    StrictInterior n d (a - 1, b - 1) ∧ StrictInterior n d (a, b - 1) ∧ StrictInterior n d (a - 1, b) := by
  have hT6 : 6 * d - 4 < T := by rw [hT]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [strict_odd_iff n d (a - 1, b - 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a, b - 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a - 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A free V witness of `v − U` gives the lower `s` bound `s(c) ≥ T + 2 − 3d + n`. -/
theorem sGrade_ge_of_rightArc (frame : ChildFrame) {c v : Site} (hv1 : |v.1 - c.1| ≤ 1)
    (hv2 : |v.2 - c.2| ≤ 1) (hvF : v - frame.child.modifiedDeck.kernel ∈ frame.freeV) :
    frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 + 2 -
        3 * frame.child.den + frame.child.num ≤ frame.sGrade c := by
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  rw [ChildFrame.child_modifiedDeck_kernel] at hvF
  obtain ⟨-, -, hwS⟩ := hvF
  unfold ChildFrame.vSpectrum at hwS
  obtain ⟨-, hwb⟩ := hwS
  have hw : 2 - frame.child.den + frame.child.num ≤ frame.sGrade (v - (frame.child.den, frame.child.num)) := by
    omega
  obtain ⟨h1, h2⟩ := abs_le.mp hv1
  obtain ⟨h3, h4⟩ := abs_le.mp hv2
  have hL : (0 : ℤ) ≤ frame.child.den + frame.child.num := by omega
  have hD : (0 : ℤ) ≤ frame.child.den - frame.child.num := by omega
  have e1 := mul_le_mul_of_nonneg_left (show -1 ≤ c.1 - v.1 by linarith) hL
  have e2 := mul_le_mul_of_nonneg_left (show -1 ≤ c.2 - v.2 by linarith) hD
  unfold ChildFrame.sGrade at hw ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hw
  linarith

/-- A centre not bottom, top or left, with the conditions of the collar frame, has a right witness. -/
theorem rightArc_of_collarFrame (frame : ChildFrame) {c : Site} (hcol : CollarFrame frame c)
    (hB : ¬ BottomArc frame c) (hT : ¬ TopArc frame c) (hL : ¬ LeftArc frame c) : RightArc frame c := by
  obtain ⟨v, hv1, hv2, hv⟩ := hcol
  rcases hv with h | h | h | h
  · exact absurd ⟨v, hv1, hv2, h⟩ hB
  · exact absurd ⟨v, hv1, hv2, h⟩ hL
  · exact absurd ⟨v, hv1, hv2, h⟩ hT
  · exact ⟨v, hv1, hv2, h⟩

/-- **The right class.** A strict right centre, not bottom, top or left, has its lower-left square strict. -/
theorem right_square_strict (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hB : ¬ BottomArc frame c)
    (hT : ¬ TopArc frame c) (hR : RightArc frame c) :
    ∀ c' ∈ squareCorners (c.1 - 1) (c.2 - 1), StrictInterior frame.child.num frame.child.den c' := by
  obtain ⟨hn0, hnd1, hd2, -, hpoly⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨v, hv1, hv2, hvF⟩ := hR
  have hsl := sGrade_ge_of_rightArc frame hv1 hv2 hvF
  intro c' hc'
  obtain ⟨x, y⟩ := c'
  by_cases hcE : EvenSite c
  · have hcE' : (c.1 + c.2) % 2 = 0 := hcE
    obtain ⟨hA, hB'⟩ := t_bounds_even frame hcS hcE hB hT
    obtain ⟨-, hcu, -, hcs2⟩ := (strict_even_iff _ _ c hcE).mp hcS
    obtain ⟨C1, C2, C3⟩ := right_corners_even frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) c.1 c.2 hn3 hnd rfl
      hcE' hcs2 hA hB'
      (by
        unfold ChildFrame.sGrade at hsl
        have hT5 : 5 * frame.child.den + frame.child.num - 2 <
            frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
            (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega)]
        linarith)
    rcases (square_mem_LL c x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C1
    · exact C2
    · exact C3
    · exact hcS
  · have hcO : (c.1 + c.2) % 2 = 1 := by
      unfold EvenSite at hcE
      omega
    obtain ⟨hA, hB'⟩ := t_bounds_odd frame hcS hcE hB hT
    obtain ⟨-, -, hcs1, hcs2⟩ := (strict_odd_iff _ _ c hcE).mp hcS
    obtain ⟨C1, C2, C3⟩ := right_corners_odd frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) c.1 c.2 hn3 hnd rfl
      hcO hcs2 hA hB'
      (by
        unfold ChildFrame.sGrade at hsl
        have hT6 : 6 * frame.child.den - 4 <
            frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
          nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
            (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega)]
        linarith)
    rcases (square_mem_LL c x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C1
    · exact C2
    · exact C3
    · exact hcS

end FLatticePaper.CollarRight
