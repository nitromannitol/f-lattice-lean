import FLatticePaper.Plane.Induction.CollarTop

/-! Task 72 (hcollar, band (a), the left class). A strict left centre `c` (not a bottom centre, not a top centre, with a
free V witness) has its upper-right square `squareCorners c1 c2` strict.

The bottom neighbour of a strict centre with the right `t` is a free H point (`bottomArc_of_odd`, `bottomArc_of_even`).
The centre reflection `R − c` turns the top condition into a bottom condition on `R − c` (`topArc_of_bottom_centre`), so
`¬TopArc c` gives the lower `t` bounds. The free V witness gives `s(c) ≤ 3d + n − 2`, and `T > 6d − 4` (from `n ≥ 3`)
gives the upper `s` bounds. -/

namespace FLatticePaper.CollarLeft

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CollarBottomCases
  FLatticePaper.CollarBottomSquare FLatticePaper.CollarTop FLatticePaper.CollarGlue FLatticePaper.AndOrRank

/-- The bottom neighbour of an odd strict centre with `t ≥ 2 − d`, as a free H point (grades). -/
theorem freeH_below_odd_pure (n d T a b : ℤ) (hn0 : 0 < n) (hnd : n + 2 ≤ d) (hnodd : n % 2 = 1)
    (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcO : (a + b) % 2 = 1)
    (hcu : n * a - d * b < n) (hcs1 : d + n - 2 < (d + n) * a + (d - n) * b)
    (hcs2 : (d + n) * a + (d - n) * b < T + (2 - d + n)) (ht : 2 - d ≤ n * a - d * b) :
    EDisj n d T a (b - 1) ∧ ¬ EDisj n d T a (b - 1 - 1) ∧ SpecH n d a (b - 1) := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have hpt := t_parity n d a b hnodd hdodd
  have ht1 : n * a - d * (b - 1) = (n * a - d * b) + d := by ring
  have ht2 : n * a - d * (b - 1 - 1) = (n * a - d * b) + 2 * d := by ring
  have hs1 : (d + n) * a + (d - n) * (b - 1) = (d + n) * a + (d - n) * b - (d - n) := by ring
  have hs2 : (d + n) * a + (d - n) * (b - 1 - 1) = (d + n) * a + (d - n) * b - 2 * (d - n) := by ring
  unfold EDisj SpecH
  rw [ht1, ht2, hs1, hs2]
  generalize hτ : n * a - d * b = τ at *
  generalize hσ : (d + n) * a + (d - n) * b = σ at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The bottom neighbour of an even strict centre with `n − d ≤ t ≤ 0`, as a free H point (grades). -/
theorem freeH_below_even_pure (n d T a b : ℤ) (hn0 : 0 < n) (hnd : n + 2 ≤ d) (hnodd : n % 2 = 1)
    (hdodd : d % 2 = 1) (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcE : (a + b) % 2 = 0)
    (hcs1 : 2 * n < (d + n) * a + (d - n) * b) (hcs2 : (d + n) * a + (d - n) * b < T)
    (hlo : n - d ≤ n * a - d * b) (hhi : n * a - d * b ≤ 0) :
    EDisj n d T a (b - 1) ∧ ¬ EDisj n d T a (b - 1 - 1) ∧ SpecH n d a (b - 1) := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have hpt := t_parity n d a b hnodd hdodd
  have ht1 : n * a - d * (b - 1) = (n * a - d * b) + d := by ring
  have ht2 : n * a - d * (b - 1 - 1) = (n * a - d * b) + 2 * d := by ring
  have hs1 : (d + n) * a + (d - n) * (b - 1) = (d + n) * a + (d - n) * b - (d - n) := by ring
  have hs2 : (d + n) * a + (d - n) * (b - 1 - 1) = (d + n) * a + (d - n) * b - 2 * (d - n) := by ring
  unfold EDisj SpecH
  rw [ht1, ht2, hs1, hs2]
  generalize hτ : n * a - d * b = τ at *
  generalize hσ : (d + n) * a + (d - n) * b = σ at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- An odd strict centre with `t ≥ 2 − d` has a bottom witness (its neighbour below is free H). -/
theorem bottomArc_of_odd (frame : ChildFrame) {w : Site}
    (hsc : StrictInterior frame.child.num frame.child.den w) (ho : ¬ EvenSite w)
    (ht : 2 - frame.child.den ≤ frame.tGrade w) : BottomArc frame w := by
  obtain ⟨hn0, -, hd2, -, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have ho' : (w.1 + w.2) % 2 = 1 := by
    unfold EvenSite at ho
    omega
  obtain ⟨-, hcu, hcs1, hcs2⟩ := (strict_odd_iff _ _ w ho).mp hsc
  obtain ⟨h1, h2, h3⟩ := freeH_below_odd_pure frame.child.num frame.child.den frame.child.periodDenominator
    w.1 w.2 hn0 hnd hnodd hdodd hT ho' hcu hcs1 (by rw [hT]; linarith) ht
  refine ⟨(w.1, w.2 - 1), ?_, ?_, ?_⟩
  · simp
  · simp
  · show _ ∧ _ ∧ _
    exact ⟨(mem_closedPolygon_EDisj frame _).mpr h1, fun hm => h2 ((mem_closedPolygon_EDisj frame _).mp hm), h3⟩

/-- An even strict centre with `n − d ≤ t ≤ 0` has a bottom witness. -/
theorem bottomArc_of_even (frame : ChildFrame) {w : Site}
    (hsc : StrictInterior frame.child.num frame.child.den w) (he : EvenSite w)
    (h1 : frame.child.num - frame.child.den ≤ frame.tGrade w) (h2 : frame.tGrade w ≤ 0) :
    BottomArc frame w := by
  obtain ⟨hn0, -, hd2, -, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have he' : (w.1 + w.2) % 2 = 0 := he
  obtain ⟨-, -, hcs1, hcs2⟩ := (strict_even_iff _ _ w he).mp hsc
  obtain ⟨g1, g2, g3⟩ := freeH_below_even_pure frame.child.num frame.child.den frame.child.periodDenominator
    w.1 w.2 hn0 hnd hnodd hdodd hT he' hcs1 (by rw [hT]; linarith [hcs2]) h1 h2
  refine ⟨(w.1, w.2 - 1), ?_, ?_, ?_⟩
  · simp
  · simp
  · show _ ∧ _ ∧ _
    exact ⟨(mem_closedPolygon_EDisj frame _).mpr g1, fun hm => g2 ((mem_closedPolygon_EDisj frame _).mp hm), g3⟩

/-- The top condition of `c` is the bottom condition of `R − c` (the converse of `top_bottom_witness`). -/
theorem topArc_of_bottom_centre (frame : ChildFrame) {c : Site} (h : BottomArc frame (frame.centre - c)) :
    TopArc frame c := by
  obtain ⟨v, hA, hB, hv⟩ := h
  refine ⟨frame.centre - v, ?_, ?_, ?_⟩
  · have e : (frame.centre - v).1 - c.1 = (frame.centre - c).1 - v.1 := by
      simp only [Prod.fst_sub]
      ring
    rw [e, abs_sub_comm]
    exact hA
  · have e : (frame.centre - v).2 - c.2 = (frame.centre - c).2 - v.2 := by
      simp only [Prod.snd_sub]
      ring
    rw [e, abs_sub_comm]
    exact hB
  · rw [sub_sub]
    exact freeH_reflect frame hv

/-- The grade of the reflected centre: `t(R − c) = L − T − t(c)`. -/
theorem tGrade_centre_sub (frame : ChildFrame) (c : Site) :
    frame.tGrade (frame.centre - c) =
      (frame.child.den + frame.child.num) - frame.child.periodDenominator - frame.tGrade c := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [hT, centre_eq]
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- A point of a square. -/
theorem square_mem (a b x y : ℤ) :
    (x, y) ∈ squareCorners a b ↔
      (x = a ∧ y = b) ∨ (x = a + 1 ∧ y = b) ∨ (x = a ∧ y = b + 1) ∨ (x = a + 1 ∧ y = b + 1) := by
  simp [squareCorners, Prod.ext_iff]

/-- The upper-right corners of an even left centre (grades). -/
theorem left_corners_even (n d T a b : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcE : (a + b) % 2 = 0) (hcu : n * a - d * b < 2)
    (hcs1 : 2 * n < (d + n) * a + (d - n) * b)
    (hA : n * a - d * b < n - d) (hB : 2 * d - T < n * a - d * b)
    (hS : (d + n) * a + (d - n) * b ≤ 3 * d + n - 2) :
    StrictInterior n d (a + 1, b) ∧ StrictInterior n d (a, b + 1) ∧ StrictInterior n d (a + 1, b + 1) := by
  have hT5 : 5 * d + n - 2 < T := by rw [hT]; nlinarith
  have hsT : (d + n) * a + (d - n) * b < T - 2 * d := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [strict_odd_iff n d (a + 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a + 1, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The upper-right corners of an odd left centre (grades). -/
theorem left_corners_odd (n d T a b : ℤ) (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hcO : (a + b) % 2 = 1)
    (hcs1 : d + n - 2 < (d + n) * a + (d - n) * b)
    (hA : n * a - d * b < 2 - d) (hB : 2 * d + n - 2 - T < n * a - d * b)
    (hS : (d + n) * a + (d - n) * b ≤ 3 * d + n - 2) :
    StrictInterior n d (a + 1, b) ∧ StrictInterior n d (a, b + 1) ∧ StrictInterior n d (a + 1, b + 1) := by
  have hT6 : 6 * d - 4 < T := by rw [hT]; nlinarith
  have hsT2 : (d + n) * a + (d - n) * b < T - d - n := by linarith
  have hsT3 : (d + n) * a + (d - n) * b < T - d + n := by linarith
  have hsT4 : (d + n) * a + (d - n) * b < T + (2 - 3 * d + n) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [strict_even_iff n d (a + 1, b) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_even_iff n d (a, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d (a + 1, b + 1) (by unfold EvenSite; dsimp only; omega)]
    dsimp only
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The free V witness gives `s(c) ≤ 3d + n − 2`. -/
theorem sGrade_le_of_freeV (frame : ChildFrame) {c v : Site} (hv1 : |v.1 - c.1| ≤ 1) (hv2 : |v.2 - c.2| ≤ 1)
    (hvF : v ∈ frame.freeV) : frame.sGrade c ≤ 3 * frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨-, -, hvS⟩ := hvF
  unfold ChildFrame.vSpectrum at hvS
  obtain ⟨-, hvb⟩ := hvS
  have hsv : frame.sGrade v ≤ frame.child.den + frame.child.num - 2 := by omega
  obtain ⟨h1, h2⟩ := abs_le.mp hv1
  obtain ⟨h3, h4⟩ := abs_le.mp hv2
  have hL : (0 : ℤ) ≤ frame.child.den + frame.child.num := by omega
  have hD : (0 : ℤ) ≤ frame.child.den - frame.child.num := by omega
  have e1 := mul_le_mul_of_nonneg_left (show c.1 - v.1 ≤ 1 by linarith) hL
  have e2 := mul_le_mul_of_nonneg_left (show c.2 - v.2 ≤ 1 by linarith) hD
  unfold ChildFrame.sGrade at hsv ⊢
  linarith

/-- **The left class.** A strict left centre, not bottom and not top, has its upper-right square strict. -/
theorem left_square_strict (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hB : ¬ BottomArc frame c)
    (hT : ¬ TopArc frame c) (hL : LeftArc frame c) :
    ∀ c' ∈ squareCorners c.1 c.2, StrictInterior frame.child.num frame.child.den c' := by
  obtain ⟨hn0, hnd1, hd2, -, hpoly⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨v, hv1, hv2, hvF⟩ := hL
  have hsup := sGrade_le_of_freeV frame hv1 hv2 hvF
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
  by_cases hcE : EvenSite c
  · have hcE' : (c.1 + c.2) % 2 = 0 := hcE
    obtain ⟨-, hcu, hcs1, hcs2⟩ := (strict_even_iff _ _ c hcE).mp hcS
    have hpc := t_parity frame.child.num frame.child.den c.1 c.2 hnodd hdodd
    have hzE : EvenSite (frame.centre - c) := by
      unfold EvenSite
      omega
    have hzE' : ((frame.centre - c).1 + (frame.centre - c).2) % 2 = 0 := hzE
    have hzt := (strict_even_iff _ _ (frame.centre - c) hzE).mp hz
    have hzp := t_parity frame.child.num frame.child.den (frame.centre - c).1 (frame.centre - c).2 hnodd hdodd
    have hA : frame.child.num * c.1 - frame.child.den * c.2 < frame.child.num - frame.child.den := by
      by_contra hcon
      rw [not_lt] at hcon
      apply hB
      exact bottomArc_of_even frame hcS hcE (by show frame.child.num - frame.child.den ≤ frame.child.num * c.1 - frame.child.den * c.2; linarith)
        (by
          show frame.child.num * c.1 - frame.child.den * c.2 ≤ 0
          generalize frame.child.num * c.1 - frame.child.den * c.2 = τ at *
          omega)
    have hB' : 2 * frame.child.den -
        (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) <
          frame.child.num * c.1 - frame.child.den * c.2 := by
      by_contra hcon
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
    obtain ⟨C1, C2, C3⟩ := left_corners_even frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) c.1 c.2 hn3 hnd rfl
      hcE' hcu hcs1 hA hB' hsup
    intro c' hc'
    obtain ⟨x, y⟩ := c'
    rcases (square_mem c.1 c.2 x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcS
    · exact C1
    · exact C2
    · exact C3
  · have hcO : (c.1 + c.2) % 2 = 1 := by
      unfold EvenSite at hcE
      omega
    obtain ⟨-, -, hcs1, hcs2⟩ := (strict_odd_iff _ _ c hcE).mp hcS
    have hpc := t_parity frame.child.num frame.child.den c.1 c.2 hnodd hdodd
    have hzO : ¬ EvenSite (frame.centre - c) := by
      unfold EvenSite
      omega
    have hzt := (strict_odd_iff _ _ (frame.centre - c) hzO).mp hz
    have hA : frame.child.num * c.1 - frame.child.den * c.2 < 2 - frame.child.den := by
      by_contra hcon
      rw [not_lt] at hcon
      apply hB
      exact bottomArc_of_odd frame hcS hcE (by show 2 - frame.child.den ≤ frame.child.num * c.1 - frame.child.den * c.2; linarith)
    have hB' : 2 * frame.child.den + frame.child.num - 2 -
        (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) <
          frame.child.num * c.1 - frame.child.den * c.2 := by
      by_contra hcon
      rw [not_lt] at hcon
      apply hT
      apply topArc_of_bottom_centre frame
      apply bottomArc_of_odd frame hz hzO
      show 2 - frame.child.den ≤ frame.tGrade (frame.centre - c)
      linarith
    obtain ⟨C1, C2, C3⟩ := left_corners_odd frame.child.num frame.child.den
      (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2) c.1 c.2 hn3 hnd rfl
      hcO hcs1 hA hB' hsup
    intro c' hc'
    obtain ⟨x, y⟩ := c'
    rcases (square_mem c.1 c.2 x y).mp hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcS
    · exact C1
    · exact C2
    · exact C3

end FLatticePaper.CollarLeft
