import FLatticePaper.Plane.Induction.HWeb

/-! Task Q21 (step 1): the box of the free H cut of a child frame.

With `n = child.num`, `d = child.den`, `L = d + n`, `t = tGrade z`, `m = x + y`, the identities
`L · x = d · m + t` and `L · y = n · m − t` (`div_identity`) and the ranges of `m` and `t` on the free H cut
(`m_range_even`, `m_range_odd`) put every free H site in the box `1 ≤ x ≤ d`, `0 ≤ y ≤ n − 1`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- Integer core of the child box: from `L u = d m + t` and `L v = n m − t` with `t ≥ 1`, `0 ≤ m ≤ L − 1`,
`d m + t ≤ d L`, `m = u + v`, the site `(u, v)` lies in `[1, d] × [0, n − 1]`. -/
theorem freeH_box_core (n d m t u v : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hm0 : 0 ≤ m)
    (ht1 : 1 ≤ t) (htL : t ≤ d + n - 1) (hmL : m ≤ d + n - 1) (hup : d * m + t ≤ d * (d + n))
    (key1 : (d + n) * u = d * m + t) (key2 : (d + n) * v = n * m - t) (hmuv : m = u + v) :
    1 ≤ u ∧ u ≤ d ∧ 0 ≤ v ∧ v ≤ n - 1 := by
  have hL : 0 < d + n := by omega
  have hd0 : 0 ≤ d := by omega
  have hn0 : 0 ≤ n := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    have hu : u ≤ 0 := by omega
    have h1 : (d + n) * u ≤ (d + n) * 0 := mul_le_mul_of_nonneg_left hu hL.le
    have h2 : 0 ≤ d * m := mul_nonneg hd0 hm0
    linarith
  · by_contra h
    have hu : d + 1 ≤ u := by omega
    have h1 : (d + n) * (d + 1) ≤ (d + n) * u := mul_le_mul_of_nonneg_left hu hL.le
    linarith
  · by_contra h
    have hv : v ≤ -1 := by omega
    have h1 : (d + n) * v ≤ (d + n) * (-1) := mul_le_mul_of_nonneg_left hv hL.le
    have h2 : 0 ≤ n * m := mul_nonneg hn0 hm0
    linarith
  · by_contra h
    have hv : n ≤ v := by omega
    have h1 : (d + n) * n ≤ (d + n) * v := mul_le_mul_of_nonneg_left hv hL.le
    have h2 : n * m ≤ n * (d + n - 1) := mul_le_mul_of_nonneg_left hmL hn0
    linarith

/-- **The child box of the free H cut.** A site of the closed polygon whose `t`-grade is in the H spectrum lies in
`[1, d] × [0, n − 1]`. This is the box of the conjugate free H arc used by Q21. -/
theorem ChildFrame.freeH_child_box (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.closedPolygon) (hsp : frame.hSpectrum (frame.tGrade z)) :
    1 ≤ z.1 ∧ z.1 ≤ frame.child.den ∧ 0 ≤ z.2 ∧ z.2 ≤ frame.child.num - 1 := by
  obtain ⟨hpos, hlt, hgap, -⟩ := frame.child_facts
  have hpar : (frame.child.den + frame.child.num) % 2 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ := frame.linear_facts
    omega
  have hn : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hkey1 : (frame.child.den + frame.child.num) * z.1 =
      frame.child.den * (z.1 + z.2) + frame.tGrade z := by
    unfold ChildFrame.tGrade
    ring
  have hkey2 := frame.div_identity z
  have hTp := frame.tGrade_mod_two_eq z
  by_cases he : EvenSite z
  · have hcpu := hz
    unfold ChildFrame.closedPolygon at hcpu
    simp only [Set.mem_setOf_eq, if_pos he] at hcpu
    unfold ChildFrame.hSpectrum at hsp
    have ht : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
      rcases hsp with ⟨-, h1, h2⟩ | ⟨h0, -, -⟩
      · exact ⟨h1, h2⟩
      · exfalso
        have hev : (z.1 + z.2) % 2 = 0 := he
        omega
    have hm := frame.m_range_even hn hnd hpar he ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩
    have hmL : z.1 + z.2 ≤ frame.child.den + frame.child.num - 1 := by
      have := hm.2
      omega
    have hup : frame.child.den * (z.1 + z.2) + frame.tGrade z ≤
        frame.child.den * (frame.child.den + frame.child.num) := by
      have h1 : frame.child.den * (z.1 + z.2) ≤ frame.child.den * (frame.child.den + frame.child.num - 2) :=
        mul_le_mul_of_nonneg_left hm.2 (by omega)
      linarith [ht.2]
    exact freeH_box_core frame.child.num frame.child.den (z.1 + z.2) (frame.tGrade z) z.1 z.2 hn hnd hm.1
      (by omega) (by omega) hmL hup hkey1 hkey2.symm rfl
  · have hcpu := hz
    unfold ChildFrame.closedPolygon at hcpu
    simp only [Set.mem_setOf_eq, if_neg he] at hcpu
    unfold ChildFrame.hSpectrum at hsp
    have hod : (z.1 + z.2) % 2 = 1 := by
      unfold EvenSite at he
      omega
    have ht : frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
      rcases hsp with ⟨h0, -, -⟩ | ⟨-, h1, h2⟩
      · exfalso
        omega
      · exact ⟨h1, h2⟩
    have hm := frame.m_range_odd hn hnd hpar hod ht ⟨hcpu.2.2.1, hcpu.2.2.2⟩
    have hmL : z.1 + z.2 ≤ frame.child.den + frame.child.num - 1 := hm.2
    have hup : frame.child.den * (z.1 + z.2) + frame.tGrade z ≤
        frame.child.den * (frame.child.den + frame.child.num) := by
      have h1 : frame.child.den * (z.1 + z.2) ≤ frame.child.den * (frame.child.den + frame.child.num - 1) :=
        mul_le_mul_of_nonneg_left hm.2 (by omega)
      linarith [ht.2]
    exact freeH_box_core frame.child.num frame.child.den (z.1 + z.2) (frame.tGrade z) z.1 z.2 hn hnd hm.1
      (by omega) (by omega) hmL hup hkey1 hkey2.symm rfl

end FLatticePaper.Induction
