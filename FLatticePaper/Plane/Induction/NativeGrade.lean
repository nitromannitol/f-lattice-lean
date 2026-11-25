import FLatticePaper.Plane.Induction.RootClassify
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.ClippedArith
import FLatticePaper.Plane.Induction.GradeCollision
import FLatticePaper.Plane.Induction.FreeEnum

/-! Task 72 / Q31 psi (i): the parent grade of the native free V cut.

For a child frame with odd parent `N/D`, `r = D + N`, `c_p = D − N`, the parent grade of a site is `pg z = r z₁ + c_p z₂`.
A nonfinal free V point has its parent grade in the even range `[0, E]` (`E = 2N` or `2N − 2`) or in the odd range `[lo, r]`
(`lo = 2 − c_p` or `−c_p`), by the window lemmas and `RootClassify`. Two such points of the same residue of ordinates mod `r` have
equal parent grades or the grades `{0, r}` (`GradeCollision.grade_collision`). -/

namespace FLatticePaper.NativeGrade

open Farey FLatticePaper FLatticePaper.Induction

/-- The parent grade `s_p(z) = (D + N) z₁ + (D − N) z₂`. -/
def pg (frame : ChildFrame) (z : Site) : ℤ :=
  (frame.parents.odd.den + frame.parents.odd.num) * z.1 + (frame.parents.odd.den - frame.parents.odd.num) * z.2

/-- The top of the even parent grades: `2N − 2` when `ε = 1`, `2N` when `ε = −1`. -/
def gE (frame : ChildFrame) : ℤ :=
  if frame.eps = 1 then 2 * frame.parents.odd.num - 2 else 2 * frame.parents.odd.num

/-- The bottom of the odd parent grades: `2 − c_p` when `ε = −1`, `−c_p` when `ε = 1`. -/
def gLo (frame : ChildFrame) : ℤ :=
  if frame.eps = -1 then 2 - (frame.parents.odd.den - frame.parents.odd.num)
  else -(frame.parents.odd.den - frame.parents.odd.num)

/-- `ε = N d − D n` for the child `n/d` and the odd parent `N/D`. -/
theorem eps_eq_child (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num := by
  rw [ClippedArith.eps_det, ZoneI1.child_num_eq, ZoneI1.child_den_eq]
  ring

/-- The odd parent has `0 < D`, `0 ≤ N`, `N ≤ D`, and `N + D` odd. -/
theorem odd_parent_facts (frame : ChildFrame) :
    0 < frame.parents.odd.den ∧ 0 ≤ frame.parents.odd.num ∧ frame.parents.odd.num ≤ frame.parents.odd.den ∧
      (frame.parents.odd.den + frame.parents.odd.num) % 2 = 1 := by
  have hb := frame.valid.odd_bounds
  have hp := frame.valid.odd_parity
  unfold Fraction.InUnitInterval at hb
  unfold Fraction.Odd at hp
  exact ⟨hb.1, hb.2.1, hb.2.2, by omega⟩

/-- The even window: a nonfinal even free V point has `0 ≤ pg ≤ gE`, and `pg` is even. -/
theorem freeV_even_grade (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z)
    (hne : z ≠ frame.vLast) :
    pg frame z % 2 = 0 ∧ 0 ≤ pg frame z ∧ pg frame z ≤ gE frame := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  obtain ⟨hs0, hs1⟩ := FreeVWindow.freeV_even_window frame hz he
  obtain ⟨hj0, -, hjL⟩ := FreeVOrdinate.freeV_even_ordinate frame hz he
  have hjL' := hjL hne
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  have hε := eps_eq_child frame
  have hε1 := frame.eps_unit
  have hpar : (z.1 + z.2) % 2 = 0 := he
  have hodd' : (frame.parents.odd.den - frame.parents.odd.num) % 2 = 1 := by omega
  have hr := RootClassify.even_sp_range frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    frame.eps z.1 z.2 hε hε1 hN0 hDpos hodd hodd' (by omega) hj0 hjL' hs0 hs1 hpar
  have hp := RootClassify.sp_parity (frame.parents.odd.den + frame.parents.odd.num)
    (frame.parents.odd.den - frame.parents.odd.num) z.1 z.2 hodd (by omega)
  unfold pg gE
  refine ⟨?_, hr.1, hr.2⟩
  rw [hp]
  omega


/-- The odd window: an odd free V point has `pg` odd, `gLo ≤ pg ≤ r`. The lower bound is sharp when `ε = −1`. -/
theorem freeV_odd_grade (frame : ChildFrame) (hcut : FreeEnum.CutOnePerOrdinate frame) {z : Site}
    (hz : z ∈ frame.freeV) (ho : ¬ EvenSite z) :
    pg frame z % 2 = 1 ∧ gLo frame ≤ pg frame z ∧ pg frame z ≤ frame.parents.odd.den + frame.parents.odd.num := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  obtain ⟨hs0, hs1⟩ := FreeVWindow.freeV_odd_window frame hz ho
  obtain ⟨hj0, hjL⟩ := FreeVOrdinate.freeV_odd_ordinate frame hcut hz ho
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  have hε := eps_eq_child frame
  have hε1 := frame.eps_unit
  have hpar : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at ho
    omega
  have hodd' : (frame.parents.odd.den - frame.parents.odd.num) % 2 = 1 := by omega
  have hr := RootClassify.odd_sp_range frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    frame.eps z.1 z.2 hε hε1 hN0 hDpos hodd hodd' (by omega) hj0 hjL hs0 hs1 hpar
  have hp := RootClassify.sp_parity (frame.parents.odd.den + frame.parents.odd.num)
    (frame.parents.odd.den - frame.parents.odd.num) z.1 z.2 hodd hodd'
  have hr' : frame.parents.odd.num - frame.parents.odd.den ≤ pg frame z ∧
      pg frame z ≤ frame.parents.odd.den + frame.parents.odd.num := hr
  have hp' : pg frame z % 2 = (z.1 + z.2) % 2 := hp
  have hpg : pg frame z % 2 = 1 := by omega
  refine ⟨hpg, ?_, hr'.2⟩
  unfold gLo
  split_ifs with hm
  · by_contra hlt
    have hne : pg frame z ≠ -(frame.parents.odd.den - frame.parents.odd.num) := by
      intro hg
      have hg' : (frame.parents.odd.den + frame.parents.odd.num) * z.1 +
          (frame.parents.odd.den - frame.parents.odd.num) * z.2 = -(frame.parents.odd.den - frame.parents.odd.num) := hg
      exact GradeCollision.odd_grade_ne_low frame.parents.odd.num frame.parents.odd.den frame.child.num
        frame.child.den frame.eps z.1 z.2 hε hm (by omega) hj0 hs0 hg'
    omega
  · omega

/-- Every nonfinal free V point has its parent grade in the even range or in the odd range. -/
theorem grade_mem (frame : ChildFrame) (hcut : FreeEnum.CutOnePerOrdinate frame) {z : Site}
    (hz : z ∈ frame.freeV) (hne : z ≠ frame.vLast) :
    (pg frame z % 2 = 0 ∧ 0 ≤ pg frame z ∧ pg frame z ≤ gE frame) ∨
      (pg frame z % 2 = 1 ∧ gLo frame ≤ pg frame z ∧ pg frame z ≤ frame.parents.odd.den + frame.parents.odd.num) := by
  by_cases he : EvenSite z
  · exact Or.inl (freeV_even_grade frame hz he hne)
  · exact Or.inr (freeV_odd_grade frame hcut hz he)

/-- A free V point of ordinate `< L − 1` is not the final vertex. -/
theorem ne_vLast_of_ordinate (frame : ChildFrame) {z : Site} (hz : z.2 < frame.child.den + frame.child.num - 1) :
    z ≠ frame.vLast := by
  intro h
  have h2 : z.2 = frame.vLast.2 := by rw [h]
  unfold ChildFrame.vLast at h2
  simp only at h2
  omega

/-- **Residue trichotomy of the native parent grades.** Two nonfinal free V points whose ordinates differ by a multiple of
`r = D + N` have equal parent grades, or the grades `{0, r}`. -/
theorem pg_trichotomy (frame : ChildFrame) (hcut : FreeEnum.CutOnePerOrdinate frame) (hN : 0 < frame.parents.odd.num)
    {z b : Site} (hz : z ∈ frame.freeV) (hzne : z ≠ frame.vLast) (hb : b ∈ frame.freeV) (hbne : b ≠ frame.vLast)
    (t : ℤ) (ht : z.2 - b.2 = (frame.parents.odd.den + frame.parents.odd.num) * t) :
    pg frame z = pg frame b ∨ (pg frame z = 0 ∧ pg frame b = frame.parents.odd.den + frame.parents.odd.num) ∨
      (pg frame z = frame.parents.odd.den + frame.parents.odd.num ∧ pg frame b = 0) := by
  obtain ⟨hDpos, hN0, hNle, hodd⟩ := odd_parent_facts frame
  have hdiv : (frame.parents.odd.den + frame.parents.odd.num) ∣ pg frame z - pg frame b :=
    ⟨(z.1 - b.1) + (frame.parents.odd.den - frame.parents.odd.num) * t, by
      unfold pg
      linear_combination (frame.parents.odd.den - frame.parents.odd.num) * ht⟩
  have hcp : 0 < frame.parents.odd.den - frame.parents.odd.num := by omega
  have hE : gE frame ≤ 2 * frame.parents.odd.num := by
    unfold gE
    split_ifs <;> omega
  have hlo : -(frame.parents.odd.den - frame.parents.odd.num) ≤ gLo frame := by
    unfold gLo
    split_ifs <;> omega
  have hEx : gE frame ≤ 2 * frame.parents.odd.num - 2 ∨ 2 - (frame.parents.odd.den - frame.parents.odd.num) ≤ gLo frame := by
    rcases frame.eps_unit with h | h
    · left
      unfold gE
      rw [if_pos h]
    · right
      unfold gLo
      rw [if_pos h]
  exact GradeCollision.grade_collision frame.parents.odd.num frame.parents.odd.den (gE frame) (gLo frame)
    (pg frame z) (pg frame b) hN hcp hodd hE hlo hEx
    (grade_mem frame hcut hz hzne) (grade_mem frame hcut hb hbne) hdiv

end FLatticePaper.NativeGrade
