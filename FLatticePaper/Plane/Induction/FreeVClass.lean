import FLatticePaper.Plane.Induction.LiftPsi
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.ParentGradeKernel
import FLatticePaper.Plane.Induction.OddFreeH
import FLatticePaper.Plane.Induction.PriceInputs
import FLatticePaper.Plane.Induction.SheetStars

/-! The class decomposition of a free V white `z ≠ V_end` by its ordinate class `i = z.2 mod L'`, `L' = D + N`.

Either `z = b + k·V_p` for the cut base `b` of the ordinate `i`, with `pg z = pg b` (`pg z = L'·z₁ + (D−N)·z₂`, `V_p = tipVertex`);
or `pg z = L'` and `z = (1,0) + k·V_p` (the H_0 class). -/

namespace FLatticePaper.FreeVClass

open Farey FLatticePaper FLatticePaper.Induction

theorem freeV_class {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {z : Site}
    (hz : z ∈ (frameAt word).freeV) (hne : z ≠ (frameAt word).vLast) :
    (∃ b : Site, b ∈ (frameAt word).freeV ∧ 0 ≤ b.2 ∧ b.2 < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) ∧
        NativeGrade.pg (frameAt word) b = NativeGrade.pg (frameAt word) z ∧
        z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) = b.2 ∧
        z = b + (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) • TipVertex.tipVertex (frameAt word)) ∨
    (NativeGrade.pg (frameAt word) z = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) ∧
      z = (1, 0) + (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) • TipVertex.tipVertex (frameAt word)) := by
  obtain ⟨hN1, hND, hD2, hn0, hd0, hn, hd, heps, hε⟩ := PriceInputs.pdata h
  have hLr := LiftPsi.r_lt_L (frameAt word)
  have hN : 0 < (frameAt word).parents.odd.num := by omega
  have hL : 0 < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by omega
  have hodd := (SheetStars.parent_sums_odd h).1
  have hcop := LiftPsi.isCoprime_ND_of_frame (frameAt word)
  have hcut := CutOnePerProper.cutOnePerOrdinate_of_proper h
  have hz2 : z.2 = z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) := by rw [Int.emod_def]; ring
  have hi0 : 0 ≤ z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := Int.emod_nonneg _ hL.ne'
  have hi1 : z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := Int.emod_lt_of_pos _ hL
  obtain ⟨xb, hxb, hxu⟩ := hcut (z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) hi0 (by unfold FreeEnum.period; omega)
  have hbne : ((xb, z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) : Site) ≠ (frameAt word).vLast :=
    NativeGrade.ne_vLast_of_ordinate (frameAt word) (by show _ < (frameAt word).child.den + (frameAt word).child.num - 1; omega)
  have htri := NativeGrade.pg_trichotomy (frameAt word) hcut hN hz hne hxb hbne (z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))
    (by dsimp only; linarith [hz2])
  rcases htri with hEq | ⟨hzg0, hbgr⟩ | ⟨hzgr, hbg0⟩
  · left
    refine ⟨(xb, z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)), hxb, hi0, hi1, hEq.symm, rfl, ?_⟩
    exact LiftPsi.eq_add_vp_of_pg (frameAt word) hEq (by dsimp only; linarith [hz2])
  · exfalso
    have hb' : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * xb + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := hbgr
    obtain ⟨k, hk1, hk2⟩ := ParentGradeKernel.same_grade_vp _ _ hcop hodd (by omega) xb (z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) 1 0
      (by linarith [hb'])
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hk | hk | hk
      · have := mul_neg_of_pos_of_neg hL hk
        linarith
      · exact hk
      · have := mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ k by omega) hL.le
        linarith
    subst hk0
    have hi_zero : z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) = 0 := by linarith
    have hor : ((0 : ℤ), z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) ∈ (frameAt word).freeV := by
      rw [hi_zero]; exact origin_mem_freeV (frameAt word)
    have hxb0 := hxu 0 hor
    have hxb1 : xb = 1 := by linarith
    omega
  · right
    have hz' : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1 + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2 = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * 1 + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * 0 := by
      have := hzgr
      dsimp only [NativeGrade.pg] at this
      linarith
    obtain ⟨k, hk1, hk2⟩ := ParentGradeKernel.same_grade_vp _ _ hcop hodd (by omega) z.1 z.2 1 0 hz'
    have hkq : k = z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by
      have hm : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (k - z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) = z.2 % ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) := by linarith [hz2, hk2]
      rcases lt_trichotomy (k - z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)) 0 with hk | hk | hk
      · have := mul_neg_of_pos_of_neg hL hk
        linarith
      · linarith
      · have := mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ k - z.2 / ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) by omega) hL.le
        linarith
    subst hkq
    refine ⟨hzgr, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, TipVertex.tipVertex]
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, TipVertex.tipVertex]
      linarith

end FLatticePaper.FreeVClass
