import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.TipVertex
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.NativeCases

/-! Task 72 / item hFV: the tip vertex maps the free H arc into the closed polygon.

For `z ∈ freeH`, `z + tipVertex ∈ closedPolygon`. The proof uses the spectrum of `t(z)` (`hSpectrum`), the `s`-window of `freeH`
(`freeH_sGrade_bounds`), the tip grades `t(tip) = −tipB`, `s(tip) = 2 ε`, and the inequality `0 ≤ tipB ≤ T` (`tipB_nonneg`,
`tipB_le_periodDenominator`), which holds because `d = 2D + d_q`, `n = 2N + n_q`, `N ≤ D`, `d_q ≥ 1`. -/

namespace FLatticePaper.HFVTip

open FLatticePaper FLatticePaper.Induction

/-- `tipB ≥ 0`: `tipB = (d + n) D + (d − n) N` with `D > 0`, `N ≥ 0`, `0 < n < d`. -/
theorem tipB_nonneg (frame : ChildFrame) : 0 ≤ TipVertex.tipB frame := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hDpos, hN0, -⟩ := frame.valid.odd_bounds
  unfold TipVertex.tipB
  have h1 : 0 ≤ (frame.child.den + frame.child.num) * frame.parents.odd.den := by
    apply mul_nonneg <;> omega
  have h2 : 0 ≤ (frame.child.den - frame.child.num) * frame.parents.odd.num := by
    apply mul_nonneg <;> omega
  linarith

/-- `tipB ≤ T`, from `d = 2D + d_q` (`d_q ≥ 1`), `n = 2N + n_q` (`n_q ≥ 0`) and `N ≤ D`. -/
theorem tipB_le_periodDenominator (frame : ChildFrame) :
    TipVertex.tipB frame ≤ frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, -, -, hT⟩ := frame.child_facts
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq, hnq, -⟩ := frame.valid.even_bounds
  have hcd := ZoneI1.child_den_eq frame
  have hcn := ZoneI1.child_num_eq frame
  unfold TipVertex.tipB
  rw [hT]
  have hND : frame.parents.odd.num ≤ frame.parents.odd.den := by omega
  have h1 : (frame.child.den - frame.child.num) * frame.parents.odd.num ≤
      (frame.child.den - frame.child.num) * frame.parents.odd.den :=
    mul_le_mul_of_nonneg_left hND (by omega)
  have h2 : 2 * frame.parents.odd.den ≤ frame.child.den - 1 := by omega
  have h3 : frame.child.den * (2 * frame.parents.odd.den) ≤ frame.child.den * (frame.child.den - 1) :=
    mul_le_mul_of_nonneg_left h2 (by omega)
  have h4 : 0 ≤ frame.child.num * (2 * frame.child.den - frame.child.num) :=
    mul_nonneg (by omega) (by omega)
  nlinarith [h1, h3, h4]

/-- **The tip vertex maps `freeH` into the closed polygon.** -/
theorem tipVertex_mem_closedPolygon (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    z + TipVertex.tipVertex frame ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hB0 := tipB_nonneg frame
  have hB1 := tipB_le_periodDenominator frame
  obtain ⟨hsa, hsb⟩ := ShortRoute.freeH_sGrade_bounds frame hz
  have hsp : frame.hSpectrum (frame.tGrade z) := hz.2.2
  have heps : -1 ≤ frame.eps ∧ frame.eps ≤ 1 := by
    rcases frame.eps_unit with h | h <;> omega
  have ht : frame.tGrade (z + TipVertex.tipVertex frame) = frame.tGrade z - TipVertex.tipB frame := by
    rw [frame.tGrade_add_pt, TipVertex.tGrade_tipVertex]
    ring
  have hs : frame.sGrade (z + TipVertex.tipVertex frame) = frame.sGrade z + 2 * frame.eps := by
    rw [show frame.sGrade (z + TipVertex.tipVertex frame) =
        frame.sGrade z + frame.sGrade (TipVertex.tipVertex frame) from by
      unfold ChildFrame.sGrade
      simp only [Prod.fst_add, Prod.snd_add]
      ring, TipVertex.sGrade_tipVertex]
  have hpar := NativeCases.tGrade_parity frame z
  have hEv : EvenSite (z + TipVertex.tipVertex frame) ↔ EvenSite z := by
    have := TipVertex.evenSite_tipVertex frame
    unfold EvenSite at *
    simp only [Prod.fst_add, Prod.snd_add] at *
    omega
  unfold ChildFrame.closedPolygon
  rw [Set.mem_setOf_eq]
  by_cases he : EvenSite z
  · rw [if_pos (hEv.mpr he)]
    have hte : frame.tGrade z % 2 = 0 := by
      rw [hpar]; unfold EvenSite at he; omega
    have hsp' := hsp
    unfold ChildFrame.hSpectrum at hsp'
    rw [ht, hs]
    rcases hsp' with ⟨-, h2, hL⟩ | ⟨hodd, -, -⟩
    · refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · omega
  · rw [if_neg (fun h => he (hEv.mp h))]
    have hto : frame.tGrade z % 2 = 1 := by
      rw [hpar]; unfold EvenSite at he; omega
    have hsp' := hsp
    unfold ChildFrame.hSpectrum at hsp'
    rw [ht, hs]
    rcases hsp' with ⟨he', -, -⟩ | ⟨-, hnt, htd⟩
    · omega
    · refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end FLatticePaper.HFVTip
