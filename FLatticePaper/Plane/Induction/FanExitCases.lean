import FLatticePaper.Plane.Induction.BoundaryPair
import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.RowPair
import FLatticePaper.Plane.Induction.FreeVWindow

/-! # The exit classification of the rotated fan (Q41 section 3, steps 1 to 4)

Let `x` be a rotated exit point with `x + U` in the closed polygon, outside the open rectangle, and with `x_2 ≥ 0` and
`x_1 + x_2 ≥ 1` (these come from the cone bounds of the fan). Then `x` is a V-exit (a free V site with `x_2 ≤ L − 1`) or an H-exit
(`x + U − V` a free H site, not the corner `(1,0)`). The bottom H and the left V arcs are impossible. -/

namespace FLatticePaper.FanExitCases

open FLatticePaper FLatticePaper.Induction

theorem fan_exit_class (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {x : Site} (hx0 : 0 ≤ x.2)
    (hsum : 1 ≤ x.1 + x.2)
    (hz : x + RowAt.Uvec frame ∈ frame.closedPolygon) (hnot : ¬ frame.openRect (x + RowAt.Uvec frame)) :
    (x ∈ frame.freeV ∧ x.2 ≤ frame.child.den + frame.child.num - 1) ∨
    ((x.1 + frame.child.den - (frame.child.num - frame.child.den),
        x.2 + frame.child.num - (frame.child.num + frame.child.den)) ∈ frame.freeH ∧
      (x.1 + frame.child.den - (frame.child.num - frame.child.den),
        x.2 + frame.child.num - (frame.child.num + frame.child.den)) ≠ (1, 0)) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hU : RowAt.Uvec frame = (frame.child.den, frame.child.num) := rfl
  rcases FLatticePaper.BoundaryPair.boundary_arc frame hz hnot with hH | hV | hVU | hHV
  · -- bottom H: impossible (t ≥ 2 forces z_2 ≤ n − 1, so x_2 < 0)
    exfalso
    obtain ⟨k, hk, hkz⟩ := HChain.freeH_eq_hpath_of_mem frame hH
    have hz1 : (x + RowAt.Uvec frame).1 ≤ frame.child.den := by
      rw [hkz, RowPair.hpath_fst frame k]
      omega
    have ht : 2 ≤ frame.tGrade (x + RowAt.Uvec frame) := by
      have hsp := hH.2.2
      unfold ChildFrame.hSpectrum at hsp
      rcases hsp with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
      · omega
      · omega
    have htd : frame.tGrade (x + RowAt.Uvec frame) =
        frame.child.num * (x + RowAt.Uvec frame).1 - frame.child.den * (x + RowAt.Uvec frame).2 := by
      unfold ChildFrame.tGrade
      ring
    have hz2 : frame.child.num ≤ (x + RowAt.Uvec frame).2 := by
      rw [Prod.snd_add, hU]
      simp only
      omega
    have h1 : frame.child.num * (x + RowAt.Uvec frame).1 ≤ frame.child.num * frame.child.den :=
      mul_le_mul_of_nonneg_left hz1 (by omega)
    have h2 : frame.child.den * frame.child.num ≤ frame.child.den * (x + RowAt.Uvec frame).2 :=
      mul_le_mul_of_nonneg_left hz2 (by omega)
    nlinarith
  · -- left V: impossible (s ≤ L − 2 forces z_1 ≤ 0, and then x_1 + x_2 ≤ −1)
    exfalso
    obtain ⟨k, hk, hkz⟩ := VChain.freeV_eq_vpath_of_mem frame hV
    have hz2 : (x + RowAt.Uvec frame).2 = (k : ℤ) := by
      rw [hkz, VChain.vpath_ord frame k]
    have hs : frame.sGrade (x + RowAt.Uvec frame) ≤ frame.child.den + frame.child.num - 2 := by
      by_cases he : EvenSite (x + RowAt.Uvec frame)
      · have := FreeVWindow.freeV_even_window frame hV he
        omega
      · have := FreeVWindow.freeV_odd_window frame hV he
        omega
    have hsd : frame.sGrade (x + RowAt.Uvec frame) =
        (frame.child.den + frame.child.num) * (x + RowAt.Uvec frame).1 +
          (frame.child.den - frame.child.num) * (x + RowAt.Uvec frame).2 := by
      unfold ChildFrame.sGrade
      ring
    have hz2n : 0 ≤ (x + RowAt.Uvec frame).2 := by omega
    have hdn : 0 ≤ frame.child.den - frame.child.num := by omega
    have hpos : 0 ≤ (frame.child.den - frame.child.num) * (x + RowAt.Uvec frame).2 :=
      mul_nonneg hdn hz2n
    have hz1 : (x + RowAt.Uvec frame).1 ≤ 0 := by
      by_contra hc
      push Not at hc
      have : (frame.child.den + frame.child.num) * 1 ≤
          (frame.child.den + frame.child.num) * (x + RowAt.Uvec frame).1 :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    have hk' : (k : ℤ) ≤ frame.child.den + frame.child.num - 1 := by omega
    have hxsum : x.1 + x.2 = (x + RowAt.Uvec frame).1 + (x + RowAt.Uvec frame).2 -
        (frame.child.den + frame.child.num) := by
      rw [hU]
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    omega
  · -- right V: the V-exit
    left
    have hxV : x ∈ frame.freeV := by
      have e : x = ((x + RowAt.Uvec frame).1 - frame.child.den, (x + RowAt.Uvec frame).2 - frame.child.num) := by
        ext <;> simp [hU]
      rw [e]
      exact hVU
    obtain ⟨k, hk, hkx⟩ := VChain.freeV_eq_vpath_of_mem frame hxV
    refine ⟨hxV, ?_⟩
    rw [hkx, VChain.vpath_ord frame k]
    omega
  · -- top H: the H-exit
    right
    have hsite : (x + RowAt.Uvec frame).1 - (frame.child.num - frame.child.den) =
        x.1 + frame.child.den - (frame.child.num - frame.child.den) := by
      rw [hU]; simp only [Prod.fst_add]
    have hsite2 : (x + RowAt.Uvec frame).2 - (frame.child.num + frame.child.den) =
        x.2 + frame.child.num - (frame.child.num + frame.child.den) := by
      rw [hU]; simp only [Prod.snd_add]
    have hH : frame.freeH (x.1 + frame.child.den - (frame.child.num - frame.child.den),
        x.2 + frame.child.num - (frame.child.num + frame.child.den)) := by
      rw [← hsite, ← hsite2]
      exact hHV
    refine ⟨hH, ?_⟩
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega

end FLatticePaper.FanExitCases
