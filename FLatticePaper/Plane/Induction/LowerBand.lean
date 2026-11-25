import FLatticePaper.Plane.Induction.LowerBandCore
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Coherence
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.Binary

/-! # The lower input of an even free V root lies in the V band

For an even free V root `z` of a child frame `n/d` and a sign `δ = ±1`, the lower input `y = (z.1, z.2 - δ)` lies in
`frame.vBand` (given `z ≠ vFirst`, and `z ≠ vLast` when `δ = -1`). Hence `laplacian G y = 0` for every field `G` with the
harmonic strip (`ChildFrame.laplacian_eq_zero_of_vBand`): this is the lap-0 half of `hX3`, with the strips supplied by
`hstrip_of_strong` at the conjugate word. The membership `y ∈ freeV` is a separate claim (section B).

The arithmetic is in `LowerBandCore`; this file only translates the frame into integers (`tGrade`, `sGrade`, `vBand`). -/

namespace FLatticePaper.Induction

open LowerBandCore

namespace ChildFrame
variable (frame : ChildFrame)

theorem child_num_odd : frame.child.num % 2 = 1 := by
  obtain ⟨u, v, huv⟩ := frame.child_reduced
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rcases Int.emod_two_eq_zero_or_one frame.child.num with h | h
  · exfalso
    have hd : frame.child.den % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : (2:ℤ) ∣ frame.child.num := Int.dvd_of_emod_eq_zero h
    obtain ⟨m, hm⟩ : (2:ℤ) ∣ frame.child.den := Int.dvd_of_emod_eq_zero hd
    have h2 : (2:ℤ) ∣ 1 := ⟨u * k + v * m, by rw [hk, hm] at huv; linear_combination -huv⟩
    omega
  · exact h

theorem ident_a (z : Site) :
    frame.child.periodDenominator * z.1
      = (frame.child.den - frame.child.num) * frame.tGrade z + frame.child.den * frame.sGrade z := by
  obtain ⟨-, -, -, -, hP⟩ := frame.child_facts
  unfold ChildFrame.tGrade ChildFrame.sGrade
  rw [hP]; ring

theorem ident_b (z : Site) :
    frame.child.periodDenominator * z.2
      = frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z := by
  obtain ⟨-, -, -, -, hP⟩ := frame.child_facts
  unfold ChildFrame.tGrade ChildFrame.sGrade
  rw [hP]; ring

/-- The lower input of an even free V root of a child frame lies in the V band. -/
theorem lower_in_vBand {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hzF : z ≠ vFirst) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hδz : δ = 1 ∨ z ≠ frame.vLast) :
    (z.1, z.2 - δ) ∈ frame.vBand := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hodd := frame.child_num_odd
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hcoprime : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
  obtain ⟨u, v, huv⟩ := hcoprime
  have hcop : IsCoprime frame.child.den (frame.child.den - frame.child.num) :=
    ⟨u + v, -u, by linear_combination huv⟩
  have hA := frame.ident_a z
  have hB := frame.ident_b z
  obtain ⟨hzcp, hzn, hzspec⟩ := hz
  have hpz : 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧ 0 ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num := by
    rcases (frame.mem_closedPolygon_iff z).mp hzcp with h | h
    · exact h.2
    · exact absurd hev h.1
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hpz
  have hsv : frame.sGrade z % 2 = 0 ∧
      ((0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
        (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2)) := hzspec
  obtain ⟨hsE, hspec⟩ := hsv
  have hnot : frame.tGrade z < 2 * frame.child.num - frame.child.periodDenominator ∨
      frame.sGrade z < 2 * frame.child.num + 2 := by
    by_contra hc
    push Not at hc
    apply hzn
    rw [frame.mem_closedPolygon_iff]
    have hodd' : ¬ EvenSite (z.1 - 1, z.2) := by
      show ¬ ((z.1 - 1 + z.2) % 2 = 0)
      omega
    right
    refine ⟨hodd', ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_sub_x]; omega
    · rw [frame.tGrade_sub_x]; omega
    · rw [frame.sGrade_sub_x]; omega
    · rw [frame.sGrade_sub_x]; omega
  have hs2n : frame.sGrade z ≤ 2 * frame.child.num :=
    core_s_le hn0 hnd hdn hd3 hP hcop hA hp1 hp3 hsE hspec hnot
  have hTb := core_t_bounds hn0 hnd hdn hd3 hP hA hp1 hp2 hp3 hs2n
  obtain ⟨hlo, hhi⟩ := hTb
  have hcoprime' : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := ⟨u, v, huv⟩
  rcases hδ with rfl | rfl
  · -- δ = 1: the lower input is (z.1, z.2 - 1)
    have hs2 : 2 ≤ frame.sGrade z := by
      have hne : frame.sGrade z ≠ 0 := by
        intro h0
        rw [h0] at hA hB
        obtain ⟨ha0, hb0⟩ := core_s0 hn0 hdn hP hcoprime' hodd hA hB hev' hlo hhi
        exact hzF (Prod.ext ha0 hb0)
      omega
    have hyeven : ¬ EvenSite (z.1, z.2 - 1) := by
      show ¬ ((z.1 + (z.2 - 1)) % 2 = 0)
      omega
    refine (frame.mem_vBand_iff _).mpr ⟨?_, ?_⟩
    · rw [frame.mem_closedPolygon_iff]
      right
      refine ⟨hyeven, ?_, ?_, ?_, ?_⟩
      · rw [frame.tGrade_sub_y]; omega
      · rw [frame.tGrade_sub_y]; omega
      · rw [frame.sGrade_sub_y]; omega
      · rw [frame.sGrade_sub_y]; omega
    · rw [if_neg hyeven, frame.sGrade_sub_y]
      omega
  · -- δ = -1: the lower input is (z.1, z.2 + 1)
    have hzv : z ≠ frame.vLast := hδz.resolve_left (by norm_num)
    have hs_ne : frame.sGrade z ≠ 2 * frame.child.num := by
      intro h2
      rw [h2] at hA hB
      obtain ⟨ha, hb⟩ := core_s2n hn0 hdn hP hcoprime' hodd hA hB hev' hlo hhi
      exact hzv (by unfold ChildFrame.vLast; exact Prod.ext ha hb)
    have hs_le : frame.sGrade z ≤ 2 * frame.child.num - 2 := by omega
    have hyeven : ¬ EvenSite (z.1, z.2 - -1) := by
      show ¬ ((z.1 + (z.2 - -1)) % 2 = 0)
      omega
    refine (frame.mem_vBand_iff _).mpr ⟨?_, ?_⟩
    · rw [frame.mem_closedPolygon_iff]
      right
      refine ⟨hyeven, ?_, ?_, ?_, ?_⟩
      · rw [show z.2 - -1 = z.2 + 1 by ring, frame.tGrade_add_y]; omega
      · rw [show z.2 - -1 = z.2 + 1 by ring, frame.tGrade_add_y]; omega
      · rw [show z.2 - -1 = z.2 + 1 by ring, frame.sGrade_add_y]; omega
      · rw [show z.2 - -1 = z.2 + 1 by ring, frame.sGrade_add_y]; omega
    · rw [if_neg hyeven, show z.2 - -1 = z.2 + 1 by ring, frame.sGrade_add_y]
      omega

/-- The vertical band carries Laplacian zero from the harmonic strip alone, on the range `[2 - 2d, 2(d+n) - 2]` that
`Q30Strips.hstrip_of_strong` provides (the shifted sites of the band stay in that range since `d ≥ n + 2`). -/
theorem laplacian_eq_zero_of_vBand_harm {G : Field}
    (hh : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → G z = harmonicGrid z)
    {w : Site} (hw : w ∈ frame.vBand) : laplacian G w = 0 := by
  obtain ⟨hN1, hNlt, hdn, hd3, -⟩ := frame.child_facts
  obtain ⟨-, hwin⟩ := (frame.mem_vBand_iff w).mp hw
  have hlap := harmonicGrid_harmonic w
  unfold laplacian at hlap ⊢
  by_cases he : EvenSite w
  · rw [if_pos he] at hwin
    simp only [incomingNeg, incomingPos, if_pos he] at hlap ⊢
    have h0 : G w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : G (w.1 - 1, w.2) = harmonicGrid (w.1 - 1, w.2) :=
      hh _ (by rw [frame.sGrade_sub_x w]; omega) (by rw [frame.sGrade_sub_x w]; omega)
    have h2 : G (w.1 + 1, w.2) = harmonicGrid (w.1 + 1, w.2) :=
      hh _ (by rw [frame.sGrade_add_x w]; omega) (by rw [frame.sGrade_add_x w]; omega)
    rw [h0, h1, h2]
    linarith
  · rw [if_neg he] at hwin
    simp only [incomingNeg, incomingPos, if_neg he] at hlap ⊢
    have h0 : G w = harmonicGrid w := hh w (by omega) (by omega)
    have h1 : G (w.1, w.2 - 1) = harmonicGrid (w.1, w.2 - 1) :=
      hh _ (by rw [frame.sGrade_sub_y w]; omega) (by rw [frame.sGrade_sub_y w]; omega)
    have h2 : G (w.1, w.2 + 1) = harmonicGrid (w.1, w.2 + 1) :=
      hh _ (by rw [frame.sGrade_add_y w]; omega) (by rw [frame.sGrade_add_y w]; omega)
    rw [h0, h1, h2]
    linarith

/-- The lap-0 half of `hX3`: the Laplacian of the lower input of an even free V root vanishes, given the harmonic strip. -/
theorem lap_lower_eq_zero {G : Field}
    (hh : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → G z = harmonicGrid z)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ vFirst) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hδz : δ = 1 ∨ z ≠ frame.vLast) :
    laplacian G (z.1, z.2 - δ) = 0 :=
  frame.laplacian_eq_zero_of_vBand_harm hh (frame.lower_in_vBand hz hev hzF hδ hδz)

end ChildFrame

end FLatticePaper.Induction
