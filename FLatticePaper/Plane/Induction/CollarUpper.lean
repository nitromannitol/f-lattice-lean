import FLatticePaper.Plane.Induction.CollarBottomBand

/-! Task 72 (hcollar, band (a), the H-arc upper bounds).

The identity `L · s(x) = (x₁ + x₂) · T + 2 n · t(x)` (with `L = d + n`, `T = d² + 2dn − n²`) holds for every site. It turns the
`s`-bounds of the bottom corners into bounds on the diagonal index `k = x₁ + x₂`.

* Even H points of the closed polygon have `k ≤ L − 2`, and `k = L − 2` forces `v = (d − 1, n − 1)`.
* Odd H points of the closed polygon have `k ≤ L − 1`, and `k = L − 1` forces `v = (d, n − 1)`. -/

namespace FLatticePaper.CollarUpper

open Farey FLatticePaper FLatticePaper.Induction

/-- The grade identity `L · s(x) = (x₁ + x₂) · T + 2 n · t(x)`. -/
theorem L_mul_sGrade (frame : ChildFrame) (x : Site) :
    (frame.child.den + frame.child.num) * frame.sGrade x =
      (x.1 + x.2) * frame.child.periodDenominator + 2 * frame.child.num * frame.tGrade x := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [hT]
  unfold ChildFrame.sGrade ChildFrame.tGrade
  ring

/-- The even H points of the closed polygon: `x₁ + x₂ ≤ L − 2`, with equality only at `(d − 1, n − 1)`. -/
theorem even_H_k_bounds (frame : ChildFrame) {v : Site} (hv : EvenSite v) (hE : v ∈ frame.closedPolygon)
    (hsp : frame.hSpectrum (frame.tGrade v)) :
    v.1 + v.2 ≤ frame.child.den + frame.child.num - 2 ∧
      (v.1 + v.2 = frame.child.den + frame.child.num - 2 → v = (frame.child.den - 1, frame.child.num - 1)) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hid := L_mul_sGrade frame v
  have hEv : 2 - frame.child.periodDenominator ≤ frame.tGrade v ∧
      frame.tGrade v ≤ frame.child.den + frame.child.num - 2 ∧ 0 ≤ frame.sGrade v ∧
      frame.sGrade v ≤ frame.child.periodDenominator + 2 * frame.child.num := by
    rw [frame.mem_closedPolygon_iff] at hE
    rcases hE with h | h
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · exact absurd hv h.1
  have ht : 2 ≤ frame.tGrade v := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨-, h1, -⟩ | ⟨h3, -, -⟩
    · exact h1
    · exfalso
      obtain ⟨c, hc⟩ := frame.tGrade_parity v
      unfold EvenSite at hv
      omega
  obtain ⟨-, htL, hs0, hsE⟩ := hEv
  have htL' : frame.tGrade v ≤ frame.child.den + frame.child.num - 2 := htL
  have hKpar : (v.1 + v.2) % 2 = 0 := by
    unfold EvenSite at hv
    omega
  -- the bound `K ≤ L`
  have hKL : v.1 + v.2 ≤ frame.child.den + frame.child.num := by
    by_contra hc
    have hc2 : frame.child.den + frame.child.num + 2 ≤ v.1 + v.2 := by omega
    have h1 : (frame.child.den + frame.child.num) * frame.sGrade v ≤
        (frame.child.den + frame.child.num) * (frame.child.periodDenominator + 2 * frame.child.num) :=
      mul_le_mul_of_nonneg_left hsE (by omega)
    have h2 : (frame.child.den + frame.child.num + 2) * frame.child.periodDenominator ≤
        (v.1 + v.2) * frame.child.periodDenominator :=
      mul_le_mul_of_nonneg_right hc2 (by rw [hT]; nlinarith)
    rw [hid] at h1
    rw [hT] at h1 h2
    nlinarith
  -- `K = L` is impossible: the floor law gives `t(v) = 0`
  have hKne : v.1 + v.2 ≠ frame.child.den + frame.child.num := by
    intro hKL'
    have hfl := even_spectrum_floor frame hv hsp
    have hLne : (frame.child.den + frame.child.num) ≠ 0 := by omega
    have hm : (v.1 + v.2) / 2 = (frame.child.den + frame.child.num) / 2 := by
      rw [hKL']
    have h2n : 2 * frame.child.num * ((v.1 + v.2) / 2) = frame.child.num * (frame.child.den + frame.child.num) := by
      rw [hm]
      have : 2 * ((frame.child.den + frame.child.num) / 2) = frame.child.den + frame.child.num := by omega
      linear_combination frame.child.num * this
    rw [h2n, Int.mul_ediv_cancel _ hLne] at hfl
    have hv1 : v.1 = frame.child.den := by omega
    unfold ChildFrame.tGrade at ht
    rw [hv1, hfl] at ht
    nlinarith
  have hKlt : v.1 + v.2 ≤ frame.child.den + frame.child.num - 2 := by omega
  refine ⟨hKlt, fun hEq => ?_⟩
  -- `K = L − 2`: the floor law gives `v.2 = n − 1`
  have hfl := even_spectrum_floor frame hv hsp
  have hm : (v.1 + v.2) / 2 = (frame.child.den + frame.child.num - 2) / 2 := by
    rw [hEq]
  have hLne : (frame.child.den + frame.child.num) ≠ 0 := by omega
  have hlin : 2 * frame.child.num * ((v.1 + v.2) / 2) =
      (frame.child.den + frame.child.num - 2 * frame.child.num) +
        (frame.child.num - 1) * (frame.child.den + frame.child.num) := by
    rw [hm]
    have : 2 * ((frame.child.den + frame.child.num - 2) / 2) = frame.child.den + frame.child.num - 2 := by omega
    linear_combination frame.child.num * this
  rw [hlin, Int.add_mul_ediv_right _ _ hLne, Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add] at hfl
  have hv2 : v.2 = frame.child.num - 1 := hfl
  have hv1 : v.1 = frame.child.den - 1 := by omega
  exact Prod.ext hv1 hv2

/-- The odd H points of the closed polygon: `x₁ + x₂ ≤ L − 1`, with equality only at `(d, n − 1)`. -/
theorem odd_H_k_bounds (frame : ChildFrame) {v : Site} (hv : ¬ EvenSite v) (hE : v ∈ frame.closedPolygon)
    (hsp : frame.hSpectrum (frame.tGrade v)) :
    v.1 + v.2 ≤ frame.child.den + frame.child.num - 1 ∧
      (v.1 + v.2 = frame.child.den + frame.child.num - 1 → v = (frame.child.den, frame.child.num - 1)) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hid := L_mul_sGrade frame v
  have hEv : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade v ∧
      frame.tGrade v ≤ frame.child.den ∧ 2 - frame.child.den + frame.child.num ≤ frame.sGrade v ∧
      frame.sGrade v ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
    rw [frame.mem_closedPolygon_iff] at hE
    rcases hE with h | h
    · exact absurd h.1 hv
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  have ht : frame.child.num ≤ frame.tGrade v := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
    · exfalso
      obtain ⟨c, hc⟩ := frame.tGrade_parity v
      unfold EvenSite at hv
      omega
    · exact h2
  obtain ⟨-, htd, hs0, hsE⟩ := hEv
  have hKpar : (v.1 + v.2) % 2 = 1 := by
    unfold EvenSite at hv
    omega
  have hKL : v.1 + v.2 ≤ frame.child.den + frame.child.num - 1 := by
    by_contra hc
    have hc2 : frame.child.den + frame.child.num ≤ v.1 + v.2 := by omega
    have hc3 : frame.child.den + frame.child.num + 1 ≤ v.1 + v.2 := by omega
    have h1 : (frame.child.den + frame.child.num) * frame.sGrade v ≤
        (frame.child.den + frame.child.num) * (frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :=
      mul_le_mul_of_nonneg_left hsE (by omega)
    have h2 : (frame.child.den + frame.child.num + 1) * frame.child.periodDenominator ≤
        (v.1 + v.2) * frame.child.periodDenominator :=
      mul_le_mul_of_nonneg_right hc3 (by rw [hT]; nlinarith)
    rw [hid] at h1
    rw [hT] at h1 h2
    nlinarith
  refine ⟨hKL, fun hEq => ?_⟩
  -- `K = L − 1`: the value of `v.2` is forced to be `n − 1`
  unfold ChildFrame.tGrade at ht htd
  have hx : v.1 = frame.child.den + frame.child.num - 1 - v.2 := by omega
  have hm1 : -1 ≤ v.2 - frame.child.num := by
    by_contra h
    have h' : v.2 - frame.child.num ≤ -2 := by omega
    nlinarith
  have hm2 : v.2 - frame.child.num ≤ -1 := by
    by_contra h
    have h' : 0 ≤ v.2 - frame.child.num := by omega
    nlinarith
  have hy : v.2 = frame.child.num - 1 := by omega
  have hx' : v.1 = frame.child.den := by omega
  exact Prod.ext hx' hy

end FLatticePaper.CollarUpper
