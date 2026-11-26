import Mathlib
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! # No even H-cut point with an H-spectrum `t` at the top `s`-band (easy frames `2n ≤ d`)

For an even site `z` with `t = t(z)`, `s = s(z)`, the lattice identity `T·z₂ = n s − (d+n) t` (`FreeVOrdinate.T_mul_ordinate`) with
`T = d² + 2dn − n²`, the closed polygon `0 ≤ s ≤ T + 2n`, and the H spectrum `t` even in `[2, d+n−2]` cannot have
`s ≥ T + 2 − 2d`. The multiple `z₂` lies in `{n−1, n}`; `z₂ = n` forces `n ∣ t` with `0 < t < n`, and `z₂ = n−1` forces
`n ∣ t − d` with `t` in `(d−n, d+n−2]`, so `t = d`, which is odd. This is `gap_arith`; `VGap.no_gap` is the odd V analogue. -/

namespace FLatticePaper.HGap

open FLatticePaper FLatticePaper.Induction

theorem gap_arith {n d t s u : ℤ} (hn1 : 1 ≤ n) (hnd : 2 * n ≤ d) (hdodd : d % 2 = 1)
    (hcop : IsCoprime d n)
    (hid : (d ^ 2 + 2 * d * n - n ^ 2) * u = n * s - (d + n) * t)
    (ht1 : 2 ≤ t) (ht2 : t ≤ d + n - 2) (htev : t % 2 = 0)
    (hs1 : d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d ≤ s) (hs2 : s ≤ d ^ 2 + 2 * d * n - n ^ 2 + 2 * n) : False := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hL : 0 < d + n := by omega
  -- the multiple `u` lies in `{n − 1, n}`
  have hu_up : u ≤ n := by
    by_contra h
    push Not at h
    have h1 : (d ^ 2 + 2 * d * n - n ^ 2) * (n + 1) ≤ (d ^ 2 + 2 * d * n - n ^ 2) * u :=
      mul_le_mul_of_nonneg_left (by omega) hT.le
    have h2 : n * s ≤ n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 * n) := mul_le_mul_of_nonneg_left hs2 (by omega)
    have h3 : (d + n) * 2 ≤ (d + n) * t := mul_le_mul_of_nonneg_left ht1 hL.le
    nlinarith
  have hu_lo : n - 1 ≤ u := by
    by_contra h
    push Not at h
    have h1 : (d ^ 2 + 2 * d * n - n ^ 2) * u ≤ (d ^ 2 + 2 * d * n - n ^ 2) * (n - 2) :=
      mul_le_mul_of_nonneg_left (by omega) hT.le
    have h2 : n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d) ≤ n * s := mul_le_mul_of_nonneg_left hs1 (by omega)
    have h3 : (d + n) * t ≤ (d + n) * (d + n - 2) := mul_le_mul_of_nonneg_left ht2 hL.le
    nlinarith
  rcases (show u = n - 1 ∨ u = n by omega) with hu | hu
  · -- `u = n − 1`: `n ∣ d (t − d)`, so `t = d`, which is odd
    subst hu
    have h2 : n * (d ^ 2 + 2 * d * n - n ^ 2 + 2 - 2 * d) ≤ n * s := mul_le_mul_of_nonneg_left hs1 (by omega)
    have ht_lo : d - n + 1 ≤ t := by nlinarith
    have hdiv : n ∣ d * (t - d) := ⟨s - (d ^ 2 + 2 * d * n - n ^ 2) - t + 2 * d - n, by linear_combination hid⟩
    have hcop' : IsCoprime n d := hcop.symm
    have hdt : n ∣ t - d := hcop'.dvd_of_dvd_mul_left hdiv
    obtain ⟨c, hc⟩ := hdt
    have hc0 : c = 0 := by
      have hc1 : c < 1 := by nlinarith
      have hc2 : -1 < c := by nlinarith
      omega
    have : t = d := by
      rw [hc0] at hc
      linarith
    omega
  · -- `u = n`: `n ∣ (d + n) t`, so `n ∣ t` with `0 < t < n`
    rw [hu] at hid
    have hsT : (d + n) * t = n * (s - (d ^ 2 + 2 * d * n - n ^ 2)) := by linear_combination hid
    have hbound : t < n := by
      have h2 : n * (s - (d ^ 2 + 2 * d * n - n ^ 2)) ≤ n * (2 * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by omega)
      have h3 : (d + n) * t ≤ 2 * n * n := by linarith
      have h4 : 3 * n * t ≤ 2 * n * n := by nlinarith
      nlinarith
    have hdvd : n ∣ t * (d + n) := ⟨s - (d ^ 2 + 2 * d * n - n ^ 2), by rw [mul_comm t (d + n)]; exact hsT⟩
    have hcopL : IsCoprime n (d + n) := by
      obtain ⟨a, b, hab⟩ := hcop
      exact ⟨b - a, a, by linear_combination hab⟩
    have hnt : n ∣ t := hcopL.dvd_of_dvd_mul_right hdvd
    have hle : n ≤ t := Int.le_of_dvd (by omega) hnt
    omega

/-- **The gap at a free even H point.** For an even `z ∈ freeH` in the easy regime `2 num ≤ den`, `s(z) < T + 2 − 2d`. -/
theorem sGrade_lt_of_freeH_even (frame : ChildFrame) (hd2 : 2 * frame.child.num ≤ frame.child.den) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    frame.sGrade z < frame.child.periodDenominator + 2 - 2 * frame.child.den := by
  obtain ⟨hn0, hnd, -, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hcop : IsCoprime frame.child.den frame.child.num := frame.child_reduced.symm
  have hid := FLatticePaper.FreeVOrdinate.T_mul_ordinate frame z
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨hE, -, hsp⟩ := hz
  unfold ChildFrame.closedPolygon at hE
  simp only [Set.mem_setOf_eq, if_pos hev] at hE
  obtain ⟨-, -, -, hs_hi⟩ := hE
  -- the parity of `t` at an even site (`n`, `d` odd)
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have hev' : (z.1 + z.2) % 2 = 0 := by
    unfold EvenSite at hev
    exact hev
  have e : frame.tGrade z = (z.1 - z.2) + 2 * (a * z.1 - b * z.2) := by
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  have htev : frame.tGrade z % 2 = 0 := by
    rw [e]
    generalize a * z.1 - b * z.2 = X
    omega
  unfold ChildFrame.hSpectrum at hsp
  obtain ⟨ht1, ht2⟩ : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hsp with ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · exact ⟨h2, h3⟩
    · omega
  by_contra hcon
  push Not at hcon
  rw [hT] at hcon hs_hi hid
  exact FLatticePaper.HGap.gap_arith (n := frame.child.num) (d := frame.child.den) (t := frame.tGrade z)
    (s := frame.sGrade z) (u := z.2) (by omega) hd2 hdodd hcop hid ht1 ht2 htev hcon hs_hi

end FLatticePaper.HGap
