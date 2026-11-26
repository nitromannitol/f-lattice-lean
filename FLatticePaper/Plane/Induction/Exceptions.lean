import FLatticePaper.Plane.Induction.ExteriorNbr
import FLatticePaper.Plane.Induction.BottomExcl

/-! # The exceptional strict centres next to `hLast` and `vLast` (step (5))

`hLast = (d, n-1)`: the only strict site within one pixel of `hLast` is `(d-1, n)`, which is black (`StripColours.lap_den_sub_one`).
`vLast = (n-d+1, n+d-1)`: the strict sites within one pixel are `V + (2,-1) = vLast + (1,0)` (black, `lap_vLast_east`) and
`vLast + (1,-1)`, which has no bottom and no right witness (proved in `vLast_no_witness`, with `T ≥ 3(d+n)`). -/

namespace FLatticePaper.Exceptions

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CrossingLattice
  FLatticePaper.AlignedClassGrade FLatticePaper.AlignedClassSite FLatticePaper.ExteriorNbr

/-- The grade-level case split for `hLast`: the offsets `(i,j)` from `(d, n-1)` with the strictness of the centre. -/
theorem hLast_grade (n d T i j : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hi1 : -1 ≤ i) (hi2 : i ≤ 1) (hj1 : -1 ≤ j) (hj2 : j ≤ 1)
    (hS : SIG n d T (d + n * i - d * j) ((T - d + n) + (d + n) * i + (d - n) * j)) :
    i = -1 ∧ j = 1 := by
  have hi : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  have hj : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp only [SIG] at hS <;> omega

/-- **The strict centre next to `hLast` is `(d-1, n)`.** -/
theorem hLast_strict {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (c : Site) (hc1 : |c.1 - d| ≤ 1) (hc2 : |c.2 - (n - 1)| ≤ 1)
    (hS : StrictInterior n d c) : c = (d - 1, n) := by
  have hb1 := abs_le.mp hc1
  have hb2 := abs_le.mp hc2
  have hSg := (strict_iff_SIG' hn hd c).mp hS
  have e1 : w1t n d c = d + n * (c.1 - d) - d * (c.2 - (n - 1)) := by unfold w1t; ring
  have e2 : w1s n d c = (w1T n d - d + n) + (d + n) * (c.1 - d) + (d - n) * (c.2 - (n - 1)) := by
    unfold w1s w1T; ring
  rw [e1, e2] at hSg
  obtain ⟨hi, hj⟩ := hLast_grade n d (w1T n d) (c.1 - d) (c.2 - (n - 1)) hn hd hn1 hnd
    hb1.1 hb1.2 hb2.1 hb2.2 hSg
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-! ## (5c): the strict centres next to `K` with a bottom or left witness -/

/-- The strict offsets from `K`: only `(-1,0)` and `(-1,1)`. -/
theorem K_grade_offsets (n d T i j : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hi1 : -1 ≤ i) (hi2 : i ≤ 1) (hj1 : -1 ≤ j) (hj2 : j ≤ 1)
    (hS : SIG n d T (n * i - d * j) (T + (d + n) * i + (d - n) * j)) :
    (i = -1 ∧ j = 0) ∨ (i = -1 ∧ j = 1) := by
  have hi : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  have hj : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp only [SIG] at hS <;> omega

/-- The offset `(-1,1)` from `K` has no relaxed bottom witness. -/
theorem K_bottom_excl (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (htc : tc = n * (-1) - d * 1) (hsc : sc = T + (d + n) * (-1) + (d - n) * 1)
    (hB : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FHr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hB
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hF <;> omega

/-- The offset `(-1,1)` from `K` has no relaxed left witness (eps = +1). -/
theorem K_left_excl (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT3 : 3 * (d + n) ≤ T) (htc : tc = n * (-1) - d * 1) (hsc : sc = T + (d + n) * (-1) + (d - n) * 1)
    (hL : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FVr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hL
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FVr, ClG, vSpG] at hF <;> omega

/-- **The strict centre next to `K` with a bottom or left witness is `(d-1, n)`** (`ε = +1`; `(d-1,n)` is black). -/
theorem K_strict_bottom_left {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (c : Site) (hc1 : |c.1 - d| ≤ 1) (hc2 : |c.2 - n| ≤ 1) (hS : StrictInterior n d c)
    (hW : (∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeHn n d v) ∨
      (∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeVn n d v)) :
    c = (d - 1, n) := by
  have hT3 := BottomTopEmpty.period_ge n d (w1T n d) hn1 hnd (w1T_eq n d)
  have hb1 := abs_le.mp hc1
  have hb2 := abs_le.mp hc2
  have hSg := (strict_iff_SIG' hn hd c).mp hS
  have e1 : w1t n d c = n * (c.1 - d) - d * (c.2 - n) := by unfold w1t; ring
  have e2 : w1s n d c = w1T n d + (d + n) * (c.1 - d) + (d - n) * (c.2 - n) := by
    unfold w1s w1T; ring
  rw [e1, e2] at hSg
  rcases K_grade_offsets n d (w1T n d) (c.1 - d) (c.2 - n) hn hd hn1 hnd hb1.1 hb1.2 hb2.1 hb2.2 hSg with
    ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  · exfalso
    have htc : w1t n d c = n * (-1) - d * 1 := by rw [e1, hi, hj]
    have hsc : w1s n d c = w1T n d + (d + n) * (-1) + (d - n) * 1 := by rw [e2, hi, hj]
    rcases hW with ⟨v, hv1, hv2, hvF⟩ | ⟨v, hv1, hv2, hvF⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      refine K_bottom_excl n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, ?_⟩
      rw [← w1t_diff n d c v, ← w1s_diff n d c v]
      exact ⟨(closedRect_iff_ClG hn hd v).mp hvF.1, hvF.2.2⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      refine K_left_excl n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hT3 htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, ?_⟩
      rw [← w1t_diff n d c v, ← w1s_diff n d c v]
      exact ⟨(closedRect_iff_ClG hn hd v).mp hvF.1, hvF.2.2⟩

/-! ## (5b): the strict centres within one pixel of `vLast` -/

/-- The strict period bound `3(d+n)+2 ≤ T` (the real period satisfies it with equality at `(n,d) = (1,3)`). -/
theorem period_ge2 {n d : ℤ} (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) : 3 * (d + n) + 2 ≤ w1T n d := by
  have he : (0 : ℤ) ≤ d - n - 2 := by omega
  rw [w1T_eq]
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ n - 1) (by omega : (0 : ℤ) ≤ n + 2), mul_nonneg he he,
    mul_nonneg he (by omega : (0 : ℤ) ≤ n)]

/-- The period bound `4(d+n)-3 ≤ T`: no right witness of `vLast + (1,0)` exists below it. -/
theorem period_ge4 {n d : ℤ} (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) : 4 * (d + n) - 3 ≤ w1T n d := by
  have he : (0 : ℤ) ≤ d - n - 2 := by omega
  rw [w1T_eq]
  nlinarith [mul_nonneg he he, mul_nonneg he (by omega : (0 : ℤ) ≤ n),
    mul_nonneg (by omega : (0 : ℤ) ≤ n - 1) (by omega : (0 : ℤ) ≤ n + 1)]

/-- The strict offsets from `vLast = (n-d+1, n+d-1)` are only `(1,0)` and `(1,-1)`. -/
theorem vL_grade_offsets (n d T i j : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTe : T % 2 = 0) (hi1 : -1 ≤ i) (hi2 : i ≤ 1) (hj1 : -1 ≤ j) (hj2 : j ≤ 1)
    (hS : SIG n d T (-T + n + d + n * i - d * j) (2 * n + (d + n) * i + (d - n) * j)) :
    (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = -1) := by
  have hi : i = -1 ∨ i = 0 ∨ i = 1 := by omega
  have hj : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp only [SIG] at hS <;> omega

/-- The offset `(1,0)` from `vLast` (grades `(-T+2n+d, 3n+d)`) has no relaxed bottom witness. -/
theorem vL0_bot (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTe : T % 2 = 0) (hT4 : 3 * (d + n) + 2 ≤ T) (htc : tc = -T + 2 * n + d) (hsc : sc = 3 * n + d)
    (hB : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FHr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hB
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hF <;> omega

/-- The offset `(1,0)` from `vLast`: no relaxed right witness (the kernel-shifted `s` is `s − T`). -/
theorem vL0_right (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTe : T % 2 = 0) (hT5 : 4 * (d + n) - 3 ≤ T) (htc : tc = -T + 2 * n + d) (hsc : sc = 3 * n + d)
    (hB : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FVr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q - T)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hB
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FVr, ClG, vSpG] at hF <;> omega

/-- The offset `(1,-1)` from `vLast` (grades `(-T+2n+2d, 4n)`) has no relaxed bottom witness. -/
theorem vL1_bot (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTe : T % 2 = 0) (hT4 : 3 * (d + n) + 2 ≤ T) (htc : tc = -T + 2 * n + 2 * d) (hsc : sc = 4 * n)
    (hB : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FHr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hB
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hF <;> omega

/-- The offset `(1,-1)` from `vLast`: no relaxed right witness. -/
theorem vL1_right (n d T tc sc : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hTe : T % 2 = 0) (hT4 : 3 * (d + n) + 2 ≤ T) (htc : tc = -T + 2 * n + 2 * d) (hsc : sc = 4 * n)
    (hB : ∃ p q : Int, -1 ≤ p ∧ p ≤ 1 ∧ -1 ≤ q ∧ q ≤ 1 ∧
      FVr n d T (tc + n * p - d * q) (sc + (d + n) * p + (d - n) * q - T)) : False := by
  subst htc
  subst hsc
  obtain ⟨p, q, hp1, hp2, hq1, hq2, hF⟩ := hB
  have hp : p = -1 ∨ p = 0 ∨ p = 1 := by omega
  have hq : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    simp only [FVr, ClG, vSpG] at hF <;> omega

/-- A right witness `v` (with `v − K` free V) gives the shifted free V grades `(w1t v, w1s v − T)`. -/
theorem freeVn_shift_FVr {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (v : Site)
    (hvF : freeVn n d (v.1 - d, v.2 - n)) :
    FVr n d (w1T n d) (w1t n d v) (w1s n d v - w1T n d) := by
  unfold freeVn at hvF
  have hgv : w1t n d (v.1 - d, v.2 - n) = w1t n d v := by unfold w1t; ring
  have hgs : w1s n d (v.1 - d, v.2 - n) = w1s n d v - w1T n d := by unfold w1s w1T; ring
  have hC := (closedRect_iff_ClG hn hd (v.1 - d, v.2 - n)).mp hvF.1
  rw [hgv, hgs] at hC
  have hV := hvF.2.2
  rw [hgs] at hV
  exact ⟨hC, hV⟩

/-- **No strict centre within one pixel of `vLast` has a bottom or aligned (right, at `ε = −1`) witness.** -/
theorem vLast_strict_excl {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (c : Site) (hc1 : |c.1 - (n - d + 1)| ≤ 1) (hc2 : |c.2 - (n + d - 1)| ≤ 1) (hS : StrictInterior n d c)
    (hW : (∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeHn n d v) ∨
      (∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ freeVn n d (v.1 - d, v.2 - n))) : False := by
  have hT4 := period_ge2 hn1 hnd
  have hTe := parity_w1T hn hd
  have hSg := (strict_iff_SIG' hn hd c).mp hS
  have e1 : w1t n d c = -w1T n d + n + d + n * (c.1 - (n - d + 1)) - d * (c.2 - (n + d - 1)) := by
    unfold w1t w1T; ring
  have e2 : w1s n d c = 2 * n + (d + n) * (c.1 - (n - d + 1)) + (d - n) * (c.2 - (n + d - 1)) := by
    unfold w1s; ring
  rw [e1, e2] at hSg
  have hb1 := abs_le.mp hc1
  have hb2 := abs_le.mp hc2
  rcases vL_grade_offsets n d (w1T n d) (c.1 - (n - d + 1)) (c.2 - (n + d - 1)) hn hd hn1 hnd hTe hb1.1 hb1.2 hb2.1 hb2.2 hSg with
    ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have htc : w1t n d c = -w1T n d + 2 * n + d := by rw [e1, hi, hj]; ring
    have hsc : w1s n d c = 3 * n + d := by rw [e2, hi, hj]; ring
    rcases hW with ⟨v, hv1, hv2, hvF⟩ | ⟨v, hv1, hv2, hvF⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      exact vL0_bot n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hTe hT4 htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, by
          rw [← w1t_diff n d c v, ← w1s_diff n d c v]
          exact ⟨(closedRect_iff_ClG hn hd v).mp hvF.1, hvF.2.2⟩⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      exact vL0_right n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hTe (period_ge4 hn1 hnd) htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, by
          rw [← w1t_diff n d c v, ← w1s_diff n d c v]
          exact freeVn_shift_FVr hn hd v hvF⟩
  · have htc : w1t n d c = -w1T n d + 2 * n + 2 * d := by rw [e1, hi, hj]; ring
    have hsc : w1s n d c = 4 * n := by rw [e2, hi, hj]; ring
    rcases hW with ⟨v, hv1, hv2, hvF⟩ | ⟨v, hv1, hv2, hvF⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      exact vL1_bot n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hTe hT4 htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, by
          rw [← w1t_diff n d c v, ← w1s_diff n d c v]
          exact ⟨(closedRect_iff_ClG hn hd v).mp hvF.1, hvF.2.2⟩⟩
    · have hb3 := abs_le.mp hv1
      have hb4 := abs_le.mp hv2
      exact vL1_right n d (w1T n d) (w1t n d c) (w1s n d c) hn hd hn1 hnd hTe hT4 htc hsc
        ⟨v.1 - c.1, v.2 - c.2, hb3.1, hb3.2, hb4.1, hb4.2, by
          rw [← w1t_diff n d c v, ← w1s_diff n d c v]
          exact freeVn_shift_FVr hn hd v hvF⟩

end FLatticePaper.Exceptions
