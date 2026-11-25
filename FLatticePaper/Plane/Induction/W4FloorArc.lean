import FLatticePaper.Plane.Induction.W4Boundary
import FLatticePaper.Plane.Induction.UnitBound
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.W1Constructor

/-! # W4 (Q35): the native V arc of the child, from the native H labels of the conjugate (the floor step)

Write `N, D` for the odd parent (`0 ≤ N < D`), `n, d` for the word's child (`2D ≤ d`, `Nd − Dn = ε = ±1`). The conjugate child is
`(n', d') = (D − N, D + N)` with `T' = 2(D² + 2DN − N²)`. A native free H label `g = (x, y)` of the conjugate (spectrum and the closed
polygon) has, with `r = (D − N)l − D y`:

* even `g` (`x + y = 2l`): `t' = 2r`, `1 ≤ r ≤ D − 1`, and the window gives `1 ≤ l ≤ D − 1`;
* odd `g` (`x + y = 2l + 1`): `t' = n' + 2r`, `0 ≤ r ≤ N`, and the window gives `0 ≤ l ≤ D − 1`.

The child's vertex `v = Z g = (−y, x − 1)` has `s(v) = 2 r_c − (d − n)` (even `g`) or `s(v) = 2 r_c` (odd `g`), with
`r_c = (d − n) l − d y` and the identity `D r_c = d r + ε l`. These give the initial left V arc, except the exceptional label
`g = hLast` (`ε = 1`, `r = N`). -/

namespace FLatticePaper.W4FloorArc

/-- The even native labels: `x + y = 2l` and the window of `s'` give `1 ≤ l ≤ D − 1`. -/
theorem even_label_range {N D x y l : ℤ} (hN0 : 0 ≤ N) (hND : N < D) (hl : x + y = 2 * l)
    (ht1 : 2 ≤ (D - N) * x - (D + N) * y) (ht2 : (D - N) * x - (D + N) * y ≤ 2 * D - 2)
    (hs1 : 0 ≤ 2 * D * x + 2 * N * y)
    (hs2 : 2 * D * x + 2 * N * y ≤ 2 * (D * D + 2 * D * N - N * N) + 2 * (D - N)) :
    1 ≤ l ∧ l ≤ D - 1 := by
  have hx : x = 2 * l - y := by linarith
  subst hx
  have hD : 0 < D := by omega
  have htr : (D - N) * (2 * l - y) - (D + N) * y = 2 * ((D - N) * l - D * y) := by ring
  have hDs : D * (2 * D * (2 * l - y) + 2 * N * y) =
      2 * (D * D + 2 * D * N - N * N) * l + 2 * (D - N) * ((D - N) * l - D * y) := by ring
  have hr1 : 1 ≤ (D - N) * l - D * y := by linarith
  have hr2 : (D - N) * l - D * y ≤ D - 1 := by linarith
  have hTp : (D - N) * (D - 1) < D * D + 2 * D * N - N * N := by nlinarith
  have hD0 : 0 ≤ D * (2 * D * (2 * l - y) + 2 * N * y) := mul_nonneg hD.le hs1
  have hDu : D * (2 * D * (2 * l - y) + 2 * N * y) ≤
      D * (2 * (D * D + 2 * D * N - N * N) + 2 * (D - N)) := mul_le_mul_of_nonneg_left hs2 hD.le
  have hTpnn : 0 ≤ D * D + 2 * D * N - N * N := by nlinarith
  constructor
  · by_contra hlt
    rcases lt_or_eq_of_le (show l ≤ 0 by omega) with hl0 | hl0
    · -- `l ≤ −1`: `D s' < 0`
      have h1 : 2 * (D * D + 2 * D * N - N * N) * l ≤ -2 * (D * D + 2 * D * N - N * N) := by
        nlinarith
      have h2 : 2 * (D - N) * ((D - N) * l - D * y) ≤ 2 * (D - N) * (D - 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    · -- `l = 0`: `r = −D y ∈ [1, D − 1]` is impossible
      subst hl0
      rcases le_or_gt y (-1) with hy | hy
      · nlinarith
      · nlinarith
  · by_contra hlt
    rcases eq_or_lt_of_le (show D ≤ l by omega) with heq | hgt
    · -- `l = D`: `r = D (D − N − y)` is a multiple of D, in [1, D − 1]: impossible
      subst heq
      rcases le_or_gt (D - N - y) 0 with hk | hk
      · nlinarith
      · nlinarith
    · -- `l ≥ D + 1`: `D s' > D (upper)`
      have h1 : 2 * (D * D + 2 * D * N - N * N) * (D + 1) ≤
          2 * (D * D + 2 * D * N - N * N) * l := by
        apply mul_le_mul_of_nonneg_left (by omega) (by linarith)
      have h2 : 2 * (D - N) * 1 ≤ 2 * (D - N) * ((D - N) * l - D * y) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith

/-- The odd native labels: `x + y = 2l + 1` and the window give `0 ≤ l ≤ D − 1`. -/
theorem odd_label_range {N D x y l : ℤ} (hN0 : 0 ≤ N) (hND : N < D) (hl : x + y = 2 * l + 1)
    (ht1 : D - N ≤ (D - N) * x - (D + N) * y) (ht2 : (D - N) * x - (D + N) * y ≤ D + N)
    (hs1 : 2 - 2 * N ≤ 2 * D * x + 2 * N * y)
    (hs2 : 2 * D * x + 2 * N * y ≤ 2 * (D * D + 2 * D * N - N * N) + 2 * D - 2) :
    0 ≤ l ∧ l ≤ D - 1 := by
  have hx : x = 2 * l + 1 - y := by linarith
  subst hx
  have hD : 0 < D := by omega
  have htr : (D - N) * (2 * l + 1 - y) - (D + N) * y = (D - N) + 2 * ((D - N) * l - D * y) := by ring
  have hr0 : 0 ≤ (D - N) * l - D * y := by linarith
  have hrN : (D - N) * l - D * y ≤ N := by linarith
  have hDs : D * (2 * D * (2 * l + 1 - y) + 2 * N * y) =
      2 * (D * D + 2 * D * N - N * N) * l + 2 * (D - N) * ((D - N) * l - D * y) + 2 * D * D := by ring
  have hD0 : D * (2 - 2 * N) ≤ D * (2 * D * (2 * l + 1 - y) + 2 * N * y) :=
    mul_le_mul_of_nonneg_left hs1 hD.le
  have hDu : D * (2 * D * (2 * l + 1 - y) + 2 * N * y) ≤
      D * (2 * (D * D + 2 * D * N - N * N) + 2 * D - 2) := mul_le_mul_of_nonneg_left hs2 hD.le
  have hTpnn : 0 ≤ D * D + 2 * D * N - N * N := by nlinarith
  constructor
  · by_contra hlt
    -- `l ≤ −1`: `D s' ≤ −2DN < D (2 − 2N)`
    have h1 : 2 * (D * D + 2 * D * N - N * N) * l ≤ -2 * (D * D + 2 * D * N - N * N) := by
      nlinarith
    have h2 : 2 * (D - N) * ((D - N) * l - D * y) ≤ 2 * (D - N) * N := by
      apply mul_le_mul_of_nonneg_left hrN (by linarith)
    nlinarith
  · by_contra hlt
    -- `l ≥ D`: `D s' ≥ D (2T_p + 2D) > D (upper)`
    have h1 : 2 * (D * D + 2 * D * N - N * N) * D ≤ 2 * (D * D + 2 * D * N - N * N) * l := by
      apply mul_le_mul_of_nonneg_left (by omega) (by linarith)
    have h2 : 0 ≤ 2 * (D - N) * ((D - N) * l - D * y) := by
      apply mul_nonneg (by linarith) hr0
    nlinarith

/-- The child's arc, even native labels: `s(v) = 2 r_c − (d − n)` with `1 ≤ r_c ≤ d − 1`, so `s(v)` is in the initial odd range. -/
theorem child_even_arc {N D n d ε x y l : ℤ} (hN0 : 0 ≤ N) (hND : N < D) (_hD : 0 < D) (hd : 2 * D ≤ d)
    (hε : N * d - D * n = ε) (hεu : ε = 1 ∨ ε = -1) (hl : x + y = 2 * l) (hl1 : 1 ≤ l) (hl2 : l ≤ D - 1)
    (hr1 : 1 ≤ (D - N) * l - D * y) (hr2 : (D - N) * l - D * y ≤ D - 1) :
    2 - d + n ≤ (d + n) * (-y) + (d - n) * (x - 1) ∧
      (d + n) * (-y) + (d - n) * (x - 1) ≤ d + n - 2 := by
  have hx : x = 2 * l - y := by linarith
  subst hx
  set r := (D - N) * l - D * y with hr
  set rc := (d - n) * l - d * y with hrc_def
  have hrc : D * rc = d * r + ε * l := by
    rw [hrc_def, hr]
    linear_combination l * hε
  have hs : (d + n) * (-y) + (d - n) * (2 * l - y - 1) = 2 * rc - (d - n) := by
    rw [hrc_def]; ring
  rw [hs]
  have hrc1 : 1 ≤ rc := by
    rcases hεu with rfl | rfl
    · have hp : 0 < D * rc := by rw [hrc]; nlinarith
      nlinarith
    · have hp : 0 < D * rc := by rw [hrc]; nlinarith
      nlinarith
  have hrc2 : rc ≤ d - 1 := by
    rcases hεu with rfl | rfl
    · have hp : D * rc ≤ D * (d - 1) := by rw [hrc]; nlinarith
      nlinarith
    · have hp : D * rc ≤ D * (d - 1) := by rw [hrc]; nlinarith
      nlinarith
  constructor <;> linarith

/-- The child's arc, odd native labels: `s(v) = 2 r_c` with `0 ≤ r_c ≤ n` unless `ε = 1` and `r = N`. -/
theorem child_odd_arc {N D n d ε x y l : ℤ} (hN0 : 0 ≤ N) (hND : N < D) (hD : 0 < D) (hd : 2 * D ≤ d)
    (hε : N * d - D * n = ε) (hεu : ε = 1 ∨ ε = -1) (hl : x + y = 2 * l + 1) (hl1 : 0 ≤ l) (hl2 : l ≤ D - 1)
    (hr1 : 0 ≤ (D - N) * l - D * y) (hr2 : (D - N) * l - D * y ≤ N)
    (hexc : ¬ (ε = 1 ∧ (D - N) * l - D * y = N)) :
    0 ≤ (d + n) * (-y) + (d - n) * (x - 1) ∧ (d + n) * (-y) + (d - n) * (x - 1) ≤ 2 * n := by
  have hx : x = 2 * l + 1 - y := by linarith
  subst hx
  set r := (D - N) * l - D * y with hr
  set rc := (d - n) * l - d * y with hrc_def
  have hrc : D * rc = d * r + ε * l := by
    rw [hrc_def, hr]
    linear_combination l * hε
  have hs : (d + n) * (-y) + (d - n) * (2 * l + 1 - y - 1) = 2 * rc := by
    rw [hrc_def]; ring
  rw [hs]
  have hrc0 : 0 ≤ rc := by
    by_contra hneg
    have hneg' : rc ≤ -1 := by omega
    have hp : D * rc ≤ -D := by nlinarith
    rcases hεu with rfl | rfl
    · nlinarith
    · nlinarith
  have hrcn : rc ≤ n := by
    have hDn : D * n = N * d - ε := by linarith
    have hp : D * rc ≤ D * n := by
      rw [hrc, hDn]
      rcases hεu with rfl | rfl
      · have hne : r ≤ N - 1 := by
          have : r ≠ N := fun h => hexc ⟨rfl, h⟩
          omega
        nlinarith
      · nlinarith
    exact le_of_mul_le_mul_left hp hD
  constructor <;> linarith

/-- The exceptional odd label: `ε = 1`, `r = N` forces `l = D − 1`, `y = D − N − 1` (the label `hLast`). -/
theorem odd_exception {N D n d y l : ℤ} (hε : N * d - D * n = 1) (hD : 0 < D) (hl1 : 0 ≤ l) (hl2 : l ≤ D - 1)
    (hr : (D - N) * l - D * y = N) : l = D - 1 ∧ y = D - N - 1 := by
  have hk : l + 1 = D * (d * (l - y) - n * (l + 1)) := by
    linear_combination (-(l + 1)) * hε + (-d) * hr
  have hk1 : 0 < d * (l - y) - n * (l + 1) := by
    by_contra hneg
    have : d * (l - y) - n * (l + 1) ≤ 0 := by omega
    nlinarith
  have hk2 : d * (l - y) - n * (l + 1) ≤ 1 := by
    by_contra hbig
    have : 2 ≤ d * (l - y) - n * (l + 1) := by omega
    nlinarith
  have hk3 : d * (l - y) - n * (l + 1) = 1 := by omega
  have hl : l = D - 1 := by
    rw [hk3] at hk
    linarith
  refine ⟨hl, ?_⟩
  subst hl
  have hy : D * (y - (D - N - 1)) = 0 := by linear_combination (-1 : ℤ) * hr
  rcases mul_eq_zero.mp hy with h0 | h0
  · omega
  · linarith

/-- **The shift `k` of the old root is `0` or `1` (even `v`).** With `s(x) = sv + 2kC` and `s(x + U_q) = s(x) + (T − 2C)`, both points in
the even polygon `[0, T + 2n]`, and `C ≥ d + n`, `0 ≤ sv ≤ 2n`. -/
theorem k_even_bounds {n d C T k sv : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hC : d + n ≤ C) (hsv0 : 0 ≤ sv) (hsv1 : sv ≤ 2 * n)
    (hx0 : 0 ≤ sv + 2 * k * C) (hu1 : sv + 2 * k * C + (T - 2 * C) ≤ T + 2 * n) :
    0 ≤ k ∧ k ≤ 1 := by
  have hC0 : (0 : ℤ) ≤ C := by linarith
  constructor
  · by_contra hneg
    have hk : k ≤ -1 := by omega
    have h1 : k * C ≤ -C := by nlinarith
    linarith
  · by_contra hbig
    have hk : 2 ≤ k := by omega
    have h1 : 2 * C ≤ k * C := by nlinarith
    linarith

/-- **The shift `k` of the old root is `0` or `1` (odd `v`).** With the odd polygon `[2 − d + n, T + d + n − 2]` for both points. -/
theorem k_odd_bounds {n d C T k sv : ℤ} (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hC : d + n ≤ C)
    (hsv0 : 2 - d + n ≤ sv) (hsv1 : sv ≤ d + n - 2)
    (hx0 : 2 - d + n ≤ sv + 2 * k * C)
    (hu1 : sv + 2 * k * C + (T - 2 * C) ≤ T + d + n - 2) :
    0 ≤ k ∧ k ≤ 1 := by
  constructor
  · by_contra hneg
    have hk : k ≤ -1 := by omega
    nlinarith
  · by_contra hbig
    have hk : 2 ≤ k := by omega
    nlinarith

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- **The native V arc of the child (Q35, the floor step).** For a native free H label `g` of the conjugate with `g ≠ hLast`, the
child's V-path vertex `v = Z g = (−g₂, g₁ − 1)` lies on the initial left V arc: `w1c ≤ s(v) ≤ w1h`. -/
theorem native_V_arc {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {g : Site}
    (hg : g ∈ (frameAt (conjWord word)).freeH)
    (hne : g ≠ (frameAt (conjWord word)).hLast ∨ (frameAt word).eps = -1) :
    w1c (frameAt word).child.num (frameAt word).child.den (-g.2, g.1 - 1) ≤
        w1s (frameAt word).child.num (frameAt word).child.den (-g.2, g.1 - 1) ∧
      w1s (frameAt word).child.num (frameAt word).child.den (-g.2, g.1 - 1) ≤
        w1h (frameAt word).child.num (frameAt word).child.den (-g.2, g.1 - 1) := by
  obtain ⟨hC1, hC2⟩ := FLatticePaper.UnitBound.conj_child_sums h
  obtain ⟨hD0, hN0, hNleD, hpar⟩ := FLatticePaper.NativeGrade.odd_parent_facts (frameAt word)
  have hND : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den := by omega
  have hcd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hq : 0 < (frameAt word).parents.even.den := by
    have hb := (frameAt word).valid.even_bounds
    unfold Fraction.InUnitInterval at hb
    omega
  have hd2 : 2 * (frameAt word).parents.odd.den ≤ (frameAt word).child.den := by omega
  have hε : (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).parents.odd.den * (frameAt word).child.num = (frameAt word).eps :=
    ((frameAt word).eps_eq).symm
  have hεu := (frameAt word).eps_unit
  have hn := (frameAt word).child_facts
  have hcl : closedRect (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den g := by
    have h0 := hg.1
    rw [closedPolygon_eq_closedRect (frameAt (conjWord word))] at h0
    exact h0
  have hsp := hg.2.2
  unfold closedRect at hcl
  unfold ChildFrame.hSpectrum ChildFrame.tGrade at hsp
  rw [hC1, hC2] at hcl hsp
  unfold w1t w1s w1T at hcl
  set D := (frameAt word).parents.odd.den with hDdef
  set N := (frameAt word).parents.odd.num with hNdef
  set n := (frameAt word).child.num with hndef
  set d := (frameAt word).child.den with hddef
  unfold w1c w1h w1s
  by_cases hpg : (g.1 + g.2) % 2 = 0
  · -- even `g`: `t' = 2r`, the child vertex `v` is odd
    obtain ⟨l, hl⟩ : ∃ l, g.1 + g.2 = 2 * l := ⟨(g.1 + g.2) / 2, by omega⟩
    have hodd : ¬ EvenSite (-g.2, g.1 - 1) := by
      unfold EvenSite
      simp only
      omega
    rw [if_pos (show EvenSite g from hpg)] at hcl
    simp only [if_neg hodd]
    have ht_e : (D - N) * g.1 - (D + N) * g.2 = 2 * ((D - N) * l - D * g.2) := by
      have hx : g.1 = 2 * l - g.2 := by omega
      rw [hx]
      ring
    rcases hsp with hsp | hsp
    swap
    · exfalso
      omega
    obtain ⟨hl1, hl2⟩ := even_label_range hN0 hND hl (by linarith [hsp.2.1]) (by linarith [hsp.2.2])
      (by linarith [hcl.2.2.1]) (by linarith [hcl.2.2.2])
    have hr1 : 1 ≤ (D - N) * l - D * g.2 := by linarith [hsp.2.1]
    have hr2 : (D - N) * l - D * g.2 ≤ D - 1 := by linarith [hsp.2.2]
    obtain ⟨hc1, hc2⟩ := child_even_arc hN0 hND hD0 hd2 hε hεu hl hl1 hl2 hr1 hr2
    exact ⟨hc1, hc2⟩
  · -- odd `g`: `t' = (D − N) + 2r`, the child vertex `v` is even
    obtain ⟨l, hl⟩ : ∃ l, g.1 + g.2 = 2 * l + 1 := ⟨(g.1 + g.2 - 1) / 2, by omega⟩
    have hev : EvenSite (-g.2, g.1 - 1) := by
      unfold EvenSite
      simp only
      omega
    have hgodd : ¬ EvenSite g := fun h' => hpg (show (g.1 + g.2) % 2 = 0 from h')
    rw [if_neg hgodd] at hcl
    simp only [if_pos hev]
    have ht_o : (D - N) * g.1 - (D + N) * g.2 = (D - N) + 2 * ((D - N) * l - D * g.2) := by
      have hx : g.1 = 2 * l + 1 - g.2 := by omega
      rw [hx]
      ring
    rcases hsp with hsp | hsp
    · exfalso
      omega
    obtain ⟨hl1, hl2⟩ := odd_label_range hN0 hND hl (by linarith [hsp.2.1]) (by linarith [hsp.2.2])
      (by linarith [hcl.2.1]) (by linarith [hcl.2.2.2])
    have hr0 : 0 ≤ (D - N) * l - D * g.2 := by linarith [hsp.2.1]
    have hrN : (D - N) * l - D * g.2 ≤ N := by linarith [hsp.2.2]
    by_cases hexc : (frameAt word).eps = 1 ∧ (D - N) * l - D * g.2 = N
    · exfalso
      obtain ⟨hl_eq, hy_eq⟩ := odd_exception (hε.trans hexc.1) hD0 hl1 hl2 hexc.2
      rcases hne with hne | hne
      · apply hne
        unfold ChildFrame.hLast
        rw [hC1, hC2]
        refine Prod.ext ?_ ?_
        · simp only
          omega
        · simp only
          omega
      · rw [hexc.1] at hne
        norm_num at hne
    · exact child_odd_arc hN0 hND hD0 hd2 hε hεu hl hl1 hl2 hr0 hrN hexc

end FLatticePaper.W4FloorArc
