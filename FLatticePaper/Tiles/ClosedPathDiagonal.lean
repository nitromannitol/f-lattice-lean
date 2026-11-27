import FLatticePaper.Tiles.ClosedPathExcluded

/-! # Condition (C): the diagonal bounds of a standard tile, and the excluded pairs in the even-first orientation

For a standard tile of the fraction `n/d` (`0 < n < d`, period multiplier `μ`), every site satisfies

`0 ≤ x + y ≤ μ (n + d) + 2n` and `1 - 2d ≤ x - y ≤ μ (d - n) + 1`

(`diag_odd`, `diag_even`). The proof reads the four inequalities of the hull `H` (`SubOddCopy.mem_oddTile_iff`), in the
coordinates `t = n x - d y`, `s = (d + n) x + (d - n) y`, through the identities `T (x + y) = -2n t + (n + d) s` and
`T (x - y) = 2d t + (d - n) s`, `T = d² + 2dn - n²`. The bounds of `H` depend on the parity of the site, and so do `x ± y`;
the error of the bound is less than `T` or, at the sites where the parities agree, less than `2T` or `3T`, which the parity
absorbs.

These bounds separate the two excluded mixed pairs of each standard child in the even-first orientation (`W_1` even), the
diagonal `x + y` for the odd child and `x - y` for the even child, with no relation between the two parents beyond
`0 < n < d`. Together with `ClosedPathExcluded` this proves `ExclOdd` and `ExclEven` (`exclOdd_all`, `exclEven_all`). -/

namespace FLatticePaper.Tiles.ClosedPathDiagonal

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathStandard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.ClosedPathExcluded
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-! ### The arithmetic core -/

theorem lt_of_T {T k E c : ℤ} (hT : 0 < T) (h : T * k ≤ E) (hE : E < c * T) : k < c := by
  by_contra hc
  rw [not_lt] at hc
  have : c * T ≤ k * T := mul_le_mul_of_nonneg_right hc hT.le
  nlinarith

theorem gt_of_T {T k E c : ℤ} (hT : 0 < T) (h : E ≤ T * k) (hE : c * T < E) : c < k := by
  by_contra hc
  rw [not_lt] at hc
  have : k * T ≤ c * T := mul_le_mul_of_nonneg_right hc hT.le
  nlinarith

/-- The four inequalities of `H` at a site, in the variables `t`, `s`, `T`, with the parity-dependent bounds `a`, `l`. -/
structure HBounds (n d μ T t s a l : ℤ) : Prop where
  t1 : a - T ≤ t
  t2 : t ≤ d + n - a
  s1 : l ≤ s
  s2 : s ≤ μ * T + 2 * n - l

/-- The polynomial facts used by the diagonal bounds. -/
theorem poly_facts (n d : ℤ) (hn : 0 < n) (hnd : n < d) :
    0 < d ^ 2 + 2 * d * n - n ^ 2 ∧ n * n < d * d ∧ 0 < n * d ∧ 0 < (d - n) * n ∧ 0 < (d - n) * d := by
  have hd : 0 < d := by linarith
  have hdn : 0 < d - n := by linarith
  refine ⟨by nlinarith [mul_pos hn hd, mul_pos hdn hn], by nlinarith, mul_pos hn hd, mul_pos hdn hn,
    mul_pos hdn hd⟩

/-- `x + y ≥ 0` at a site of `H`. -/
theorem diag_sum_lower (n d T t s x y a l : ℤ) (hn : 0 < n) (hnd : n < d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (e1 : T * (x + y) = -2 * n * t + (n + d) * s) (μ : ℤ) (hb : HBounds n d μ T t s a l)
    (hcase : ((x + y) % 2 = 1 ∧ a = n ∧ (l = d - n ∨ l = 3 * n - d)) ∨
      ((x + y) % 2 = 0 ∧ (a = 2 * n ∨ a = d - n) ∧ l = 0)) :
    0 ≤ x + y := by
  obtain ⟨hT0', hnn, hnd0, hdnn, hdnd⟩ := poly_facts n d hn hnd
  have hT0 : 0 < T := by rw [hT]; exact hT0'
  have p1 : 2 * n * t ≤ 2 * n * (d + n - a) := mul_le_mul_of_nonneg_left hb.t2 (by linarith)
  have p2 : (n + d) * l ≤ (n + d) * s := mul_le_mul_of_nonneg_left hb.s1 (by linarith)
  have hE : -2 * n * (d + n - a) + (n + d) * l ≤ T * (x + y) := by linarith
  rcases hcase with ⟨hpar, ha, hl⟩ | ⟨hpar, ha, rfl⟩
  · subst a
    have hc : (-1) * T < -2 * n * (d + n - n) + (n + d) * l := by
      rw [hT]
      rcases hl with rfl | rfl <;> nlinarith
    have := gt_of_T hT0 hE hc
    omega
  · have hc : (-2) * T < -2 * n * (d + n - a) + (n + d) * 0 := by
      rw [hT]
      rcases ha with rfl | rfl <;> nlinarith
    have := gt_of_T hT0 hE hc
    omega

/-- `x + y ≤ μ (n + d) + 2n` at a site of `H`. -/
theorem diag_sum_upper (n d T t s x y a l : ℤ) (hn : 0 < n) (hnd : n < d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (e1 : T * (x + y) = -2 * n * t + (n + d) * s) (μ : ℤ) (hMpar : (μ * (n + d) + 2 * n) % 2 = 0)
    (hb : HBounds n d μ T t s a l)
    (hcase : ((x + y) % 2 = 1 ∧ a = n ∧ (l = d - n ∨ l = 3 * n - d)) ∨
      ((x + y) % 2 = 0 ∧ (a = 2 * n ∨ a = d - n) ∧ l = 0)) :
    x + y ≤ μ * (n + d) + 2 * n := by
  obtain ⟨hT0', hnn, hnd0, hdnn, hdnd⟩ := poly_facts n d hn hnd
  have hT0 : 0 < T := by rw [hT]; exact hT0'
  have p1 : 2 * n * (a - T) ≤ 2 * n * t := mul_le_mul_of_nonneg_left hb.t1 (by linarith)
  have p2 : (n + d) * s ≤ (n + d) * (μ * T + 2 * n - l) := mul_le_mul_of_nonneg_left hb.s2 (by linarith)
  have hE : T * (x + y - (μ * (n + d) + 2 * n)) ≤ -2 * n * a + (n + d) * (2 * n - l) := by
    have : T * (x + y - (μ * (n + d) + 2 * n)) = T * (x + y) - T * (μ * (n + d) + 2 * n) := by ring
    rw [this]
    nlinarith
  generalize hM : μ * (n + d) + 2 * n = M at hE hMpar ⊢
  rcases hcase with ⟨hpar, ha, hl⟩ | ⟨hpar, ha, rfl⟩
  · subst a
    have hc : -2 * n * n + (n + d) * (2 * n - l) < 1 * T := by
      rw [hT]
      rcases hl with rfl | rfl <;> nlinarith
    have := lt_of_T hT0 hE hc
    omega
  · have hc : -2 * n * a + (n + d) * (2 * n - 0) < 2 * T := by
      rw [hT]
      rcases ha with rfl | rfl <;> nlinarith
    have := lt_of_T hT0 hE hc
    omega

/-- `x - y ≥ 1 - 2d` at a site of `H`. -/
theorem diag_diff_lower (n d T t s x y a l : ℤ) (hn : 0 < n) (hnd : n < d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (e2 : T * (x - y) = 2 * d * t + (d - n) * s) (μ : ℤ) (hb : HBounds n d μ T t s a l)
    (hcase : ((x + y) % 2 = 1 ∧ a = n ∧ (l = d - n ∨ l = 3 * n - d)) ∨
      ((x + y) % 2 = 0 ∧ (a = 2 * n ∨ a = d - n) ∧ l = 0)) :
    1 - 2 * d ≤ x - y := by
  obtain ⟨hT0', hnn, hnd0, hdnn, hdnd⟩ := poly_facts n d hn hnd
  have hT0 : 0 < T := by rw [hT]; exact hT0'
  have p1 : 2 * d * (a - T) ≤ 2 * d * t := mul_le_mul_of_nonneg_left hb.t1 (by linarith)
  have p2 : (d - n) * l ≤ (d - n) * s := mul_le_mul_of_nonneg_left hb.s1 (by linarith)
  have hE : 2 * d * a + (d - n) * l ≤ T * (x - y + 2 * d) := by
    have : T * (x - y + 2 * d) = T * (x - y) + 2 * d * T := by ring
    rw [this]
    nlinarith
  rcases hcase with ⟨hpar, ha, hl⟩ | ⟨hpar, ha, rfl⟩
  · subst a
    have hc : (-1) * T < 2 * d * n + (d - n) * l := by
      rw [hT]
      rcases hl with rfl | rfl <;> nlinarith
    have := gt_of_T hT0 hE hc
    omega
  · have hc : 0 * T < 2 * d * a + (d - n) * 0 := by
      rcases ha with rfl | rfl <;> nlinarith
    have := gt_of_T hT0 hE hc
    omega

/-- `x - y ≤ μ (d - n) + 1` at a site of `H`. -/
theorem diag_diff_upper (n d T t s x y a l : ℤ) (hn : 0 < n) (hnd : n < d) (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (e2 : T * (x - y) = 2 * d * t + (d - n) * s) (μ : ℤ) (hNpar : (μ * (d - n)) % 2 = 0)
    (hb : HBounds n d μ T t s a l)
    (hcase : ((x + y) % 2 = 1 ∧ a = n ∧ (l = d - n ∨ l = 3 * n - d)) ∨
      ((x + y) % 2 = 0 ∧ (a = 2 * n ∨ a = d - n) ∧ l = 0)) :
    x - y ≤ μ * (d - n) + 1 := by
  obtain ⟨hT0', hnn, hnd0, hdnn, hdnd⟩ := poly_facts n d hn hnd
  have hT0 : 0 < T := by rw [hT]; exact hT0'
  have p1 : 2 * d * t ≤ 2 * d * (d + n - a) := mul_le_mul_of_nonneg_left hb.t2 (by linarith)
  have p2 : (d - n) * s ≤ (d - n) * (μ * T + 2 * n - l) := mul_le_mul_of_nonneg_left hb.s2 (by linarith)
  have hE : T * (x - y - μ * (d - n)) ≤ 2 * d * (d + n - a) + (d - n) * (2 * n - l) := by
    have : T * (x - y - μ * (d - n)) = T * (x - y) - μ * (d - n) * T := by ring
    rw [this]
    nlinarith
  generalize hN : μ * (d - n) = N at hE hNpar ⊢
  rcases hcase with ⟨hpar, ha, hl⟩ | ⟨hpar, ha, rfl⟩
  · subst a
    have hc : 2 * d * (d + n - n) + (d - n) * (2 * n - l) < 3 * T := by
      rw [hT]
      rcases hl with rfl | rfl <;> nlinarith
    have := lt_of_T hT0 hE hc
    omega
  · have hc : 2 * d * (d + n - a) + (d - n) * (2 * n - 0) < 2 * T := by
      rw [hT]
      rcases ha with rfl | rfl <;> nlinarith
    have := lt_of_T hT0 hE hc
    omega

/-! ### The diagonal bounds of the standard tiles -/

/-- **The diagonal bounds of `H`**, for a fraction `0 < n < d`. -/
theorem diag_of_inH (f : Fraction) (hpos : 0 < f.num) (hlt : f.num < f.den) (z : ℤ × ℤ) (hz : InH f z) :
    0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ SiteInduction.muOf f * (f.num + f.den) + 2 * f.num ∧
      1 - 2 * f.den ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ SiteInduction.muOf f * (f.den - f.num) + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have e1 : tOf f * (z.1 + z.2) = -2 * f.num * tCo f z + (f.num + f.den) * sCo f z := by
    unfold tOf tCo sCo; ring
  have e2 : tOf f * (z.1 - z.2) = 2 * f.den * tCo f z + (f.den - f.num) * sCo f z := by
    unfold tOf tCo sCo; ring
  have hT : tOf f = f.den ^ 2 + 2 * f.den * f.num - f.num ^ 2 := rfl
  have hMpar : (SiteInduction.muOf f * (f.num + f.den) + 2 * f.num) % 2 = 0 := by
    unfold SiteInduction.muOf
    split_ifs with h <;> omega
  have hNpar : (SiteInduction.muOf f * (f.den - f.num)) % 2 = 0 := by
    unfold SiteInduction.muOf
    split_ifs with h <;> omega
  have hcase : ((z.1 + z.2) % 2 = 1 ∧ aOf f (decide ((z.1 + z.2) % 2 = 0)) = f.num ∧
        (lOf f (decide ((z.1 + z.2) % 2 = 0)) = f.den - f.num ∨
          lOf f (decide ((z.1 + z.2) % 2 = 0)) = 3 * f.num - f.den)) ∨
      ((z.1 + z.2) % 2 = 0 ∧ (aOf f (decide ((z.1 + z.2) % 2 = 0)) = 2 * f.num ∨
          aOf f (decide ((z.1 + z.2) % 2 = 0)) = f.den - f.num) ∧ lOf f (decide ((z.1 + z.2) % 2 = 0)) = 0) := by
    by_cases hp : (z.1 + z.2) % 2 = 0
    · right
      refine ⟨hp, ?_, ?_⟩
      · simpa [aOf, hp] using min_choice (2 * f.num) (f.den - f.num)
      · simp [lOf, hp]
    · left
      have hp' : (z.1 + z.2) % 2 = 1 := by omega
      refine ⟨hp', ?_, ?_⟩
      · simp [aOf, hp]
      · simpa [lOf, hp] using min_choice (f.den - f.num) (3 * f.num - f.den)
  have hb : HBounds f.num f.den (SiteInduction.muOf f) (tOf f) (tCo f z) (sCo f z)
      (aOf f (decide ((z.1 + z.2) % 2 = 0))) (lOf f (decide ((z.1 + z.2) % 2 = 0))) := ⟨h1, h2, h3, h4⟩
  exact ⟨diag_sum_lower _ _ _ _ _ _ _ _ _ hpos hlt hT e1 _ hb hcase,
    diag_sum_upper _ _ _ _ _ _ _ _ _ hpos hlt hT e1 _ hMpar hb hcase,
    diag_diff_lower _ _ _ _ _ _ _ _ _ hpos hlt hT e2 _ hb hcase,
    diag_diff_upper _ _ _ _ _ _ _ _ _ hpos hlt hT e2 _ hNpar hb hcase⟩

/-- **The diagonal bounds of the odd standard tile**: `0 ≤ x + y ≤ 4n + 2d` and `1 - 2d ≤ x - y ≤ 2(d - n) + 1`. -/
theorem diag_odd (u : Word) (z : ℤ × ℤ) (hz : z ∈ oddTile u) :
    0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * ((fracOdd u).num + (fracOdd u).den) + 2 * (fracOdd u).num ∧
      1 - 2 * (fracOdd u).den ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 2 * ((fracOdd u).den - (fracOdd u).num) + 1 := by
  have hpl := SiteHullOdd.curO_pos_lt u
  have h := diag_of_inH (SiteInduction.curO u) hpl.1 hpl.2 z ((SubOddCopy.mem_oddTile_iff u z).1 hz)
  have hmu : SiteInduction.muOf (SiteInduction.curO u) = 2 := by
    have h' : ((SiteInduction.curO u).num + (SiteInduction.curO u).den) % 2 = 1 := SiteHullOdd.curO_odd u
    simp [SiteInduction.muOf, h']
  rw [hmu] at h
  exact h

/-- **The diagonal bounds of the even standard tile**: `0 ≤ x + y ≤ 3n + d` and `1 - 2d ≤ x - y ≤ d - n + 1`. -/
theorem diag_even (u : Word) (z : ℤ × ℤ) (hz : z ∈ evenTile u) :
    0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 1 * ((fracEven u).num + (fracEven u).den) + 2 * (fracEven u).num ∧
      1 - 2 * (fracEven u).den ≤ z.1 - z.2 ∧ z.1 - z.2 ≤ 1 * ((fracEven u).den - (fracEven u).num) + 1 := by
  have hpl := SiteHullEven.curE_pos_lt u
  have h := diag_of_inH (SiteInduction.curE u) hpl.1 hpl.2 z ((SubEvenCopy.mem_evenTile_iff u z).1 hz)
  have hmu : SiteInduction.muOf (SiteInduction.curE u) = 1 := by
    have h' := SiteHullEven.curE_num_add_den_even u
    simp [SiteInduction.muOf, h']
  rw [hmu] at h
  exact h

theorem diag_shift_odd (u : Word) (v z : ℤ × ℤ) (hz : z ∈ shiftS (tOddSet u) v) :
    0 ≤ (z.1 - v.1) + (z.2 - v.2) ∧
      (z.1 - v.1) + (z.2 - v.2) ≤ 2 * ((fracOdd u).num + (fracOdd u).den) + 2 * (fracOdd u).num ∧
      1 - 2 * (fracOdd u).den ≤ (z.1 - v.1) - (z.2 - v.2) ∧
      (z.1 - v.1) - (z.2 - v.2) ≤ 2 * ((fracOdd u).den - (fracOdd u).num) + 1 := by
  have h := diag_odd u (z - v) (Finset.mem_coe.1 (sub_mem_of_shift _ _ _ hz))
  simpa using h

theorem diag_shift_even (u : Word) (v z : ℤ × ℤ) (hz : z ∈ shiftS (tEvenSet u) v) :
    0 ≤ (z.1 - v.1) + (z.2 - v.2) ∧
      (z.1 - v.1) + (z.2 - v.2) ≤ 1 * ((fracEven u).num + (fracEven u).den) + 2 * (fracEven u).num ∧
      1 - 2 * (fracEven u).den ≤ (z.1 - v.1) - (z.2 - v.2) ∧
      (z.1 - v.1) - (z.2 - v.2) ≤ 1 * ((fracEven u).den - (fracEven u).num) + 1 := by
  have h := diag_even u (z - v) (Finset.mem_coe.1 (sub_mem_of_shift _ _ _ hz))
  simpa using h

/-! ### The excluded pairs in the even-first orientation -/

/-- **The excluded pairs of the odd child, `W_1` even**, separated by `x + y`: `Q^{+,1}` (at `0`) lies below `P^+` (at `2U`),
and `P^-` (at `V`) below `Q^{-,2}` (at `A + B + U`). -/
theorem exclOdd_evenFirst (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    (∀ z, z ∈ dOdd w u1 u2 0 → z ∈ dOdd w u1 u2 2 → False) ∧ (∀ z, z ∈ dOdd w u1 u2 1 → z ∈ dOdd w u1 u2 5 → False) := by
  have hP := oddP_ef w hph
  have hQ := oddQ_ef w hph
  have hql := SiteHullEven.curE_pos_lt u2
  have hcu : SiteInduction.curE u2 = fracEven u2 := rfl
  rw [hcu, ← hq] at hql
  constructor
  · intro z h0 h2
    simp only [dOdd, pieceSet, hP, hQ] at h0 h2
    simp at h0 h2
    have b0 := diag_shift_odd u1 _ z h0
    have b2 := diag_shift_even u2 _ z h2
    rw [← hp] at b0
    rw [← hq] at b2
    simp only [texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b0 b2
    omega
  · intro z h1 h5
    simp only [dOdd, pieceSet, hP, hQ] at h1 h5
    simp at h1 h5
    have b1 := diag_shift_odd u1 _ z h1
    have b5 := diag_shift_even u2 _ z h5
    rw [← hp] at b1
    rw [← hq] at b5
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add] at b1 b5
    omega

/-- **The excluded pairs of the even child, `W_1` even**, separated by `x - y`: `P^{+,1}` (at `U`) and `Q^-` (at `A + 2B`),
and `P^{-,2}` (at `V + B`) and `Q^+` (at `0`). -/
theorem exclEven_evenFirst (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) : ExclEven w u1 u2 := by
  have hP := evenP_ef w hph
  have hQ := evenQ_ef w hph
  have hpl := SiteHullOdd.curO_pos_lt u1
  have hcu : SiteInduction.curO u1 = fracOdd u1 := rfl
  rw [hcu, ← hp] at hpl
  constructor
  · intro z h0 h5
    simp only [dEven, pieceSet, hP, hQ] at h0 h5
    simp at h0 h5
    have b0 := diag_shift_odd u1 _ z h0
    have b5 := diag_shift_even u2 _ z h5
    rw [← hp] at b0
    rw [← hq] at b5
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add] at b0 b5
    omega
  · intro z h3 h4
    simp only [dEven, pieceSet, hP, hQ] at h3 h4
    simp at h3 h4
    have b3 := diag_shift_odd u1 _ z h3
    have b4 := diag_shift_even u2 _ z h4
    rw [← hp] at b3
    rw [← hq] at b4
    simp only [texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at b3 b4
    omega

/-- **`ExclOdd` for every word**: the two excluded mixed pairs of the odd child never meet, in both orientations. -/
theorem exclOdd_all (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    ExclOdd w u1 u2 :=
  exclOdd_of w u1 u2 hp hq (fun hph => exclOdd_evenFirst w u1 u2 hph hp hq)

/-- **`ExclEven` for every word**: the two excluded mixed pairs of the even child never meet, in both orientations. -/
theorem exclEven_all (w u1 u2 : Word) (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2) :
    ExclEven w u1 u2 :=
  exclEven_of w u1 u2 hp hq (fun hph => exclEven_evenFirst w u1 u2 hph hp hq)

/-! ### Condition (C) without the excluded pairs as an input -/

/-- **Condition (C), odd standard child**, with the excluded pairs proved (`exclOdd_all`). -/
theorem closedPathOdd_of (w u1 u2 : Word)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (TP TQ : Finset Site) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored TP (SiteStrings.hWordOf u1 false) (SiteStrings.vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored TQ (SiteStrings.hWordOf u2 true) (SiteStrings.vWordOf u2 true) oQ)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + texV1Even (parentsAt w).even ∈ tEvenSet u2 →
      oQ (x + texV1Even (parentsAt w).even) - oQ x = k)
    (hcompat : MixedCompatOdd w u1 u2 (placedOdd w oP oQ c)) (htri : TriOdd w u1 u2 oP oQ c) :
    ClosedPathOdd w u1 u2 (placedOdd w oP oQ c) :=
  closedPathOdd_standard w u1 u2 hp hq oP oQ TP TQ c hRP hRQ hdbl hcompat (exclOdd_all w u1 u2 hp hq) htri

/-- **Condition (C), even standard child**, with the excluded pairs proved (`exclEven_all`). -/
theorem closedPathEven_of (w u1 u2 : Word)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : ℤ × ℤ → ℤ) (TP TQ : Finset Site) (c : ℕ → ℤ)
    (hRP : SurgicalWeak.RespectsAnchored TP (SiteStrings.hWordOf u1 false) (SiteStrings.vWordOf u1 false) oP)
    (hRQ : SurgicalWeak.RespectsAnchored TQ (SiteStrings.hWordOf u2 true) (SiteStrings.vWordOf u2 true) oQ)
    (hdbl : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + texV2 (parentsAt w).odd ∈ tOddSet u1 →
      oP (x + texV2 (parentsAt w).odd) - oP x -
        ClosedPathSum.dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) x = k)
    (hcompat : MixedCompatEven w u1 u2 (placedEven w oP oQ c)) (htri : TriEven w u1 u2 oP oQ c) :
    ClosedPathEven w u1 u2 (placedEven w oP oQ c) :=
  closedPathEven_standard w u1 u2 hp hq oP oQ TP TQ c hRP hRQ hdbl hcompat (exclEven_all w u1 u2 hp hq) htri

end FLatticePaper.Tiles.ClosedPathDiagonal
