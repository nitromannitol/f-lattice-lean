import FLatticePaper.Construction.PureRank1

-- PureRank2: part 2 of 5; declarations from window_alias to valMinus_Vlast.
namespace FLatticePaper.PureRank
open Classical

/-- **The finite window (the note's complete alias window).** Two native points differ by an alias: `|i| ≤ 2`, `|j| ≤ 1`.
Proof by the deck coordinates: `i·T = (d+1)Δx + (d−1)Δy` and `j·T = dΔy − Δx` with `T = d² + 2d − 1`. -/
theorem window_alias (d : ℤ) (hd : 3 ≤ d) (p q : Pt) (hp : NativeP d p) (hq : NativeP d q) (i j : ℤ)
    (h : q = shiftP d p i j) : -2 ≤ i ∧ i ≤ 2 ∧ -1 ≤ j ∧ j ≤ 1 := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := nativeP_bounds d (by omega) p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := nativeP_bounds d (by omega) q hq
  have hT : (0:ℤ) < d * d + 2 * d - 1 := by nlinarith
  have hi : i * (d * d + 2 * d - 1) = (d + 1) * (q.1 - p.1) + (d - 1) * (q.2 - p.2) := by
    subst h
    simp only [shiftP]
    ring
  have hj : j * (d * d + 2 * d - 1) = d * (q.2 - p.2) - (q.1 - p.1) := by
    subst h
    simp only [shiftP]
    ring
  have hdx1 : q.1 - p.1 ≤ 2 * d - 2 := by omega
  have hdx2 : -(2 * d - 2) ≤ q.1 - p.1 := by omega
  have hdy1 : q.2 - p.2 ≤ d + 1 := by omega
  have hdy2 : -(d + 1) ≤ q.2 - p.2 := by omega
  have hd1 : (0:ℤ) ≤ d + 1 := by omega
  have hd2 : (0:ℤ) ≤ d - 1 := by omega
  have hd0 : (0:ℤ) ≤ d := by omega
  have hA1 : (d + 1) * (q.1 - p.1) ≤ (d + 1) * (2 * d - 2) := mul_le_mul_of_nonneg_left hdx1 hd1
  have hA2 : -((d + 1) * (2 * d - 2)) ≤ (d + 1) * (q.1 - p.1) := by nlinarith
  have hB1 : (d - 1) * (q.2 - p.2) ≤ (d - 1) * (d + 1) := mul_le_mul_of_nonneg_left hdy1 hd2
  have hB2 : -((d - 1) * (d + 1)) ≤ (d - 1) * (q.2 - p.2) := by nlinarith
  have hC1 : d * (q.2 - p.2) ≤ d * (d + 1) := mul_le_mul_of_nonneg_left hdy1 hd0
  have hC2 : -(d * (d + 1)) ≤ d * (q.2 - p.2) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc
    have h3 : (3:ℤ) ≤ -i := by omega
    have h4 : 3 * (d * d + 2 * d - 1) ≤ -i * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (3:ℤ) ≤ i := by omega
    have h4 : 3 * (d * d + 2 * d - 1) ≤ i * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (2:ℤ) ≤ -j := by omega
    have h4 : 2 * (d * d + 2 * d - 1) ≤ -j * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (2:ℤ) ≤ j := by omega
    have h4 : 2 * (d * d + 2 * d - 1) ≤ j * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith

/-- **Rank uniqueness.** The rank of a point is determined: two alias translates that are representatives coincide,
because their difference is an alias (the window) and a nonzero alias translate of a representative is not a representative. -/
theorem rankOf_unique (d : ℤ) (hd : 3 ≤ d) (p : Pt) (r r' : ℤ) (h : RankOf d p r) (h' : RankOf d p r') : r = r' := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := h
  obtain ⟨i', j', hi', hrep', rfl⟩ := h'
  have hnat : ∀ a b, IsAlias a b → IsRepP d (shiftP d p a b) → NativeP d (shiftP d p a b) := by
    intro a b _ hr
    rcases hr with hf | ⟨hn, -, -⟩
    · exact freeP_native d hd _ hf
    · exact hn
  have hnq : NativeP d (shiftP d p i j) := hnat i j hi hrep
  have hnq' : NativeP d (shiftP d p i' j') := hnat i' j' hi' hrep'
  by_cases hk : i' - i = 0 ∧ j' - j = 0
  · obtain ⟨hk1, hk2⟩ := hk
    have e1 : i' = i := by omega
    have e2 : j' = j := by omega
    subst e1; subst e2
    rfl
  · exfalso
    set q := shiftP d p i j with hqdef
    have hq' : shiftP d p i' j' = shiftP d q (i' - i) (j' - j) := by
      rw [hqdef, shiftP_shiftP]
      congr 1 <;> ring_nf
    have hwin := window_alias d hd q (shiftP d p i' j') hnq hnq' (i' - i) (j' - j) hq'
    have hki : IsAlias (i' - i) (j' - j) := by
      obtain ⟨a1, a2, a3, a4⟩ := hwin
      exact ⟨a1, a2, a3, a4⟩
    rw [hq'] at hrep'
    by_cases hqf : IsFreeP d q
    · exact not_rep_of_free_translate d hd q hqf _ _ hki hk hrep'
    · exact not_rep_of_bulk_translate d hd q hrep hqf _ _ hki hk hrep'

/-! ## The families of the native domain (step (ii))

The native domain splits into six families: free points (F0), the top row `y = d+1, x ≤ 1` (F2, represented by the H point
`(x+d−1, 0)`), the corner `(2,d+1)` (F3, represented by `(2−d, d)`), the anti-diagonal `x+y = d+2, y ≤ d` (F4, represented by
`(x−d, y−1)`), the point `(d,1)` (F5, represented by `(0,0)`), and the interior (F1, its own representative). -/

/-- An interior point is its own representative. -/
theorem rep_interior (d : ℤ) (x y : ℤ) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1)) : IsRepP d (x, y) := by
  have hn' := hn
  unfold NativeP at hn'
  simp only [Prod.mk.injEq] at hn'
  unfold IsFreeP IsHc IsVc at hf
  simp only [Prod.mk.injEq] at hf
  right
  refine ⟨hn, ?_, ?_⟩
  · intro i j hij hfree
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
    unfold IsFreeP IsHc IsVc at hfree
    simp only [shiftP, Prod.mk.injEq] at hfree
    interval_cases i <;> interval_cases j <;> omega
  · intro i j hij hnat hlex
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
    unfold NativeP at hnat
    simp only [shiftP, Prod.mk.injEq] at hnat
    unfold LexGt at hlex
    simp only [shiftP] at hlex
    interval_cases i <;> interval_cases j <;> omega

/-- The top row point `(x, d+1)` with `x ≤ 1` is translated by `(0,−1)` onto the H point `(x+d−1, 0)`. -/
theorem rankOf_top (d : ℤ) (x : ℤ) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 1) :
    RankOf d (x, d + 1) (valMinus d (x + d - 1, 0) - 2 * (d + 1)) := by
  have hs : shiftP d (x, d + 1) 0 (-1) = (x + d - 1, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    left
    unfold IsHc
    exact ⟨rfl, by show 1 ≤ x + d - 1; omega, by show x + d - 1 ≤ d; omega⟩
  · rw [hs]
    ring

/-- The corner `(2, d+1)` is translated by `(−1,0)` onto the V-last point `(2−d, d)`. -/
theorem rankOf_corner (d : ℤ) :
    RankOf d (2, d + 1) (valMinus d (2 - d, d) + 2 * d) := by
  have hs : shiftP d (2, d + 1) (-1) 0 = (2 - d, d) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inr (Or.inr rfl)
  · rw [hs]
    ring

/-- The anti-diagonal point `(x, y)` with `x + y = d+2` and `y ≤ d` is translated by `(−1,0)` onto the V point `(x−d, y−1)`. -/
theorem rankOf_anti (d : ℤ) (x y : ℤ) (hs : x + y = d + 2) (hxd : x ≤ d) (hyd : y ≤ d) :
    RankOf d (x, y) (valMinus d (x - d, y - 1) + 2 * d) := by
  have e : shiftP d (x, y) (-1) 0 = (x - d, y - 1) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    simp only [Prod.mk.injEq]
    omega
  · rw [e]
    ring

/-- The point `(d,1)` is translated by `(−1,0)` onto the origin. -/
theorem rankOf_fifth (d : ℤ) :
    RankOf d (d, 1) (valMinus d (0, 0) + 2 * d) := by
  have e : shiftP d (d, 1) (-1) 0 = (0, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inl rfl
  · rw [e]
    ring

/-- The rank of a native point, by family. -/
noncomputable def qRank (d : ℤ) (p : Pt) : ℤ :=
  if IsFreeP d p then valMinus d p
  else if p.2 = d + 1 ∧ p.1 ≤ 1 then valMinus d (p.1 + d - 1, 0) - 2 * (d + 1)
  else if p = (2, d + 1) then valMinus d (2 - d, d) + 2 * d
  else if p.1 + p.2 = d + 2 then valMinus d (p.1 - d, p.2 - 1) + 2 * d
  else if p = (d, 1) then valMinus d (0, 0) + 2 * d
  else valMinus d p

/-- Every native point has its family rank as a rank. -/
theorem rankOf_qRank (d : ℤ) (hd : 3 ≤ d) (x y : ℤ) (hn : NativeP d (x, y)) :
    RankOf d (x, y) (qRank d (x, y)) := by
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 := nativeP_bounds d (by omega) (x, y) hn
  obtain ⟨hx1, hx2, -, hy2⟩ := hb
  have hn' := hn
  unfold NativeP at hn'
  simp only [Prod.mk.injEq] at hn'
  simp only [qRank, Prod.mk.injEq]
  split_ifs with h1 h2 h3 h4 h5
  · exact rankOf_self d (x, y) (Or.inl h1)
  · obtain ⟨rfl, h2'⟩ := h2
    exact rankOf_top d x hx1 h2'
  · obtain ⟨rfl, rfl⟩ := h3
    exact rankOf_corner d
  · have hyd : y ≤ d := by omega
    exact rankOf_anti d x y h4 hx2 hyd
  · rw [h5.1, h5.2]
    exact rankOf_fifth d
  · have hyd : y ≤ d := by omega
    exact rankOf_self d (x, y) (rep_interior d x y hn h1 hyd h4 h5)

/-- **The rank of a native point is its family rank.** Any rank of a native point equals `qRank`, by the uniqueness of the rank. -/
theorem rankOf_eq_qRank (d : ℤ) (hd : 3 ≤ d) (x y : ℤ) (hn : NativeP d (x, y)) (r : ℤ)
    (h : RankOf d (x, y) r) : r = qRank d (x, y) :=
  rankOf_unique d hd (x, y) r _ h (rankOf_qRank d hd x y hn)

/-! ## The free-root gate (step (ii), free sources)

For every free native point with prescribed direction, every rank of its target is below its rank.
The targets may lie outside the native domain; their ranks are read through their representative translates. -/

/-- A representative is free, or non-free and native with the interior shape. -/
theorem rep_cases (d : ℤ) (q : Pt) (hq : IsRepP d q) :
    IsFreeP d q ∨ (NativeP d q ∧ q.2 ≤ d ∧ q.1 + q.2 ≠ d + 2 ∧ ¬ (q.1 = d ∧ q.2 = 1)) := by
  obtain ⟨x, y⟩ := q
  by_cases hf : IsFreeP d (x, y)
  · exact Or.inl hf
  right
  unfold IsRepP at hq
  rcases hq with hf' | ⟨hn, hfree, -⟩
  · exact absurd hf' hf
  have H1 := hfree 0 (-1) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have H2 := hfree (-1) 0 ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  refine ⟨hn, ?_⟩
  unfold IsFreeP IsHc IsVc at H1 H2 hf
  unfold NativeP at hn
  simp only [shiftP, Prod.mk.injEq] at H1 H2 hf hn
  omega

set_option maxHeartbeats 400000 in
/-- The H point with even `x` (root value `2x`): every rank of its prescribed target `(x−1, 0)` is below `2x`. -/
theorem gate_H_even_all (d x : ℤ) (hd : 3 ≤ d) (hx2 : 2 ≤ x) (hxd : x ≤ d) (hev : x % 2 = 0)
    (r : ℤ) (hr : RankOf d (x - 1, 0) r) : r < 2 * x := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

set_option maxHeartbeats 400000 in
/-- The H point with odd `x ≠ d` (root value `2x+1`): its target is `(x, −1)`. -/
theorem gate_H_odd_all (d x : ℤ) (hd : 3 ≤ d) (hx1 : 1 ≤ x) (hxd : x < d) (hod : x % 2 = 1)
    (r : ℤ) (hr : RankOf d (x, -1) r) : r < 2 * x + 1 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

set_option maxHeartbeats 400000 in
/-- The H point `(d, 0)` (root value `2d+1`): its target is `(d, 1)`. -/
theorem gate_H_d_all (d : ℤ) (hd : 3 ≤ d)
    (r : ℤ) (hr : RankOf d (d, 1) r) : r < 2 * d + 1 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

set_option maxHeartbeats 400000 in
/-- The origin (root value `0`): its target is `(−1, 0)`. -/
theorem gate_origin_all (d : ℤ) (hd : 3 ≤ d)
    (r : ℤ) (hr : RankOf d (-1, 0) r) : r < 0 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

set_option maxHeartbeats 400000 in
/-- The V point `(2−d, d)` (root value `−2d`): its target is `(1−d, d)`. -/
theorem gate_Vlast_all (d : ℤ) (hd : 3 ≤ d)
    (r : ℤ) (hr : RankOf d (1 - d, d) r) : r < -2 * d := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

set_option maxHeartbeats 400000 in
/-- The V point `(x, 1−x)` with `1 ≤ 1−x ≤ d−1` odd sum (root value `2x−3`): its target is `(x, 2−x)`. -/
theorem gate_V_odd_all (d x : ℤ) (hd : 3 ≤ d) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0)
    (r : ℤ) (hr : RankOf d (x, 2 - x) r) : r < 2 * x - 3 := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)

theorem valMinus_V_odd (d x : ℤ) (hx1 : 2 - d ≤ x) (hx0 : x ≤ 0) :
    valMinus d (x, 1 - x) = 2 * x - 3 := by
  have h1 := hx1
  unfold valMinus
  simp only [IsHc, IsVc, Prod.mk.injEq]
  split_ifs <;> omega

theorem valMinus_origin (d : ℤ) : valMinus d (0, 0) = 0 := by
  simp [valMinus, IsHc, IsVc]

theorem valMinus_Vlast (d : ℤ) (hd : 3 ≤ d) : valMinus d (2 - d, d) = -2 * d := by
  simp [valMinus, IsHc, IsVc]
  omega

