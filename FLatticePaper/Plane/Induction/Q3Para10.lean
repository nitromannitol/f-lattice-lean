import FLatticePaper.Plane.Induction.Q3VPath
import FLatticePaper.Plane.Induction.Q3Arithmetic

/-! Task 60, the first V block at `l = D` and paragraph 10 (fix Q3.md paragraphs 9–10).

With `N, D` the odd parent, `d = 2D + d_q`, `n = 2N + n_q`, `ε = N d − D n`, `B_0 = s(U_p) = 2C`, `C = DL + N(d−n)`,
`U_q = (d_q, n_q)`, `U = (d, n)`:
* a child left V vertex is `IsLeftVertex` (a left boundary site of the closed polygon with the parity-resolved V spectrum);
* the block vertex at `l = D`: the child floor is `⌊(d−n)D/d⌋ = D − N + ⌊ε/d⌋`, so for `ε = −1` the vertex is
  `A = (N−D+1, D+N)` with `s(A) = L − 2` (the top of the odd spectrum), and for `ε = +1` the parent vertex
  `v_D = (N−D, D+N−1)` is replaced by `V_p + I = (N−D+1, D+N−1)`, which has `s = 2n + 2` (above the even spectrum);
* paragraph 10: `x = v + i U_p` with `x, x + U_q ∈ E` gives `l_χ − s(v) ≤ i B_0 ≤ B_0 + h_χ − s(v)`, hence `i ∈ {0, 1}`
  for a child left vertex `v`, and `i = 0` for the exceptional vertex `V_p + I` when `ε = +1`.
The white/black conclusion (a boundary vertex is white; both centres are black) is field-level and is not formalized here. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `T − C ≥ 0` for the child's period denominator `T = d² + 2dn − n²` and `C = D(d+n) + N(d−n)`:
the difference is `d(d − D − N) + n(2d − D + N − n)`. -/
theorem periodDen_sub_parentC_nonneg (D N d n : ℤ) (hN0 : 0 ≤ N) (hND : N ≤ D) (hn0 : 0 ≤ n)
    (hnd : n < d) (hdD : 2 * D ≤ d) :
    D * (d + n) + N * (d - n) ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
  have h1 : 0 ≤ d - D - N := by omega
  have h2 : 0 ≤ 2 * d - D + N - n := by omega
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ d by omega) h1, mul_nonneg hn0 h2]

/-- `d + n ≤ C = D(d+n) + N(d−n)` for `D ≥ 1`. -/
theorem sum_le_parentC_gen (D N d n : ℤ) (hD : 0 < D) (hN0 : 0 ≤ N) (hn0 : 0 ≤ n) (hnd : n < d) :
    d + n ≤ D * (d + n) + N * (d - n) := by
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ D - 1 by omega) (show (0 : ℤ) ≤ d + n by omega),
    mul_nonneg hN0 (show (0 : ℤ) ≤ d - n by omega)]

namespace ChildFrame
variable (frame : ChildFrame)

/-- A child left V vertex: a left boundary site of the closed polygon whose `s` lies in the parity-resolved V spectrum. -/
def IsLeftVertex (v : Site) : Prop :=
  v ∈ frame.closedPolygon ∧ (v.1 - 1, v.2) ∉ frame.closedPolygon ∧
    (EvenSite v → 0 ≤ frame.sGrade v ∧ frame.sGrade v ≤ 2 * frame.child.num) ∧
    (¬ EvenSite v → 2 - frame.child.den + frame.child.num ≤ frame.sGrade v ∧
      frame.sGrade v ≤ frame.child.den + frame.child.num - 2)

/-- The linear facts of a child frame that the arithmetic below uses. -/
theorem linear_facts :
    frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den ∧
    frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num ∧
    0 < frame.parents.odd.den ∧ 0 ≤ frame.parents.odd.num ∧ frame.parents.odd.num < frame.parents.odd.den ∧
    0 < frame.parents.even.den ∧ 0 ≤ frame.parents.even.num ∧ frame.parents.even.num ≤ frame.parents.even.den ∧
    (frame.child.num + frame.child.den) % 2 = 0 := by
  obtain ⟨hD, hN0, hND⟩ := frame.valid.odd_bounds
  obtain ⟨hq, hn0, hnq⟩ := frame.valid.even_bounds
  have hop : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hep : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  have hn : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
    simp only [ChildFrame.child, Parents.current, Parents.combine]
    ring
  refine ⟨hd, hn, hD, hN0, ?_, hq, hn0, hnq, ?_⟩
  · omega
  · omega

theorem sGrade_add (x y : Site) : frame.sGrade (x + y) = frame.sGrade x + frame.sGrade y := by
  unfold sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- `s(U_q) = T − 2C`: the even parent's kernel has child `s`-grade `T − B_0`. -/
theorem sGrade_UQ :
    frame.sGrade (frame.parents.even.den, frame.parents.even.num) =
      frame.child.periodDenominator - 2 * frame.parentC := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  unfold sGrade parentC Fraction.periodDenominator
  dsimp only
  rw [hd, hn]
  ring

/-- `s(x + i U_p) = s(x) + i B_0` with `B_0 = 2C`, `U_p = (2D, 2N)`. -/
theorem sGrade_addUp (x : Site) (i : ℤ) :
    frame.sGrade (x + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num))) =
      frame.sGrade x + i * (2 * frame.parentC) := by
  unfold sGrade parentC
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem evenSite_add_Uq (x : Site) :
    EvenSite (x + (frame.parents.even.den, frame.parents.even.num)) ↔ EvenSite x := by
  have hE : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem evenSite_add_Up (x : Site) (i : ℤ) :
    EvenSite (x + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num))) ↔ EvenSite x := by
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  rw [show x.1 + i * (2 * frame.parents.odd.den) + (x.2 + i * (2 * frame.parents.odd.num)) =
      (x.1 + x.2) + 2 * (i * (frame.parents.odd.den + frame.parents.odd.num)) by ring,
    Int.add_mul_emod_self_left]

theorem parentC_ge : frame.child.den + frame.child.num ≤ frame.parentC := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hnd : frame.child.num < frame.child.den := by omega
  unfold parentC
  exact sum_le_parentC_gen _ _ _ _ hD hN0 (by omega) hnd

theorem parentC_le_periodDenominator : frame.parentC ≤ frame.child.periodDenominator := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hnd : frame.child.num < frame.child.den := by omega
  have hdD : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
  unfold parentC Fraction.periodDenominator
  exact periodDen_sub_parentC_nonneg _ _ _ _ hN0 hND.le (by omega) hnd hdD

/-- The window of `E` on the even branch, for `x` and `x + U_q` in `E`. -/
theorem sGrade_window_even (x : Site) (hx : x ∈ frame.closedPolygon)
    (hxu : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) (hpar : EvenSite x) :
    0 ≤ frame.sGrade x ∧ frame.sGrade x ≤ 2 * frame.parentC + 2 * frame.child.num := by
  rw [frame.mem_closedPolygon_iff] at hx hxu
  have hpu := (frame.evenSite_add_Uq x).mpr hpar
  rcases hx with ⟨_, _, _, hx0, _⟩ | ⟨hn, _⟩
  · rcases hxu with ⟨_, _, _, _, hu1⟩ | ⟨hn, _⟩
    · rw [frame.sGrade_add, frame.sGrade_UQ] at hu1
      exact ⟨hx0, by linarith⟩
    · exact absurd hpu hn
  · exact absurd hpar hn

/-- The window of `E` on the odd branch, for `x` and `x + U_q` in `E`. -/
theorem sGrade_window_odd (x : Site) (hx : x ∈ frame.closedPolygon)
    (hxu : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) (hpar : ¬ EvenSite x) :
    2 - frame.child.den + frame.child.num ≤ frame.sGrade x ∧
      frame.sGrade x ≤ 2 * frame.parentC + (frame.child.den + frame.child.num - 2) := by
  rw [frame.mem_closedPolygon_iff] at hx hxu
  have hpu : ¬ EvenSite (x + (frame.parents.even.den, frame.parents.even.num)) := fun h =>
    hpar ((frame.evenSite_add_Uq x).mp h)
  rcases hx with ⟨he, _⟩ | ⟨_, _, _, hx0, hx1⟩
  · exact absurd he hpar
  · rcases hxu with ⟨he, _⟩ | ⟨_, _, _, hu0, hu1⟩
    · exact absurd he hpu
    · rw [frame.sGrade_add, frame.sGrade_UQ] at hu1
      exact ⟨hx0, by linarith⟩

/-- The index inequality: `x = v + i U_p` with `x, x + U_q ∈ E` and `v` a child left vertex force `i ∈ {0, 1}`. -/
theorem index_of_left_vertex (v x : Site) (i : ℤ)
    (hx : x = v + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num)))
    (hv : frame.IsLeftVertex v) (hxE : x ∈ frame.closedPolygon)
    (hxuE : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) :
    i = 0 ∨ i = 1 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hC := frame.parentC_ge
  have hs : frame.sGrade x = frame.sGrade v + i * (2 * frame.parentC) := by
    rw [hx, frame.sGrade_addUp]
  have hB : 0 < 2 * frame.parentC := by omega
  by_cases hvpar : EvenSite v
  · obtain ⟨hl, hh⟩ := hv.2.2.1 hvpar
    have hxpar : EvenSite x := by
      rw [hx]
      exact (frame.evenSite_add_Up v i).mpr hvpar
    obtain ⟨w0, w1⟩ := frame.sGrade_window_even x hxE hxuE hxpar
    exact index_mem_zero_one_of_spectrum i (2 * frame.parentC) 0 (frame.sGrade v) (2 * frame.child.num) hB
      (by omega) hl hh (by linarith) (by linarith)
  · obtain ⟨hl, hh⟩ := hv.2.2.2 hvpar
    have hxpar : ¬ EvenSite x := by
      rw [hx]
      exact fun h => hvpar ((frame.evenSite_add_Up v i).mp h)
    obtain ⟨w0, w1⟩ := frame.sGrade_window_odd x hxE hxuE hxpar
    exact index_mem_zero_one_of_spectrum i (2 * frame.parentC) (2 - frame.child.den + frame.child.num)
      (frame.sGrade v) (frame.child.den + frame.child.num - 2) hB (by omega) hl hh (by linarith) (by linarith)

/-- The exceptional vertex `V_p + I = (N − D + 1, D + N − 1)`. -/
theorem sGrade_VpI :
    frame.sGrade (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) = 2 * frame.eps + 2 * frame.child.num := by
  rw [frame.eps_eq]
  unfold sGrade
  dsimp only
  ring

/-- The child's floor at `l = D`: `⌊(d − n) D / d⌋ = D − N + ⌊ε/d⌋`, from `(d − n) D = ε + (D − N) d`. -/
theorem floor_at_D :
    (frame.child.den - frame.child.num) * frame.parents.odd.den / frame.child.den =
      (frame.parents.odd.den - frame.parents.odd.num) + frame.eps / frame.child.den := by
  obtain ⟨hd, -, hD, -, -, hq, -, -, -⟩ := frame.linear_facts
  have hd0 : 0 < frame.child.den := by omega
  have hkey : (frame.child.den - frame.child.num) * frame.parents.odd.den =
      frame.eps + (frame.parents.odd.den - frame.parents.odd.num) * frame.child.den := by
    rw [frame.eps_eq]
    ring
  rw [hkey, Int.add_mul_ediv_right _ _ hd0.ne', add_comm]

theorem floor_at_D_pos (h : frame.eps = 1) :
    (frame.child.den - frame.child.num) * frame.parents.odd.den / frame.child.den =
      frame.parents.odd.den - frame.parents.odd.num := by
  obtain ⟨hd, -, hD, -, -, hq, -, -, -⟩ := frame.linear_facts
  have h1d : (1 : ℤ) / frame.child.den = 0 := Int.ediv_eq_zero_of_lt (by norm_num) (by omega)
  rw [frame.floor_at_D, h, h1d, add_zero]

theorem floor_at_D_neg (h : frame.eps = -1) :
    (frame.child.den - frame.child.num) * frame.parents.odd.den / frame.child.den =
      frame.parents.odd.den - frame.parents.odd.num - 1 := by
  obtain ⟨hd, -, hD, -, -, hq, -, -, -⟩ := frame.linear_facts
  rw [frame.floor_at_D, h, ediv_eq_neg_one_of_range (-1) frame.child.den (by omega) (by omega) (by norm_num)]
  ring

/-- For `ε = +1` the exceptional vertex `V_p + I` has `s = 2n + 2`, above the even spectrum `[0, 2n]`:
it is not a child left V vertex. -/
theorem not_left_VpI_of_pos (h : frame.eps = 1) :
    ¬ frame.IsLeftVertex (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) := by
  intro hv
  have hev : EvenSite (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) := by
    unfold EvenSite
    dsimp only
    omega
  obtain ⟨-, -, hs, -⟩ := hv
  have := (hs hev).2
  rw [frame.sGrade_VpI, h] at this
  omega

/-- The exceptional vertex with `s = 2n + 2` (`ε = +1`): the window forces `i = 0`. -/
theorem exceptional_i_zero (h : frame.eps = 1) (x : Site) (i : ℤ)
    (hx : x = (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1) +
      (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num)))
    (hxE : x ∈ frame.closedPolygon)
    (hxuE : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) :
    i = 0 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hC := frame.parentC_ge
  have hs : frame.sGrade x = frame.sGrade (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) + i * (2 * frame.parentC) := by
    rw [hx, frame.sGrade_addUp]
  rw [frame.sGrade_VpI, h] at hs
  have hev : EvenSite (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) := by
    unfold EvenSite
    dsimp only
    omega
  have hxpar : EvenSite x := by
    rw [hx]
    exact (frame.evenSite_add_Up _ i).mpr hev
  obtain ⟨w0, w1⟩ := frame.sGrade_window_even x hxE hxuE hxpar
  have hdn : frame.child.num + 2 ≤ frame.child.den := by omega
  have hCnn : 0 ≤ frame.parentC := by omega
  have hi1 : i ≤ 0 := by
    by_contra hc
    have hi : 1 ≤ i := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ i - 1 by omega) hCnn]
  have hi2 : 0 ≤ i := by
    by_contra hc
    have hi : i ≤ -1 := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - i by omega) hCnn]
  omega

/-- The block vertex at `l = D` for `ε = −1`: the child floor is `D − N − 1`, so the vertex is
`A = (N − D + 1, D + N)`, and `s(A) = 2ε + L = L − 2`, the top of the odd spectrum. -/
theorem sGrade_childFloorD (h : frame.eps = -1) :
    frame.sGrade (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num) =
      frame.child.den + frame.child.num - 2 := by
  have h2 : frame.sGrade (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num) = 2 * frame.eps + frame.child.den + frame.child.num := by
    rw [frame.eps_eq]
    unfold sGrade
    dsimp only
    ring
  rw [h2, h]
  ring

/-- `s(A − (1,0)) = 2ε`: the left neighbour of the child-floor vertex has `s = −2` when `ε = −1`. -/
theorem sGrade_left_neighbour :
    frame.sGrade (frame.parents.odd.num - frame.parents.odd.den, frame.parents.odd.den + frame.parents.odd.num) =
      2 * frame.eps := by
  rw [frame.eps_eq]
  unfold sGrade
  dsimp only
  ring

/-- The W = 0 block vertex at `l = D` is a child left V vertex. -/
theorem isLeftVertex_childFloorD (h : frame.eps = -1) :
    frame.IsLeftVertex (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num) := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hnd : frame.child.num < frame.child.den := by omega
  have hnn : 0 ≤ frame.child.num := by omega
  have hdD : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
  have hCT : frame.parents.odd.den * (frame.child.den + frame.child.num) +
      frame.parents.odd.num * (frame.child.den - frame.child.num) ≤
      frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 :=
    periodDen_sub_parentC_nonneg _ _ _ _ hN0 hND.le hnn hnd hdD
  have hs := frame.sGrade_childFloorD h
  have hsl := frame.sGrade_left_neighbour
  rw [h] at hsl
  have hodd : ¬ EvenSite (frame.parents.odd.num - frame.parents.odd.den + 1,
      frame.parents.odd.den + frame.parents.odd.num) := by
    unfold EvenSite
    dsimp only
    omega
  have hnb : EvenSite (frame.parents.odd.num - frame.parents.odd.den + 1 - 1,
      frame.parents.odd.den + frame.parents.odd.num) := by
    unfold EvenSite
    dsimp only
    omega
  have hT0 : 0 ≤ frame.child.periodDenominator := by
    unfold Fraction.periodDenominator
    nlinarith [mul_nonneg hnn (show (0 : ℤ) ≤ frame.child.den by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
        (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega)]
  unfold IsLeftVertex
  refine ⟨?_, ?_, fun he => absurd he hodd, fun _ => ⟨?_, ?_⟩⟩
  · rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨hodd, ?_, ?_, ?_, ?_⟩
    · unfold ChildFrame.tGrade Fraction.periodDenominator
      dsimp only
      nlinarith
    · unfold ChildFrame.tGrade
      dsimp only
      nlinarith [mul_nonneg hnn (show (0 : ℤ) ≤ frame.parents.odd.den - frame.parents.odd.num - 1 by omega),
        mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega)
          (show (0 : ℤ) ≤ frame.parents.odd.den + frame.parents.odd.num by omega)]
    · rw [hs]
      omega
    · rw [hs]
      omega
  · show (frame.parents.odd.num - frame.parents.odd.den + 1 - 1, frame.parents.odd.den + frame.parents.odd.num) ∉
      frame.closedPolygon
    intro hmem
    rw [frame.mem_closedPolygon_iff] at hmem
    rcases hmem with ⟨_, _, _, hs0, _⟩ | ⟨hne, _⟩
    · simp only [add_sub_cancel_right] at hs0
      rw [hsl] at hs0
      omega
    · exact hne hnb
  · rw [hs]
    omega
  · rw [hs]

end ChildFrame

end FLatticePaper.Induction
