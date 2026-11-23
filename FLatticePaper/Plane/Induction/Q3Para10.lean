import FLatticePaper.Plane.Induction.Q3VPath
import FLatticePaper.Plane.Induction.Q3Arithmetic
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 60, the first V block at `l ≤ D` and paragraph 10 (fix Q3.md paragraphs 9–10).

Notation: `N, D` the odd parent, `d = 2D + d_q`, `n = 2N + n_q` the child, `L = d + n`, `ε = N d − D n`,
`U = (d, n)` the child's modified kernel, `U_p = (2D, 2N)`, `U_q = (d_q, n_q)`, so `U = U_p + U_q`, and
`C = DL + N(d − n)`, `B_0 = s(U_p) = 2C`.

There is one notion of a child left V vertex: the V cut `freeV` of S3FreeBoundary (left boundary of the closed polygon
with `s` in the V spectrum). Here:
* `block_mem_freeV`: for `1 ≤ l ≤ D` the vertex `(−b, 2l − 1 − b)`, `b = ⌊(d − n) l / d⌋`, is in `freeV`; for `l < D` this
  is the parent vertex `v_l` (`parent_block_mem_freeV`, by `vBlock_floor_agree`);
* `VpI_not_freeV`: for `ε = +1` the exceptional vertex `V_p + I` is not in `freeV` (its left neighbour is in `E`);
* `index_of_freeV`: `x = v + i U_p` with `x, x + U_q ∈ E` and `v ∈ freeV` forces `i ∈ {0, 1}`;
* `exceptional_i_zero`: for `ε = +1` the window forces `i = 0` at `V_p + I`.
The white and black-centre contradiction is in Q3White.lean. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `T − C ≥ 0` for `T = d² + 2dn − n²` and `C = D(d+n) + N(d−n)`: the difference is
`d(d − D − N) + n(2d − D + N − n)`. -/
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

/-- `T ≥ 0` for `T = d² + 2dn − n²` with `0 ≤ n < d`. -/
theorem periodDen_nonneg_gen (d n : ℤ) (hn0 : 0 ≤ n) (hnd : n < d) : 0 ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
  nlinarith [mul_nonneg hn0 (show (0 : ℤ) ≤ d by omega),
    mul_nonneg (show (0 : ℤ) ≤ d - n by omega) (show (0 : ℤ) ≤ d + n by omega)]

namespace ChildFrame
variable (frame : ChildFrame)

/-- The linear facts of a child frame used by the arithmetic: `d = 2D + d_q`, `n = 2N + n_q`, the parent bounds, and
`d + n` even. -/
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

theorem periodDen_nonneg : 0 ≤ frame.child.periodDenominator := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  unfold Fraction.periodDenominator
  exact periodDen_nonneg_gen _ _ (by omega) (by omega)

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

/-- The index inequality: `x = v + i U_p` with `x, x + U_q ∈ E` and `v ∈ freeV` force `i ∈ {0, 1}`. The window of
the spectrum is `[2 − d + n, L − 2]`, which contains the V cut (its even part `[0, 2n]` and its other part) and the
windows of `x` in both parities. -/
theorem index_of_freeV (v x : Site) (i : ℤ)
    (hx : x = v + (i * (2 * frame.parents.odd.den), i * (2 * frame.parents.odd.num)))
    (hv : v ∈ frame.freeV) (hxE : x ∈ frame.closedPolygon)
    (hxuE : x + (frame.parents.even.den, frame.parents.even.num) ∈ frame.closedPolygon) :
    i = 0 ∨ i = 1 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hC := frame.parentC_ge
  have hs : frame.sGrade x = frame.sGrade v + i * (2 * frame.parentC) := by
    rw [hx, frame.sGrade_addUp]
  have hB : 0 < 2 * frame.parentC := by omega
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hv
  obtain ⟨-, -, hvs⟩ := hv
  unfold ChildFrame.vSpectrum at hvs
  have hlow : 2 - frame.child.den + frame.child.num ≤ frame.sGrade x := by
    by_cases hxpar : EvenSite x
    · have h1 := (frame.sGrade_window_even x hxE hxuE hxpar).1
      omega
    · exact (frame.sGrade_window_odd x hxE hxuE hxpar).1
  have hup : frame.sGrade x ≤ 2 * frame.parentC + (frame.child.den + frame.child.num - 2) := by
    by_cases hxpar : EvenSite x
    · have h1 := (frame.sGrade_window_even x hxE hxuE hxpar).2
      omega
    · exact (frame.sGrade_window_odd x hxE hxuE hxpar).2
  exact index_mem_zero_one_of_spectrum i (2 * frame.parentC) (2 - frame.child.den + frame.child.num)
    (frame.sGrade v) (frame.child.den + frame.child.num - 2) hB (by omega) (by omega) (by omega)
    (by linarith) (by linarith)

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

/-- The residue `q = (d − n) l − d ⌊(d − n) l / d⌋` lies in `[1, d − 1]` for `1 ≤ l ≤ D`: `q = 0` would give
`d ∣ l` (since `ε = ±1` makes `d ∣ ε l`), impossible for `1 ≤ l < d`. -/
theorem block_q_bounds (l : ℤ) (hl1 : 1 ≤ l) (hl2 : l ≤ frame.parents.odd.den) :
    1 ≤ (frame.child.den - frame.child.num) * l - frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) ∧
    (frame.child.den - frame.child.num) * l - frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) ≤
      frame.child.den - 1 := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hdpos : 0 < frame.child.den := by omega
  have hlt : l < frame.child.den := by omega
  have hr0 := Int.emod_nonneg ((frame.child.den - frame.child.num) * l) hdpos.ne'
  have hr1 := Int.emod_lt_of_pos ((frame.child.den - frame.child.num) * l) hdpos
  rw [Int.emod_def] at hr0 hr1
  have hne : (frame.child.den - frame.child.num) * l -
      frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) ≠ 0 := by
    intro h0
    have hxb : (frame.child.den - frame.child.num) * l =
        frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) := by
      linarith
    generalize hb : (frame.child.den - frame.child.num) * l / frame.child.den = b at hxb
    have hε := frame.eps_eq
    have hKey : frame.eps * l = frame.child.den *
        (frame.parents.odd.num * l - frame.parents.odd.den * (l - b)) := by
      linear_combination l * hε + frame.parents.odd.den * hxb
    generalize hK : frame.parents.odd.num * l - frame.parents.odd.den * (l - b) = K at hKey
    rcases frame.eps_unit with h1 | h1 <;> rw [h1] at hKey <;>
      rcases (show K ≤ -1 ∨ K = 0 ∨ 1 ≤ K by omega) with hK' | rfl | hK' <;> nlinarith
  generalize hq' : (frame.child.den - frame.child.num) * l -
      frame.child.den * ((frame.child.den - frame.child.num) * l / frame.child.den) = q at hr0 hr1 hne ⊢
  constructor <;> omega

/-- The block vertex `(−b, 2l − 1 − b)`, `b = ⌊(d − n) l / d⌋`, for `1 ≤ l ≤ D`, lies in the V cut `freeV`. Its
`s` is `2q − (d − n)` with `q ∈ [1, d − 1]`, so `s ∈ [2 − d + n, L − 2]`; its left neighbour has `s = 2q − 2d < 0`. -/
theorem block_mem_freeV (l : ℤ) (hl1 : 1 ≤ l) (hl2 : l ≤ frame.parents.odd.den) :
    (-((frame.child.den - frame.child.num) * l / frame.child.den),
      2 * l - 1 - (frame.child.den - frame.child.num) * l / frame.child.den) ∈ frame.freeV := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hdpos : 0 < frame.child.den := by omega
  have hnl : frame.child.num < frame.child.den := by omega
  have hnn : 0 ≤ frame.child.num := by omega
  have hdn : 0 ≤ frame.child.den - frame.child.num := by omega
  have hl0 : 0 ≤ l := by omega
  have hdl : 0 ≤ frame.child.den - 2 * l := by omega
  have hT0 := frame.periodDen_nonneg
  obtain ⟨b, hb⟩ : ∃ b, (frame.child.den - frame.child.num) * l / frame.child.den = b := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by
    rw [← hb]
    exact Int.ediv_nonneg (mul_nonneg hdn hl0) hdpos.le
  have hbl : b ≤ l := by
    have hA := Int.ediv_mul_le ((frame.child.den - frame.child.num) * l) hdpos.ne'
    rw [hb] at hA
    by_contra hc
    have h5 : l + 1 ≤ b := by omega
    nlinarith [mul_le_mul_of_nonneg_right h5 hdpos.le, mul_nonneg hnn hl0]
  have hq' := frame.block_q_bounds l hl1 hl2
  rw [hb] at hq'
  obtain ⟨q, hqdef⟩ : ∃ q, q = (frame.child.den - frame.child.num) * l - frame.child.den * b := ⟨_, rfl⟩
  rw [← hqdef] at hq'
  obtain ⟨hq1, hq2⟩ := hq'
  have hs : frame.sGrade (-b, 2 * l - 1 - b) = 2 * q - (frame.child.den - frame.child.num) := by
    rw [hqdef]
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hsn : frame.sGrade (-b - 1, 2 * l - 1 - b) = 2 * q - 2 * frame.child.den := by
    rw [hqdef]
    unfold ChildFrame.sGrade
    dsimp only
    ring
  rw [hb]
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold EvenSite
      dsimp only
      omega
    · unfold ChildFrame.tGrade Fraction.periodDenominator
      dsimp only
      nlinarith [mul_nonneg hdpos.le hdl, mul_nonneg hnn (show (0 : ℤ) ≤ 2 * frame.child.den - frame.child.num by omega),
        mul_nonneg hb0 hdn]
    · unfold ChildFrame.tGrade
      dsimp only
      nlinarith [mul_le_mul_of_nonneg_right hbl hdn, mul_nonneg hl0 hnn, mul_nonneg hl0 hdpos.le]
    · rw [hs]
      omega
    · rw [hs]
      omega
  · show (-b - 1, 2 * l - 1 - b) ∉ frame.closedPolygon
    intro hmem
    rw [frame.mem_closedPolygon_iff] at hmem
    rcases hmem with ⟨-, -, -, hs0, -⟩ | ⟨hne, -⟩
    · rw [hsn] at hs0
      omega
    · exact hne (by unfold EvenSite; dsimp only; omega)
  · unfold ChildFrame.vSpectrum
    rw [hs]
    exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩

/-- The parent vertex `v_l = (−b'_l, 2l − 1 − b'_l)`, `b'_l = ⌊(D − N) l / D⌋`, for `1 ≤ l < D` lies in `freeV`: the
child and parent floors agree (`vBlock_floor_agree`). -/
theorem parent_block_mem_freeV (l : ℤ) (hl1 : 1 ≤ l) (hl2 : l < frame.parents.odd.den) :
    (-((frame.parents.odd.den - frame.parents.odd.num) * l / frame.parents.odd.den),
      2 * l - 1 - (frame.parents.odd.den - frame.parents.odd.num) * l / frame.parents.odd.den) ∈ frame.freeV := by
  have hf := vBlock_floor_agree frame l hl1 hl2
  have hm := frame.block_mem_freeV l hl1 (by omega)
  rw [hf] at hm
  exact hm

/-- `V_p + I = (N − D + 1, D + N − 1)` is not in `freeV` when `ε = +1`: its left neighbour `(N − D, D + N − 1)` is in `E`
(odd branch, with `s = 2 − d + n` and `t ∈ [n − T, d]`). -/
theorem VpI_not_freeV (h : frame.eps = 1) :
    (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1) ∉
      frame.freeV := by
  obtain ⟨hd, hn, hD, hN0, hND, hq, hn0, hnq, hpar⟩ := frame.linear_facts
  have hnl : frame.child.num < frame.child.den := by omega
  have hnn : 0 ≤ frame.child.num := by omega
  have hdD : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
  have hCT := periodDen_sub_parentC_nonneg _ _ _ _ hN0 hND.le hnn hnl hdD
  have hT0 := frame.periodDen_nonneg
  have hsn : frame.sGrade (frame.parents.odd.num - frame.parents.odd.den + 1 - 1,
      frame.parents.odd.den + frame.parents.odd.num - 1) = 2 * frame.eps - frame.child.den + frame.child.num := by
    rw [frame.eps_eq]
    unfold ChildFrame.sGrade
    dsimp only
    ring
  rw [h] at hsn
  intro hv
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hv
  obtain ⟨-, hout, -⟩ := hv
  apply hout
  show (frame.parents.odd.num - frame.parents.odd.den + 1 - 1,
    frame.parents.odd.den + frame.parents.odd.num - 1) ∈ frame.closedPolygon
  rw [frame.mem_closedPolygon_iff]
  right
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold EvenSite
    dsimp only
    omega
  · unfold ChildFrame.tGrade Fraction.periodDenominator
    dsimp only
    nlinarith [hCT]
  · unfold ChildFrame.tGrade
    dsimp only
    nlinarith [mul_nonneg hn0 (show (0 : ℤ) ≤ frame.parents.odd.den - frame.parents.odd.num by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega)
        (show (0 : ℤ) ≤ frame.parents.odd.den + frame.parents.odd.num by omega)]
  · rw [hsn]
    omega
  · rw [hsn]
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

end ChildFrame

end FLatticePaper.Induction
