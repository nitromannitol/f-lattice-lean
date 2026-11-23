import FLatticePaper.Plane.Induction.CollarTop

/-! Task 72 / Q20, the V-arc grade ranges (BOTH_FREE §3), derived from the explicit lattice parametrization.

For a child `(n, d)` with `c = d − n`, `T = d² + 2dn − n²`, `L = d + n`: a free V point `z = (x, y)` has
* even `y − x = 2l`: `A = dx + cl` (so `s = 2A`), `B = cx + 2dl` (so `t = −B`), and `T l = dB − cA`;
* odd `y − x = 2l − 1`: `A = dx + cl` (so `s = 2A − c`), `B = cx + 2dl` (so `t = d − B`), and `T l = dB − cA`.

The integer cores below prove `0 ≤ l ≤ d − 1` (even) and `1 ≤ l ≤ d − 1` (odd) from the spectrum bounds, the left-exit condition,
and integrality; the endpoints `l = 0` and `l = d − 1` (even) are `V_0` and `V_{L−1}`. The grade ranges then follow. -/

namespace FLatticePaper.ArcRanges

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.CollarTop

/-- If `D = d·k` lies strictly between `0` and `d`, then `k` is not an integer; in particular `x = 0` when `0 ≤ d x < d`. -/
theorem eq_zero_of_mul_bounds (d x A : ℤ) (hd : 0 < d) (hA : A = d * x) (h0 : 0 ≤ A) (h1 : A < d) : x = 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : d * x ≤ -d := by nlinarith
    linarith
  · exact hx
  · have : d ≤ d * x := by nlinarith
    linarith

/-- If `D = d·m` with `−d < D < d`, then `m = 0`. -/
theorem eq_zero_of_mul_lt (d m D : ℤ) (hd : 0 < d) (hD : D = d * m) (hlo : -d < D) (hhi : D < d) : m = 0 := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : d * m ≤ -d := by nlinarith
    linarith
  · exact hm
  · have : d ≤ d * m := by nlinarith
    linarith

/-- The even core: `0 ≤ l ≤ d − 1`, and `l = 0` forces `x = 0`, `l = d − 1` forces `x = 1 − c`. -/
theorem even_core (n d T x l A B : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hAx : A = d * x + (d - n) * l) (hBx : B = (d - n) * x + 2 * d * l)
    (hA0 : 0 ≤ A) (hA2 : 2 * A ≤ d + n - 2) (hB1 : 2 - (d + n) ≤ B) (hB2 : B ≤ T - 2)
    (hcase : T - 2 * n < B ∨ A ≤ n) :
    0 ≤ l ∧ l ≤ d - 1 := by
  have hdpos : 0 < d := by omega
  have hcpos : 0 < d - n := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hlB : T * l = d * B - (d - n) * A := by
    rw [hAx, hBx, hT]
    ring
  have hTL : T = d * (d + n) + (d - n) * n := by rw [hT]; ring
  constructor
  · by_contra hl
    have hl1 : l ≤ -1 := by omega
    have h1 : T * l ≤ -T := by nlinarith
    rcases hcase with h | h
    · nlinarith [mul_le_mul_of_nonneg_left (show T - 2 * n + 1 ≤ B by omega) hdpos.le,
        mul_le_mul_of_nonneg_left (show 0 ≤ A by omega) hcpos.le]
    · nlinarith [mul_le_mul_of_nonneg_left hB1 hdpos.le, mul_le_mul_of_nonneg_left (show A ≤ n by omega) hcpos.le]
  · by_contra hl
    have hl1 : d ≤ l := by omega
    have h1 : d * T ≤ T * l := by nlinarith
    nlinarith [mul_nonneg hcpos.le hA0]

/-- The odd core: `1 ≤ l ≤ d − 1`, with `A = dx + cl ∈ [1, d − 1]`; `l = d − 1` forces `A = n`. -/
theorem odd_core (n d T x l A B : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hAx : A = d * x + (d - n) * l) (hBx : B = (d - n) * x + 2 * d * l)
    (hA1 : 1 ≤ A) (hA2 : A ≤ d - 1) (hB0 : 0 ≤ B) (hB2 : B ≤ T + d - n) :
    1 ≤ l ∧ l ≤ d - 1 := by
  have hdpos : 0 < d := by omega
  have hcpos : 0 < d - n := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hlB : T * l = d * B - (d - n) * A := by
    rw [hAx, hBx, hT]
    ring
  have hTL : T = d * (d + n) + (d - n) * n := by rw [hT]; ring
  have hTc : (d - n) * d < T := by nlinarith
  -- A = d·k with 1 ≤ A ≤ d − 1 is impossible
  have hAk : ∀ k : ℤ, A = d * k → 1 ≤ A → A ≤ d - 1 → False := by
    intro k hk h1 h2
    rcases le_or_gt k 0 with hk0 | hk0
    · nlinarith
    · nlinarith
  constructor
  · by_contra hl
    rcases (show l = 0 ∨ l < 0 by omega) with h0 | hneg
    · exact hAk x (by rw [hAx, h0]; ring) hA1 hA2
    · have h1 : T * l ≤ -T := by nlinarith
      nlinarith [mul_nonneg hdpos.le hB0, mul_le_mul_of_nonneg_left hA2 hcpos.le]
  · by_contra hl
    rcases (show l = d ∨ d < l by omega) with h | hgt
    · exact hAk (x + (d - n)) (by rw [hAx, h]; ring) hA1 hA2
    · have h1 : T * (d + 1) ≤ T * l := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hB2 hdpos.le, mul_nonneg hcpos.le (show (0:ℤ) ≤ A by omega)]

/-- **Even arc range.** For `1 ≤ l ≤ d − 2` (a non-endpoint even point), `−T + 2L ≤ −B ≤ −L`, i.e. the grade `t = −B`. -/
theorem even_range_core (n d T x l A B : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hAx : A = d * x + (d - n) * l) (hBx : B = (d - n) * x + 2 * d * l)
    (hA0 : 0 ≤ A) (hA2 : 2 * A ≤ d + n - 2) (_hB1 : 2 - (d + n) ≤ B) (hB2 : B ≤ T - 2)
    (hcase : T - 2 * n < B ∨ A ≤ n) (hl1 : 1 ≤ l) (hl2 : l ≤ d - 2) :
    -(d ^ 2 + 2 * d * n - n ^ 2) + 2 * (d + n) ≤ -B ∧ -B ≤ -(d + n) := by
  have hdpos : 0 < d := by omega
  have hcpos : 0 < d - n := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hlB : T * l = d * B - (d - n) * A := by
    rw [hAx, hBx, hT]
    ring
  have hTL : T = d * (d + n) + (d - n) * n := by rw [hT]; ring
  have hdB : d * B = T * l + (d - n) * A := by linarith
  have hA_n : A ≤ n := by
    rcases hcase with h | h
    · -- the case `B > T − 2n` contradicts the upper `l`
      exfalso
      nlinarith [mul_le_mul_of_nonneg_left (show T - 2 * n + 1 ≤ B by omega) hdpos.le,
        mul_le_mul_of_nonneg_left (show T * l ≤ T * (d - 2) by nlinarith) (le_refl (0:ℤ)),
        mul_le_mul_of_nonneg_left hl2 hT0.le, mul_le_mul_of_nonneg_left hA2 hcpos.le]
    · exact h
  constructor
  · have hup : d * B ≤ d * (T - 2 * (d + n)) := by
      nlinarith [mul_le_mul_of_nonneg_left hl2 hT0.le, mul_le_mul_of_nonneg_left hA_n hcpos.le]
    have hB' : B ≤ T - 2 * (d + n) := le_of_mul_le_mul_left hup hdpos
    linarith
  · have hlo : d * (d + n) ≤ d * B := by
      nlinarith [mul_le_mul_of_nonneg_left hl1 hT0.le, mul_nonneg hcpos.le hA0]
    have hB' : d + n ≤ B := le_of_mul_le_mul_left (by linarith) hdpos
    linarith

/-- **Odd arc range.** For `1 ≤ l ≤ d − 1` (every odd point) with `A ∈ [1, d − 1]`, `t = d − B ∈ [−T + L + d, −d]`. -/
theorem odd_range_core (n d T x l A B : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2)
    (hAx : A = d * x + (d - n) * l) (hBx : B = (d - n) * x + 2 * d * l)
    (hA1 : 1 ≤ A) (hA2 : A ≤ d - 1) (hl1 : 1 ≤ l) (hl2 : l ≤ d - 1) :
    -(d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) + d) ≤ d - B ∧ d - B ≤ -d := by
  have hdpos : 0 < d := by omega
  have hcpos : 0 < d - n := by omega
  have hT0 : 0 < T := by rw [hT]; nlinarith
  have hlB : T * l = d * B - (d - n) * A := by
    rw [hAx, hBx, hT]
    ring
  have hTL : T = d * (d + n) + (d - n) * n := by rw [hT]; ring
  have hdB : d * B = T * l + (d - n) * A := by linarith
  have hcd : (d - n) * (d - 1) ≤ T := by nlinarith
  constructor
  · -- `B ≤ T − L`
    rcases (show l ≤ d - 2 ∨ l = d - 1 by omega) with h | h
    · have hup : d * B ≤ d * (T - (d + n)) := by
        nlinarith [mul_le_mul_of_nonneg_left h hT0.le, mul_le_mul_of_nonneg_left hA2 hcpos.le]
      have hB' : B ≤ T - (d + n) := le_of_mul_le_mul_left hup hdpos
      linarith
    · -- `l = d − 1` forces `A = n`
      have hk : A = n := by
        have hA' : d * (x + (d - n)) = A + (d - n) := by
          rw [hAx, h]
          ring
        have hkpos : 1 ≤ x + (d - n) := by nlinarith
        have hkle : x + (d - n) ≤ 1 := by nlinarith
        have hk1 : x + (d - n) = 1 := by omega
        rw [hk1] at hA'
        linarith
      have hBv : d * B = d * (T - (d + n)) := by
        rw [hdB, h, hk]
        nlinarith
      have hB' : B = T - (d + n) := mul_left_cancel₀ hdpos.ne' hBv
      linarith
  · -- `B ≥ 2d`
    rcases (show l = 1 ∨ 2 ≤ l by omega) with h | h
    · have hA_c : A = d - n := by
        subst h
        have hx0 : x = 0 := by
          have h1 : d * x = A - (d - n) := by rw [hAx]; ring
          rcases le_or_gt x 0 with hx | hx
          · nlinarith
          · nlinarith
        rw [hAx, hx0]
        ring
      have hBv : d * B = d * (2 * d) := by
        rw [hdB, h, hA_c]
        nlinarith
      have hB' : B = 2 * d := mul_left_cancel₀ hdpos.ne' hBv
      linarith
    · have hBL : 2 * d ≤ B := by
        have h2T : 2 * d ^ 2 ≤ T * l := by nlinarith
        have : d * (2 * d) ≤ d * B := by nlinarith [mul_nonneg hcpos.le (show (0:ℤ) ≤ A by omega)]
        exact le_of_mul_le_mul_left this hdpos
      linarith

/-- **The even V arc.** A free V point `z` of even parity other than the endpoints `V_0`, `V_{L−1}` has
`−T + 2L ≤ t z ≤ −L`. -/
theorem arc_even_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z)
    (h1 : z ≠ vFirst) (h2 : z ≠ frame.vLast) :
    -frame.child.periodDenominator + 2 * (frame.child.den + frame.child.num) ≤ frame.tGrade z ∧
      frame.tGrade z ≤ -(frame.child.den + frame.child.num) := by
  obtain ⟨hn0, hnd1, hd2, -, hT⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨x, y⟩ := z
  obtain ⟨hE0, hleft0, hvS⟩ := hz
  have hE := (mem_closedPolygon_EDisj frame (x, y)).mp hE0
  have hleft : ¬ EDisj frame.child.num frame.child.den frame.child.periodDenominator (x - 1) y :=
    fun h => hleft0 ((mem_closedPolygon_EDisj frame _).mpr h)
  rw [hT] at hE hleft
  have he' : (x + y) % 2 = 0 := he
  obtain ⟨l, rfl⟩ : ∃ l, y = x + 2 * l := ⟨(y - x) / 2, by omega⟩
  unfold ChildFrame.vSpectrum at hvS
  obtain ⟨-, hvb⟩ := hvS
  simp only [ChildFrame.sGrade] at hvb
  unfold EDisj at hE
  rcases hE with ⟨-, e1, e2, e3, e4⟩ | ⟨hodd, -⟩
  swap
  · exact absurd he' (by omega)
  simp only [ChildFrame.tGrade]
  rw [hT]
  set n := frame.child.num with hn
  set d := frame.child.den with hd
  set T := frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 with hTdef
  obtain ⟨A, hA⟩ : ∃ A, A = d * x + (d - n) * l := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (d - n) * x + 2 * d * l := ⟨_, rfl⟩
  have htB : n * x - d * (x + 2 * l) = -B := by rw [hB]; ring
  have hsA : (d + n) * x + (d - n) * (x + 2 * l) = 2 * A := by rw [hA]; ring
  have hA0 : 0 ≤ A := by linarith
  have hA2 : 2 * A ≤ d + n - 2 := by
    rcases hvb with ⟨-, h⟩ | ⟨-, h⟩ <;> nlinarith [h]
  have hB1 : 2 - (d + n) ≤ B := by linarith
  have hB2 : B ≤ T - 2 := by linarith
  have hcase : T - 2 * n < B ∨ A ≤ n := by
    by_contra hcon
    rw [not_or, not_lt, not_le] at hcon
    apply hleft
    right
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · have : n * (x - 1) - d * (x + 2 * l) = -B - n := by rw [hB]; ring
      linarith
    · have : n * (x - 1) - d * (x + 2 * l) = -B - n := by rw [hB]; ring
      linarith
    · have : (d + n) * (x - 1) + (d - n) * (x + 2 * l) = 2 * A - (d + n) := by rw [hA]; ring
      linarith
    · have : (d + n) * (x - 1) + (d - n) * (x + 2 * l) = 2 * A - (d + n) := by rw [hA]; ring
      linarith
  have hcpos : 0 < d - n := by omega
  obtain ⟨hl0, hl1⟩ := even_core n d T x l A B (by omega) hnd (by rw [hTdef]) hA hB hA0 hA2 hB1 hB2 hcase
  rcases (show l = 0 ∨ l = d - 1 ∨ (1 ≤ l ∧ l ≤ d - 2) by omega) with h0 | hd1 | hmid
  · -- `l = 0`: `A = dx`, `0 ≤ A ≤ (L − 2)/2 < d`, so `x = 0` and `z = V_0`
    exfalso
    apply h1
    have hA' : A = d * x := by rw [hA, h0]; ring
    have hAlt : A < d := by omega
    have hx0 : x = 0 := eq_zero_of_mul_bounds d x A (by omega) hA' hA0 hAlt
    show (x, x + 2 * l) = vFirst
    simp [vFirst, hx0, h0]
  · -- `l = d − 1`: `d(x + c − 1) = A + c − d ∈ (−d, d)`, so `x = 1 − c` and `z = V_{L−1}`
    exfalso
    apply h2
    have hm : d * (x + (d - n) - 1) = A + (d - n) - d := by
      rw [hA, hd1]
      ring
    have hm0 : x + (d - n) - 1 = 0 := by
      refine eq_zero_of_mul_lt d _ _ (by omega) hm.symm ?_ ?_
      · rw [hd1] at hA
        omega
      · omega
    show (x, x + 2 * l) = frame.vLast
    simp only [ChildFrame.vLast, Prod.mk.injEq]
    constructor
    · omega
    · rw [hd1]
      omega
  · rw [htB]
    exact even_range_core n d T x l A B (by omega) hnd (by rw [hTdef]) hA hB hA0 hA2 hB1 hB2 hcase hmid.1 hmid.2

/-- **The odd V arc.** A free V point of odd parity has `−T + (L + d) ≤ t z ≤ −d`. -/
theorem arc_odd_range (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (ho : ¬ EvenSite z) :
    -frame.child.periodDenominator + (frame.child.den + frame.child.num + frame.child.den) ≤ frame.tGrade z ∧
      frame.tGrade z ≤ -frame.child.den := by
  obtain ⟨hn0, hnd1, hd2, -, hT⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨x, y⟩ := z
  obtain ⟨hE0, hleft0, hvS⟩ := hz
  have hE := (mem_closedPolygon_EDisj frame (x, y)).mp hE0
  rw [hT] at hE
  have ho' : ¬ (x + y) % 2 = 0 := ho
  obtain ⟨l, rfl⟩ : ∃ l, y = x + 2 * l - 1 := ⟨(y - x + 1) / 2, by omega⟩
  unfold ChildFrame.vSpectrum at hvS
  obtain ⟨-, hvb⟩ := hvS
  simp only [ChildFrame.sGrade] at hvb
  unfold EDisj at hE
  rcases hE with ⟨hev, -⟩ | ⟨-, e1, e2, e3, e4⟩
  · exfalso
    omega
  simp only [ChildFrame.tGrade]
  set n := frame.child.num with hn
  set d := frame.child.den with hd
  set T := frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 with hTdef
  obtain ⟨A, hA⟩ : ∃ A, A = d * x + (d - n) * l := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (d - n) * x + 2 * d * l := ⟨_, rfl⟩
  have htB : n * x - d * (x + 2 * l - 1) = d - B := by rw [hB]; ring
  have hsA : (d + n) * x + (d - n) * (x + 2 * l - 1) = 2 * A - (d - n) := by rw [hA]; ring
  rw [hsA] at e3 e4 hvb
  rw [htB] at e1 e2 ⊢
  have hA1 : 1 ≤ A := by omega
  have hA2 : A ≤ d - 1 := by
    rcases hvb with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hB0 : 0 ≤ B := by linarith
  have hB2 : B ≤ T + d - n := by linarith
  obtain ⟨hl1, hl2⟩ := odd_core n d T x l A B (by omega) hnd hTdef hA hB hA1 hA2 hB0 hB2
  exact odd_range_core n d T x l A B (by omega) hnd hTdef hA hB hA1 hA2 hl1 hl2

end FLatticePaper.ArcRanges
