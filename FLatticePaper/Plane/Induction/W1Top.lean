import FLatticePaper.Plane.Induction.W1Window
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.Q3Paragraph8

/-! Task 49, W1 §2 (top collar): the bounds of the parent query `x = y − εU − (1 − W)(d_q, n_q)` in the parent strips.

`parentTGrade_query` gives `t_p(x) = t_p(y) − W`. The `y`-ranges are the top-collar ranges of W1_CONSTRUCTOR.md §2 ("Top"),
named here as hypotheses: even `y`: `L − 2 < t(y) ≤ 2L − 2`, `2n < s(y) < T`; odd `y`: `d < t(y) ≤ n + 2d − 2`,
`L − 2 < s(y) < T + 2 − d + n`. The parent identities `T·t_p(y) = C t + ε s` (`parent_transform_t`) are exact.

* Odd `y`: `1 − D ≤ t_p(x) ≤ N + 2D − 1`, the ORDINARY odd-parent zero strip. `StrongEstimates.zeroStripInterval` of the
  conjugate word gives `quarterTurnField (standardField (conjWord w)) x = 0` with no further input (`top_odd_query_zero`).
* Even `y`: `1 − (D+N) ≤ t_p(x) ≤ 2(D+N) − 1`, the STRENGTHENED even-parent window. Its vanishing is the named input `hWin`
  (W1_CONSTRUCTOR.md §1: the even window is the conjugate's opposite strip with parity tracked). -/

namespace FLatticePaper.W1Top

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Window FLatticePaper.W1Strips

/-- The parent query of the top collar, `x = y − εU − (1 − W)(d_q, n_q)`. -/
def queryX (frame : ChildFrame) (y : Site) : Site :=
  y - frame.eps • frame.child.modifiedDeck.kernel -
    (1 - frame.phaseW) • (frame.parents.even.den, frame.parents.even.num)

theorem parentTGrade_queryX (frame : ChildFrame) (y : Site) :
    frame.parentTGrade (queryX frame y) = frame.parentTGrade y - frame.phaseW :=
  parentTGrade_query frame y

/-- The integer core of the odd top collar: `1 − D ≤ t_p − W ≤ N + 2D − 1`. -/
theorem odd_core {n d D N ε W C t s T tp : ℤ}
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hD : 1 ≤ D) (hN : 0 ≤ N)
    (hε : (ε = 1 ∧ W = 1) ∨ (ε = -1 ∧ W = 0))
    (hC : C = D * (d + n) + N * (d - n))
    (hCL : C * (d + n) = (D + N) * T - 2 * ε * n)
    (hCd : C * d = D * T + ε * (d - n))
    (hT : 0 < T) (htp : T * tp = C * t + ε * s)
    (ht1 : d < t) (ht2 : t ≤ n + 2 * d - 2) (hs1 : d + n - 2 < s) (hs2 : s < T + 2 - d + n) :
    1 - D ≤ tp - W ∧ tp - W ≤ N + 2 * D - 1 := by
  have hC0 : 0 ≤ C := by rw [hC]; nlinarith
  have hCge : d + n ≤ C := by rw [hC]; nlinarith
  have hDT : 0 ≤ (D - 1) * T := mul_nonneg (by linarith) hT.le
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hl : C * (d + 1) ≤ C * t := mul_le_mul_of_nonneg_left (by omega) hC0
    have hu : C * t ≤ C * (n + 2 * d - 2) := mul_le_mul_of_nonneg_left ht2 hC0
    constructor
    · have hk : T * (2 - D) ≤ T * tp := by rw [htp]; nlinarith
      have := le_of_mul_le_mul_left hk hT
      linarith
    · have hk : T * tp < T * (N + 2 * D + 1) := by rw [htp]; nlinarith
      have := lt_of_mul_lt_mul_left hk hT.le
      omega
  · have hl : C * (d + 1) ≤ C * t := mul_le_mul_of_nonneg_left (by omega) hC0
    have hu : C * t ≤ C * (n + 2 * d - 2) := mul_le_mul_of_nonneg_left ht2 hC0
    constructor
    · have hk : T * (1 - D) ≤ T * tp := by rw [htp]; nlinarith
      have := le_of_mul_le_mul_left hk hT
      linarith
    · have hk : T * tp < T * (N + 2 * D) := by rw [htp]; nlinarith
      have := lt_of_mul_lt_mul_left hk hT.le
      omega

/-- The integer core of the even top collar: `1 − (D+N) ≤ t_p − W ≤ 2(D+N) − 1`. -/
theorem even_core {n d D N ε W C t s T tp : ℤ}
    (hn3 : 3 ≤ n) (hnd : n + 2 ≤ d) (hD : 1 ≤ D) (hN : 0 ≤ N)
    (hε : (ε = 1 ∧ W = 1) ∨ (ε = -1 ∧ W = 0))
    (heps : N * d - D * n = ε)
    (hC : C = D * (d + n) + N * (d - n))
    (hCL : C * (d + n) = (D + N) * T - 2 * ε * n)
    (hT : 0 < T) (htp : T * tp = C * t + ε * s)
    (ht1 : d + n - 2 < t) (ht2 : t ≤ 2 * (d + n) - 2) (hs1 : 2 * n < s) (hs2 : s < T) :
    1 - (D + N) ≤ tp - W ∧ tp - W ≤ 2 * (D + N) - 1 := by
  have hC0 : 0 ≤ C := by rw [hC]; nlinarith
  have hCge : d + n ≤ C := by rw [hC]; nlinarith
  have hCle : C ≤ C * (d + n) := by nlinarith
  have hl : C * (d + n - 1) ≤ C * t := mul_le_mul_of_nonneg_left (by omega) hC0
  have hu : C * t ≤ C * (2 * (d + n) - 2) := mul_le_mul_of_nonneg_left ht2 hC0
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hN1 : 1 ≤ N := by
      by_contra h
      have h0 : N ≤ 0 := by omega
      nlinarith [mul_nonneg (show (0:ℤ) ≤ -N by omega) (show (0:ℤ) ≤ d by omega),
        mul_nonneg (show (0:ℤ) ≤ D - 1 by omega) (show (0:ℤ) ≤ n by omega)]
    have hDN : 0 ≤ (D + N - 2) * T := mul_nonneg (by omega) hT.le
    constructor
    · have hk : T * (2 - D - N) ≤ T * tp := by rw [htp]; nlinarith
      have := le_of_mul_le_mul_left hk hT
      linarith
    · have hk : T * tp < T * (2 * (D + N) + 1) := by rw [htp]; nlinarith
      have := lt_of_mul_lt_mul_left hk hT.le
      omega
  · have hDN2 : 2 ≤ D + N := by
      by_contra h
      have h1 : D = 1 := by omega
      have h2 : N = 0 := by omega
      subst h1 h2
      omega
    have hDN : 0 ≤ (D + N - 2) * T := mul_nonneg (by omega) hT.le
    constructor
    · have hk : T * (1 - D - N) ≤ T * tp := by rw [htp]; nlinarith
      have := le_of_mul_le_mul_left hk hT
      linarith
    · have hk : T * tp < T * (2 * (D + N)) := by rw [htp]; nlinarith
      have := lt_of_mul_lt_mul_left hk hT.le
      omega

/-- The coordinate sum of the parent query, in each sign case. -/
theorem queryX_sum_pos (frame : ChildFrame) (y : Site) (h1 : frame.eps = 1) (h2 : frame.phaseW = 1) :
    (queryX frame y).1 + (queryX frame y).2 = (y.1 + y.2) - (frame.child.den + frame.child.num) := by
  unfold queryX
  rw [frame.child_modifiedDeck_kernel, h1, h2]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
  ring

theorem queryX_sum_neg (frame : ChildFrame) (y : Site) (h1 : frame.eps = -1) (h2 : frame.phaseW = 0) :
    (queryX frame y).1 + (queryX frame y).2 =
      (y.1 + y.2) + (frame.child.den + frame.child.num) -
        (frame.parents.even.den + frame.parents.even.num) := by
  unfold queryX
  rw [frame.child_modifiedDeck_kernel, h1, h2]
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
  ring

/-- The parent query keeps the parity of `y`. -/
theorem queryX_evenSite_iff (frame : ChildFrame) (y : Site) : EvenSite (queryX frame y) ↔ EvenSite y := by
  have hL : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hden := ZoneI1.child_den_eq frame
  have hnum := ZoneI1.child_num_eq frame
  have hQ : (frame.parents.even.den + frame.parents.even.num) % 2 = 0 := by omega
  unfold EvenSite
  rcases frame.eps_unit with h | h
  · have hW : frame.phaseW = 1 := by unfold ChildFrame.phaseW; rw [h]; norm_num
    have hx := queryX_sum_pos frame y h hW
    omega
  · have hW : frame.phaseW = 0 := by unfold ChildFrame.phaseW; rw [h]; norm_num
    have hx := queryX_sum_neg frame y h hW
    omega

/-- **The top collar, odd parity: the parent query lies in the ordinary zero strip** (the bounds `1 − D ≤ t_p(x) ≤ N + 2D − 1`). -/
theorem top_odd_window (frame : ChildFrame) (y : Site)
    (ht1 : frame.child.den < w1t frame.child.num frame.child.den y)
    (ht2 : w1t frame.child.num frame.child.den y ≤ frame.child.num + 2 * frame.child.den - 2)
    (hs1 : frame.child.den + frame.child.num - 2 < w1s frame.child.num frame.child.den y)
    (hs2 : w1s frame.child.num frame.child.den y <
      w1T frame.child.num frame.child.den + 2 - frame.child.den + frame.child.num) :
    1 - frame.parents.odd.den ≤ frame.parentTGrade (queryX frame y) ∧
      frame.parentTGrade (queryX frame y) ≤ frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
  obtain ⟨hpos, hnlt, hdn, -, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := by
    have heps := frame.eps_eq
    rcases frame.eps_unit with h | h
    · by_contra hneg
      have h0 : frame.parents.odd.num ≤ -1 := by omega
      nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - frame.parents.odd.num by omega) (show (0:ℤ) ≤ frame.child.den by omega),
        mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) (show (0:ℤ) ≤ frame.child.num by omega)]
    · by_contra hneg
      have h0 : frame.parents.odd.num ≤ -1 := by omega
      nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - frame.parents.odd.num by omega) (show (0:ℤ) ≤ frame.child.den by omega),
        mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) (show (0:ℤ) ≤ frame.child.num by omega)]
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hpt := parent_transform_t frame y
  have hCL := frame.parentC_mul_L
  have hCd := frame.parentC_mul_den
  rw [frame_periodDenominator_eq] at hCL hCd
  have hC : frame.parentC = frame.parents.odd.den * (frame.child.den + frame.child.num) +
      frame.parents.odd.num * (frame.child.den - frame.child.num) := rfl
  have hq := parentTGrade_queryX frame y
  have hε : (frame.eps = 1 ∧ frame.phaseW = 1) ∨ (frame.eps = -1 ∧ frame.phaseW = 0) := by
    rcases frame.eps_unit with h | h
    · left; refine ⟨h, ?_⟩; unfold ChildFrame.phaseW; rw [h]; norm_num
    · right; refine ⟨h, ?_⟩; unfold ChildFrame.phaseW; rw [h]; norm_num
  obtain ⟨b1, b2⟩ := odd_core (n := frame.child.num) (d := frame.child.den) (D := frame.parents.odd.den)
    (N := frame.parents.odd.num) (ε := frame.eps) (W := frame.phaseW) (C := frame.parentC)
    (t := w1t frame.child.num frame.child.den y) (s := w1s frame.child.num frame.child.den y)
    (T := w1T frame.child.num frame.child.den) (tp := frame.parentTGrade y)
    (by omega) (by omega) hD hN hε hC (by linear_combination hCL) (by linear_combination hCd) hT hpt
    ht1 ht2 hs1 hs2
  rw [hq]
  exact ⟨b1, b2⟩

/-- **The top collar, even parity: the parent query lies in the strengthened even window** `1 − (D+N) ≤ t_p(x) ≤ 2(D+N) − 1`. -/
theorem top_even_window (frame : ChildFrame) (y : Site) (hn3 : 3 ≤ frame.child.num)
    (ht1 : frame.child.den + frame.child.num - 2 < w1t frame.child.num frame.child.den y)
    (ht2 : w1t frame.child.num frame.child.den y ≤ 2 * (frame.child.den + frame.child.num) - 2)
    (hs1 : 2 * frame.child.num < w1s frame.child.num frame.child.den y)
    (hs2 : w1s frame.child.num frame.child.den y < w1T frame.child.num frame.child.den) :
    1 - (frame.parents.odd.den + frame.parents.odd.num) ≤ frame.parentTGrade (queryX frame y) ∧
      frame.parentTGrade (queryX frame y) ≤ 2 * (frame.parents.odd.den + frame.parents.odd.num) - 1 := by
  obtain ⟨hpos, hnlt, hdn, -, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := by
    have heps := frame.eps_eq
    rcases frame.eps_unit with h | h
    · by_contra hneg
      have h0 : frame.parents.odd.num ≤ -1 := by omega
      nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - frame.parents.odd.num by omega) (show (0:ℤ) ≤ frame.child.den by omega),
        mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) (show (0:ℤ) ≤ frame.child.num by omega)]
    · by_contra hneg
      have h0 : frame.parents.odd.num ≤ -1 := by omega
      nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - frame.parents.odd.num by omega) (show (0:ℤ) ≤ frame.child.den by omega),
        mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) (show (0:ℤ) ≤ frame.child.num by omega)]
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hpt := parent_transform_t frame y
  have hCL := frame.parentC_mul_L
  rw [frame_periodDenominator_eq] at hCL
  have hC : frame.parentC = frame.parents.odd.den * (frame.child.den + frame.child.num) +
      frame.parents.odd.num * (frame.child.den - frame.child.num) := rfl
  have hq := parentTGrade_queryX frame y
  have hε : (frame.eps = 1 ∧ frame.phaseW = 1) ∨ (frame.eps = -1 ∧ frame.phaseW = 0) := by
    rcases frame.eps_unit with h | h
    · left; refine ⟨h, ?_⟩; unfold ChildFrame.phaseW; rw [h]; norm_num
    · right; refine ⟨h, ?_⟩; unfold ChildFrame.phaseW; rw [h]; norm_num
  obtain ⟨b1, b2⟩ := even_core (n := frame.child.num) (d := frame.child.den) (D := frame.parents.odd.den)
    (N := frame.parents.odd.num) (ε := frame.eps) (W := frame.phaseW) (C := frame.parentC)
    (t := w1t frame.child.num frame.child.den y) (s := w1s frame.child.num frame.child.den y)
    (T := w1T frame.child.num frame.child.den) (tp := frame.parentTGrade y)
    hn3 (by omega) hD hN hε frame.eps_eq.symm hC (by linear_combination hCL) hT hpt ht1 ht2 hs1 hs2
  rw [hq]
  exact ⟨b1, b2⟩

/-- **Top collar, odd parity, zero of the conjugate's quarter-turn**: the strip of `StrongEstimates` gives the vanishing. -/
theorem top_odd_query_zero {w : Word} (hw : ∃ x ∈ w, x ≠ Digit.three) (h : StrongEstimates (conjWord w))
    (y : Site)
    (ht1 : (frameAt w).child.den < w1t (frameAt w).child.num (frameAt w).child.den y)
    (ht2 : w1t (frameAt w).child.num (frameAt w).child.den y ≤ (frameAt w).child.num + 2 * (frameAt w).child.den - 2)
    (hs1 : (frameAt w).child.den + (frameAt w).child.num - 2 < w1s (frameAt w).child.num (frameAt w).child.den y)
    (hs2 : w1s (frameAt w).child.num (frameAt w).child.den y <
      w1T (frameAt w).child.num (frameAt w).child.den + 2 - (frameAt w).child.den + (frameAt w).child.num) :
    quarterTurnField (standardField (conjWord w)) (queryX (frameAt w) y) = 0 := by
  obtain ⟨b1, b2⟩ := top_odd_window (frameAt w) y ht1 ht2 hs1 hs2
  refine h.zeroStripInterval (queryX (frameAt w) y) ?_ ?_
  · rw [parentN_conjWord hw, parentD_conjWord hw]; exact b1
  · rw [parentN_conjWord hw, parentD_conjWord hw]; exact b2

/-- **Top collar, even parity, zero from the strengthened even window** (the named input `hWin`, W1_CONSTRUCTOR.md §1). -/
theorem top_even_query_zero {w : Word}
    (hWin : ∀ x : Site, EvenSite x →
      1 - ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) ≤ (frameAt w).parentTGrade x →
      (frameAt w).parentTGrade x ≤ 2 * ((frameAt w).parents.odd.den + (frameAt w).parents.odd.num) - 1 →
      quarterTurnField (standardField (conjWord w)) x = 0)
    (y : Site) (hy : EvenSite y)
    (hn3 : 3 ≤ (frameAt w).child.num)
    (ht1 : (frameAt w).child.den + (frameAt w).child.num - 2 < w1t (frameAt w).child.num (frameAt w).child.den y)
    (ht2 : w1t (frameAt w).child.num (frameAt w).child.den y ≤ 2 * ((frameAt w).child.den + (frameAt w).child.num) - 2)
    (hs1 : 2 * (frameAt w).child.num < w1s (frameAt w).child.num (frameAt w).child.den y)
    (hs2 : w1s (frameAt w).child.num (frameAt w).child.den y < w1T (frameAt w).child.num (frameAt w).child.den) :
    quarterTurnField (standardField (conjWord w)) (queryX (frameAt w) y) = 0 := by
  obtain ⟨b1, b2⟩ := top_even_window (frameAt w) y hn3 ht1 ht2 hs1 hs2
  exact hWin _ ((queryX_evenSite_iff (frameAt w) y).2 hy) b1 b2

/-- **The two odd seeds are one input.** Under the I-reflection (`hIsym`, `sGrade_iRefl`, `harmonicGrid_iRefl`), `F = h0` on the
bottom line `s = 2 − 3d + n` (`lower_odd_h0`'s `hseed`) is equivalent to `F = h0` on the top line `s = 3d + n − 2`, the upper zero
of NO_ODD_SLIP_AUDIT §3. -/
theorem seed_bottom_iff_top (frame : ChildFrame) {F : Field} (hIsym : ∀ z, F (iRefl z) = F z) (z : Site)
    (hz : ¬ EvenSite z) (hs : frame.sGrade z = 2 - 3 * frame.child.den + frame.child.num) :
    F z = harmonicGrid z ↔
      (¬ EvenSite (iRefl z) ∧ frame.sGrade (iRefl z) = 3 * frame.child.den + frame.child.num - 2 ∧
        F (iRefl z) = harmonicGrid (iRefl z)) := by
  have h1 : F (iRefl z) = F z := hIsym z
  have h2 : harmonicGrid (iRefl z) = harmonicGrid z := harmonicGrid_iRefl z
  constructor
  · intro h
    refine ⟨fun he => hz ((evenSite_iRefl z).1 he), ?_, ?_⟩
    · rw [sGrade_iRefl, hs]; ring
    · rw [h1, h2, h]
  · intro h
    rw [h1, h2] at h
    exact h.2.2

end FLatticePaper.W1Top
