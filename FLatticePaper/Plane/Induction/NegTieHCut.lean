import FLatticePaper.Plane.Induction.FreeHBox
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.Packet

/-! Task Q21 (steps 2 and 3): the conjugate H arc in the native V box, the star of the translated root, and the
offers. For a conjugate free H point `w = zTurn x + C.child.modifiedDeck.combine a b` (`C` the conjugate frame) the
reversed root is `v = x + b U_p + (1 − a) V_p` (`vStar_eq`). The child box of `C` (`conj_freeH_box`) puts `v` in the
t-grade window `N + D − B ≤ t_p(v) ≤ 0`; a unit neighbour moves `t_p` by at most `D`, so the star lies in
`[N − B, D]`, where the native V box offers are `{0, 1}` (`V_box_a_zero_or_one`). With the drop `a(x) = 1`,
`a(y) = 0` this forces `a = 1` (`H_cut_a_eq_one`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The conjugate free H arc lies in the child box of the conjugate frame: `1 ≤ w₁ ≤ D + N`, `0 ≤ w₂ ≤ D − N − 1`. -/
theorem conj_freeH_box {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt (conjWord word)).freeH) :
    1 ≤ w.1 ∧ w.1 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num ∧
      0 ≤ w.2 ∧ w.2 ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hw
  obtain ⟨hz, -, hsp⟩ := hw
  have hb := (frameAt (conjWord word)).freeH_child_box hz hsp
  rw [hn, hd] at hb
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

/-- The conjugate modified deck: `U_c = (D + N, D − N)`, `V_c = (−2N, 2D)`, so `combine a b = (a (D+N) − 2 N b, a (D−N) + 2 D b)`. -/
theorem conj_combine_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (a b : ℤ) :
    (frameAt (conjWord word)).child.modifiedDeck.combine a b =
      (a * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
          b * (-2 * (frameAt word).parents.odd.num),
        a * ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          b * (2 * (frameAt word).parents.odd.den)) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  have hmu : (frameAt (conjWord word)).child.periodMultiplicity = 1 := by
    unfold Fraction.periodMultiplicity
    rw [if_pos (by rw [hn, hd]; omega)]
  have hK : (frameAt (conjWord word)).child.modifiedDeck.kernel =
      ((frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num) := by
    simp only [Fraction.modifiedDeck, hmu, one_mul]
  have hT : (frameAt (conjWord word)).child.modifiedDeck.transverse =
      ((frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.den,
        (frameAt (conjWord word)).child.num + (frameAt (conjWord word)).child.den) := by
    simp only [Fraction.modifiedDeck, Fraction.unmodifiedDeck]
  unfold PeriodDeck.combine
  rw [hK, hT, hn, hd]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

/-- The reversed root: for `w = zTurn x + combine a b`, `(N − D + 1 + w₂, N + D − w₁) = x + b U_p + (1 − a) V_p`. -/
theorem vStar_eq {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : Site) (a b : ℤ) :
    ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 +
        (zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine a b).2,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den -
        (zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine a b).1) =
      x + (b * (2 * (frameAt word).parents.odd.den) +
          (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
        b * (2 * (frameAt word).parents.odd.num) +
          (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) := by
  rw [conj_combine_eq h]
  ext <;> simp [zTurn] <;> ring

/-- Integer window of the reversed root: `1 ≤ w₁ ≤ D + N`, `0 ≤ w₂ ≤ D − N − 1` give
`N + D − B ≤ N (N − D + 1 + w₂) − D (N + D − w₁) ≤ 0`, with `B = D² + 2DN − N²`. -/
theorem H_cut_window_int (N D w1 w2 : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (h1 : 1 ≤ w1) (h1' : w1 ≤ D + N)
    (h2 : 0 ≤ w2) (h2' : w2 ≤ D - N - 1) :
    N + D - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * (N - D + 1 + w2) - D * (N + D - w1) ∧
      N * (N - D + 1 + w2) - D * (N + D - w1) ≤ 0 := by
  have hD : (0 : ℤ) ≤ D := by omega
  have hN0 : (0 : ℤ) ≤ N := by omega
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hD, mul_le_mul_of_nonneg_left h2 hN0]
  · nlinarith [mul_le_mul_of_nonneg_left h1' hD, mul_le_mul_of_nonneg_left h2' hN0]

/-- A unit neighbour moves the parent t-grade by at most `D`. -/
theorem parentTGrade_neighbour_bound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x y : Site)
    (hyx : y = incomingNeg x ∨ y = incomingPos x) :
    -(frameAt word).parents.odd.den ≤ (frameAt word).parentTGrade y - (frameAt word).parentTGrade x ∧
      (frameAt word).parentTGrade y - (frameAt word).parentTGrade x ≤ (frameAt word).parents.odd.den := by
  have hN := frameAt_odd_num_pos h
  obtain ⟨hD, hN0, hND⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND' : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  unfold ChildFrame.parentTGrade
  unfold incomingNeg incomingPos at hyx
  by_cases he : EvenSite x
  · simp only [if_pos he] at hyx
    rcases hyx with rfl | rfl
    · constructor <;> (try dsimp only) <;> nlinarith
    · constructor <;> (try dsimp only) <;> nlinarith
  · simp only [if_neg he] at hyx
    rcases hyx with rfl | rfl
    · constructor <;> (try dsimp only) <;> nlinarith
    · constructor <;> (try dsimp only) <;> nlinarith

/-- The offer on the star at a unit neighbour of a root whose translate has `t_p` in `[N + D − B, 0]`: it is `0` or `1`,
by the native V box (`V_box_a_zero_or_one`). The star point is `y + b U_p + (1 − a) V_p`. -/
theorem H_cut_star_zero_or_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x y : Site) (a b : ℤ)
    (hyx : y = incomingNeg x ∨ y = incomingPos x)
    (hwin : (frameAt word).parents.odd.num + (frameAt word).parents.odd.den -
          ((frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
            (frameAt word).parents.odd.num ^ 2) ≤
        (frameAt word).parentTGrade (x + (b * (2 * (frameAt word).parents.odd.den) +
          (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          b * (2 * (frameAt word).parents.odd.num) +
            (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) ∧
      (frameAt word).parentTGrade (x + (b * (2 * (frameAt word).parents.odd.den) +
          (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          b * (2 * (frameAt word).parents.odd.num) +
            (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) ≤ 0) :
    aVal (frameAt word) (standardField (conjWord word))
        (y + (b * (2 * (frameAt word).parents.odd.den) +
          (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          b * (2 * (frameAt word).parents.odd.num) +
            (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) = 0 ∨
      aVal (frameAt word) (standardField (conjWord word))
        (y + (b * (2 * (frameAt word).parents.odd.den) +
          (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
          b * (2 * (frameAt word).parents.odd.num) +
            (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den))) = 1 := by
  set t : Site := (b * (2 * (frameAt word).parents.odd.den) +
      (1 - a) * ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den),
    b * (2 * (frameAt word).parents.odd.num) +
      (1 - a) * ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den)) with ht
  have hnb := parentTGrade_neighbour_bound h x y hyx
  have hsum : (frameAt word).parentTGrade (y + t) =
      (frameAt word).parentTGrade (x + t) + ((frameAt word).parentTGrade y - (frameAt word).parentTGrade x) := by
    rw [ht]
    unfold ChildFrame.parentTGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  apply V_box_a_zero_or_one h hSE (y + t)
  · rw [hsum]
    nlinarith [hwin.1, hwin.2, hnb.1, hnb.2]
  · rw [hsum]
    nlinarith [hwin.1, hwin.2, hnb.1, hnb.2]

/-- **The drop forces `a = 1`.** For the conjugate free H point `w = zTurn x + combine a b`, the root offer `a(x) = 1` and
the neighbour offer `a(y) = 0` both sit on the star of the reversed root, whose offers are `{0, 1}`; the translates
`x + t` and `y + t` have offers `1 + (1 − a)` and `0 + (1 − a)`, so `a = 1`. -/
theorem H_cut_a_eq_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (x y : Site) (a b : ℤ)
    (hyx : y = incomingNeg x ∨ y = incomingPos x)
    (hx : aVal (frameAt word) (standardField (conjWord word)) x = 1)
    (hy : aVal (frameAt word) (standardField (conjWord word)) y = 0)
    (hf : zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine a b ∈
      (frameAt (conjWord word)).freeH) :
    a = 1 := by
  have hbox := conj_freeH_box h hf
  have hN := frameAt_odd_num_pos h
  obtain ⟨hD, hN0, hND⟩ := (frameAt word).valid.odd_bounds
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND' : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  set w : Site := zTurn x + (frameAt (conjWord word)).child.modifiedDeck.combine a b with hwdef
  set t : Site := (b * (2 * D) + (1 - a) * (N - D), b * (2 * N) + (1 - a) * (N + D)) with ht
  have hR : x + t = (N - D + 1 + w.2, N + D - w.1) := (vStar_eq h x a b).symm
  have hwinR : N + D - (D ^ 2 + 2 * D * N - N ^ 2) ≤ (frameAt word).parentTGrade (x + t) ∧
      (frameAt word).parentTGrade (x + t) ≤ 0 := by
    have hw := H_cut_window_int N D w.1 w.2 (by omega) hND' hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2
    rw [hR]
    unfold ChildFrame.parentTGrade
    dsimp only
    exact hw
  have hlo : N - (D ^ 2 + 2 * D * N - N ^ 2) ≤ (frameAt word).parentTGrade (x + t) := by
    have hD0 : (0 : ℤ) ≤ D := by omega
    linarith [hwinR.1]
  have hhi : (frameAt word).parentTGrade (x + t) ≤ D := by
    have hD0 : (0 : ℤ) ≤ D := by omega
    linarith [hwinR.2]
  have h1 : aVal (frameAt word) (standardField (conjWord word)) (x + t) = 0 ∨
      aVal (frameAt word) (standardField (conjWord word)) (x + t) = 1 :=
    V_box_a_zero_or_one h hSE (x + t) hlo hhi
  have h2 : aVal (frameAt word) (standardField (conjWord word)) (y + t) = 0 ∨
      aVal (frameAt word) (standardField (conjWord word)) (y + t) = 1 :=
    H_cut_star_zero_or_one h hSE x y a b hyx hwinR
  have e1 : aVal (frameAt word) (standardField (conjWord word)) (x + t) =
      aVal (frameAt word) (standardField (conjWord word)) x + (1 - a) :=
    aVal_translate_UV h hSE b (1 - a) x
  have e2 : aVal (frameAt word) (standardField (conjWord word)) (y + t) =
      aVal (frameAt word) (standardField (conjWord word)) y + (1 - a) :=
    aVal_translate_UV h hSE b (1 - a) y
  rw [e1, hx] at h1
  rw [e2, hy] at h2
  omega

end FLatticePaper.Induction
