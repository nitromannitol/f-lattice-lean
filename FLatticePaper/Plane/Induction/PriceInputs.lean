import FLatticePaper.Plane.Induction.EHPrice
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.W1ZeroStrip
import FLatticePaper.Plane.Induction.W1ArcBottom
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.TieReduce

/-! # Discharging the inputs of the price identities (task 118, H_PRICE)

The price identities `price_W0`, `price_W1` (EHPrice) take four inputs. Here each is proved from the trace `z ∈ freeH`:

* (i) `F z = 0`: the zero band of the packet (`packet_of_strong`), since the trace's `t` lies in `[1 − d, n + 2d − 1]`.
* (ii) `A z = 0` (`sheetA (FqW word) z = 0`): the zero band of the conjugate's packet (`zeroStrip_of_strips`), in the form
  `1 − D ≤ N x₁ − D x₂ ≤ N + 2D − 1` at `x = z − lv`. Via `T·(N p₁ − D p₂) = A t + ε s` (with `A = N(d−n) + D(d+n)`),
  this follows from the spectrum of `t`, the box of `s`, and the polynomial inequalities `P1`, `P2`.
* (iii) `F(z + V_p) = sheetMin (z + V_p)`: `z + V_p` lies in the closed polygon (`mem_tip_of`), so
  `standardField_eq_sheetMin_of_strong` applies directly.
* (iv) `F(z − V_p) = F(reflH z + V_p)` (W1): the packet's reflection about `centre` and its `V`-period, whose constants cancel
  (`cV + T + k = 0`).

Hence `price_W0'` and `price_W1'` depend only on `z ∈ freeH`. -/

namespace FLatticePaper.PriceInputs

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet
open FLatticePaper.Induction.TipVertex FLatticePaper.Induction.W0Sheets FLatticePaper.PsiCalibration
open FLatticePaper.EHPrice

/-! ### The arithmetic of the band -/

/-- `P1`: `A(L−2) + 2n ≤ T(N+2D−2)`. -/
theorem P1 (n d N D eps : ℤ) (hrel : N * d - n * D = eps) (heps : eps = 1 ∨ eps = -1)
    (_hN : 1 ≤ N) (hD : 2 ≤ D) (hn : 2 ≤ n) (hnd : n + 2 ≤ d) :
    (N * (d - n) + D * (d + n)) * ((d + n) - 2) + 2 * n ≤ (d * d + 2 * d * n - n * n) * (N + 2 * D - 2) := by
  have hX : 0 ≤ d * n + d - n := by nlinarith
  have hW : 0 ≤ 2 * n * (d * n + d - n) + d * (d * d + 2 * d * n - 3 * n * n + 2 * d + 2 * n) := by nlinarith
  have hkey : d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * ((d + n) - 2) + 2 * n))
      = D * (2 * n * (d * n + d - n) + d * (d * d + 2 * d * n - 3 * n * n + 2 * d + 2 * n))
        + 2 * eps * (d * n + d - n) + d * (-2 * (d * d + 2 * d * n - n * n) - 2 * n) := by
    linear_combination (2 * (d * n + d - n)) * hrel
  have hS : 0 ≤ 2 * (2 * n * (d * n + d - n) + d * (d * d + 2 * d * n - 3 * n * n + 2 * d + 2 * n))
      + 2 * eps * (d * n + d - n) + d * (-2 * (d * d + 2 * d * n - n * n) - 2 * n) := by
    rcases heps with h | h <;> subst h <;> nlinarith
  have hpos : 0 ≤ d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * ((d + n) - 2) + 2 * n)) := by
    rw [hkey]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ D - 2 by omega) hW]
  have hdpos : 0 < d := by omega
  have := nonneg_of_mul_nonneg_right (by linarith [hpos] : 0 ≤ (d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * ((d + n) - 2) + 2 * n)))) hdpos
  linarith

/-- `P2`: `A d + (L−2) ≤ T(N+2D−2)`. -/
theorem P2 (n d N D eps : ℤ) (hrel : N * d - n * D = eps) (heps : eps = 1 ∨ eps = -1)
    (_hN : 1 ≤ N) (hD : 2 ≤ D) (hn : 2 ≤ n) (hnd : n + 2 ≤ d) :
    (N * (d - n) + D * (d + n)) * d + ((d + n) - 2) ≤ (d * d + 2 * d * n - n * n) * (N + 2 * D - 2) := by
  have hW2 : 0 ≤ d * d * d + 3 * d * d * n + d * n * n - n * n * n := by nlinarith
  have hR : 0 ≤ 2 * (d * d * d + 3 * d * d * n + d * n * n - n * n * n) - (3 * d * n - n * n)
      - d * (2 * (d * d + 2 * d * n - n * n) + (d + n) - 2) := by nlinarith
  have hkey : d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * d + ((d + n) - 2)))
      = D * (d * d * d + 3 * d * d * n + d * n * n - n * n * n) + eps * (3 * d * n - n * n)
        - d * (2 * (d * d + 2 * d * n - n * n) + (d + n) - 2) := by
    linear_combination (3 * d * n - n * n) * hrel
  have hpos : 0 ≤ d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * d + ((d + n) - 2))) := by
    rw [hkey]
    have he : -(3 * d * n - n * n) ≤ eps * (3 * d * n - n * n) := by
      rcases heps with h | h <;> subst h <;> nlinarith
    nlinarith [mul_nonneg (show (0:ℤ) ≤ D - 2 by omega) hW2]
  have hdpos : 0 < d := by omega
  have := nonneg_of_mul_nonneg_right (by linarith [hpos] : 0 ≤ (d * ((d * d + 2 * d * n - n * n) * (N + 2 * D - 2) - ((N * (d - n) + D * (d + n)) * d + ((d + n) - 2))))) hdpos
  linarith

/-- The W1 band: `T·(N p₁ − D p₂) = A t + s`, with `t`, `s` the grades, gives `1 − D ≤ N p₁ − D p₂ ≤ N + 2D − 1`. -/
theorem band_W1 (n d N D p1 p2 t s : ℤ) (hn0 : 0 < n) (hn2 : 2 ≤ n) (hnd : n + 2 ≤ d) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hD : 2 ≤ D)
    (hrel : N * d - n * D = 1) (ht : t = n * p1 - d * p2) (hs : s = (d + n) * p1 + (d - n) * p2)
    (hspec : (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ d + n - 2) ∨ (t % 2 = 1 ∧ n ≤ t ∧ t ≤ d))
    (hsbox : d + n ≤ s ∧ s ≤ d * d + 2 * d * n - n * n - d + n) :
    1 - D ≤ N * p1 - D * p2 ∧ N * p1 - D * p2 ≤ N + 2 * D - 1 := by
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hA : 0 ≤ N * (d - n) + D * (d + n) := by nlinarith
  have hid : (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) = (N * (d - n) + D * (d + n)) * t + s := by
    rw [ht, hs]
    linear_combination ((d + n) * p1 + (d - n) * p2) * hrel
  have htlo : 0 ≤ t := by rcases hspec with ⟨-, a, -⟩ | ⟨-, a, -⟩ <;> omega
  have hlow : (d * d + 2 * d * n - n * n) * (1 - D) ≤ (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) := by
    rw [hid]
    nlinarith [mul_nonneg hA htlo]
  have hup : (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) ≤ (d * d + 2 * d * n - n * n) * (N + 2 * D - 1) := by
    rw [hid]
    rcases hspec with ⟨-, a, b⟩ | ⟨-, a, b⟩
    · have hmul := mul_le_mul_of_nonneg_left b hA
      nlinarith [P1 n d N D 1 hrel (Or.inl rfl) hN hD hn2 hnd, hsbox.2]
    · have hmul := mul_le_mul_of_nonneg_left b hA
      nlinarith [P2 n d N D 1 hrel (Or.inl rfl) hN hD hn2 hnd, hsbox.2]
  exact ⟨le_of_mul_le_mul_left hlow hT, le_of_mul_le_mul_left hup hT⟩

/-- The W0 band: `T·(N p₁ − D p₂) = A t − s`, with `N d − n D = −1`, gives `−D ≤ N p₁ − D p₂ ≤ N + 2D − 2`. -/
theorem band_W0 (n d N D p1 p2 t s : ℤ) (hn0 : 0 < n) (hn2 : 2 ≤ n) (hnd : n + 2 ≤ d) (hN : 1 ≤ N) (hND : N + 1 ≤ D) (hD : 2 ≤ D)
    (hrel : N * d - n * D = -1) (ht : t = n * p1 - d * p2) (hs : s = (d + n) * p1 + (d - n) * p2)
    (hspec : (t % 2 = 0 ∧ 2 ≤ t ∧ t ≤ d + n - 2) ∨ (t % 2 = 1 ∧ n ≤ t ∧ t ≤ d))
    (hsbox : d + n ≤ s ∧ s ≤ d * d + 2 * d * n - n * n - d + n) :
    -D ≤ N * p1 - D * p2 ∧ N * p1 - D * p2 ≤ N + 2 * D - 2 := by
  have hT : 0 < d * d + 2 * d * n - n * n := by nlinarith
  have hA : 0 ≤ N * (d - n) + D * (d + n) := by nlinarith
  have hid : (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) = (N * (d - n) + D * (d + n)) * t - s := by
    rw [ht, hs]
    linear_combination ((d + n) * p1 + (d - n) * p2) * hrel
  have htlo : 0 ≤ t := by rcases hspec with ⟨-, a, -⟩ | ⟨-, a, -⟩ <;> omega
  have hlow : (d * d + 2 * d * n - n * n) * (-D) ≤ (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) := by
    rw [hid]
    have hTD : d - n ≤ (d * d + 2 * d * n - n * n) * (D - 1) := by nlinarith
    nlinarith [mul_nonneg hA htlo]
  have hup : (d * d + 2 * d * n - n * n) * (N * p1 - D * p2) ≤ (d * d + 2 * d * n - n * n) * (N + 2 * D - 2) := by
    rw [hid]
    rcases hspec with ⟨-, a, b⟩ | ⟨-, a, b⟩
    · have hmul := mul_le_mul_of_nonneg_left b hA
      nlinarith [P1 n d N D (-1) hrel (Or.inr rfl) hN hD hn2 hnd, hsbox.1]
    · have hmul := mul_le_mul_of_nonneg_left b hA
      nlinarith [P2 n d N D (-1) hrel (Or.inr rfl) hN hD hn2 hnd, hsbox.1]
  exact ⟨le_of_mul_le_mul_left hlow hT, le_of_mul_le_mul_left hup hT⟩

/-! ### Frame-level bounds -/

/-- The `V_p`-shift of the grades: `t(V_p) = n(N−D) − d(N+D) ∈ [−T, 0]`. -/
theorem tv_bounds (n d N D nq dq : ℤ) (hN : 0 ≤ N) (hND : N < D) (hD : 2 ≤ D) (hnq : 0 ≤ nq) (hdq : 0 ≤ dq)
    (hn : n = 2 * N + nq) (hd : d = 2 * D + dq) (hn0 : 0 < n) (hnd : n + 2 ≤ d) :
    -(d * d + 2 * d * n - n * n) ≤ n * (N - D) - d * (N + D) ∧ n * (N - D) - d * (N + D) ≤ 0 := by
  have h1 : 2 * N ≤ n := by omega
  have h2 : 2 * D ≤ d := by omega
  constructor
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ n - 2 * N by omega) (show (0:ℤ) ≤ d - n by omega),
      mul_nonneg (show (0:ℤ) ≤ d - 2 * D by omega) (show (0:ℤ) ≤ d + n by omega),
      show (0:ℤ) ≤ d * d + 2 * d * n - n * n by nlinarith]
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ n by omega) (show (0:ℤ) ≤ D - N by omega),
      mul_nonneg (show (0:ℤ) ≤ d by omega) (show (0:ℤ) ≤ N + D by omega)]

/-- The box bounds of `s = L x + (d−n) y` on `1 ≤ x ≤ d`, `0 ≤ y ≤ n−1`. -/
theorem s_box (n d x y : ℤ) (hn0 : 0 < n) (hnd : n + 2 ≤ d) (hx1 : 1 ≤ x) (hxd : x ≤ d) (hy0 : 0 ≤ y)
    (hyn : y ≤ n - 1) :
    d + n ≤ (d + n) * x + (d - n) * y ∧ (d + n) * x + (d - n) * y ≤ d * d + 2 * d * n - n * n - d + n := by
  constructor
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ d + n by omega) (show (0:ℤ) ≤ x - 1 by omega),
      mul_nonneg (show (0:ℤ) ≤ d - n by omega) hy0]
  · nlinarith [mul_nonneg (show (0:ℤ) ≤ d + n by omega) (show (0:ℤ) ≤ d - x by omega),
      mul_nonneg (show (0:ℤ) ≤ d - n by omega) (show (0:ℤ) ≤ n - 1 - y by omega)]

/-- The spectrum is symmetric under `t ↦ L − t` (the reflection of the H trace). -/
theorem spec_reflect (frame : ChildFrame) (t : ℤ) (hL : (frame.child.num + frame.child.den) % 2 = 0)
    (hsp : frame.hSpectrum t) : frame.hSpectrum (frame.child.den + frame.child.num - t) := by
  unfold ChildFrame.hSpectrum at hsp ⊢
  omega

/-- The reflection of the trace: `t(reflH z) = L − t(z)`. -/
theorem tGrade_reflH (frame : ChildFrame) (z : Site) :
    frame.tGrade (frame.child.den + 1 - z.1, frame.child.num - 1 - z.2) =
      frame.child.den + frame.child.num - frame.tGrade z := by
  unfold ChildFrame.tGrade
  simp only
  ring

/-- **(iii) The tip membership.** For a trace point, `p + V_p` lies in the closed polygon. -/
theorem mem_tip_of (frame : ChildFrame) (hN1 : 1 ≤ frame.parents.odd.num)
    (hND : frame.parents.odd.num < frame.parents.odd.den) (hD2 : 2 ≤ frame.parents.odd.den)
    (hnq : 0 ≤ frame.parents.even.num) (hdq : 0 ≤ frame.parents.even.den)
    (hn_eq : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num)
    (hd_eq : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den)
    (heps : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den)
    (p : Site) (hbox : 1 ≤ p.1 ∧ p.1 ≤ frame.child.den ∧ 0 ≤ p.2 ∧ p.2 ≤ frame.child.num - 1)
    (hsp : frame.hSpectrum (frame.tGrade p)) :
    p + tipVertex frame ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hpar := FLatticePaper.Induction.tGrade_parity frame p
  have htip_t : frame.tGrade (p + tipVertex frame) = frame.tGrade p +
      (frame.child.num * (frame.parents.odd.num - frame.parents.odd.den) -
        frame.child.den * (frame.parents.odd.num + frame.parents.odd.den)) := by
    unfold ChildFrame.tGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have htip_s : frame.sGrade (p + tipVertex frame) = frame.sGrade p + 2 * frame.eps := by
    unfold ChildFrame.sGrade tipVertex
    simp only [Prod.fst_add, Prod.snd_add]
    rw [heps, hn_eq, hd_eq]
    ring
  have hTb := tv_bounds frame.child.num frame.child.den frame.parents.odd.num frame.parents.odd.den
    frame.parents.even.num frame.parents.even.den (by omega) hND hD2 hnq hdq hn_eq hd_eq hn0 (by omega)
  have hsb : frame.child.den + frame.child.num ≤ frame.sGrade p ∧
      frame.sGrade p ≤ frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num -
        frame.child.num * frame.child.num - frame.child.den + frame.child.num := by
    unfold ChildFrame.sGrade
    exact s_box frame.child.num frame.child.den p.1 p.2 hn0 (by omega) hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2
  have hu := frame.eps_unit
  rw [FLatticePaper.Induction.mem_closedPolygon_iff]
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨te, ta, tb⟩ | ⟨tod, tc, td⟩
  · have hevp : EvenSite (p + tipVertex frame) := by
      unfold EvenSite tipVertex
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_pos hevp, htip_t, htip_s, hT]
    rcases hu with h | h <;> rw [h] <;>
      exact ⟨by linarith [ta, tb, hTb.1, hTb.2, hsb.1, hsb.2], by linarith [ta, tb, hTb.1, hTb.2, hsb.1, hsb.2],
        by linarith [ta, tb, hTb.1, hTb.2, hsb.1, hsb.2], by linarith [ta, tb, hTb.1, hTb.2, hsb.1, hsb.2]⟩
  · have hodp : ¬ EvenSite (p + tipVertex frame) := by
      unfold EvenSite tipVertex
      simp only [Prod.fst_add, Prod.snd_add]
      omega
    rw [if_neg hodp, htip_t, htip_s, hT]
    rcases hu with h | h <;> rw [h] <;>
      exact ⟨by linarith [tc, td, hTb.1, hTb.2, hsb.1, hsb.2], by linarith [tc, td, hTb.1, hTb.2, hsb.1, hsb.2],
        by linarith [tc, td, hTb.1, hTb.2, hsb.1, hsb.2], by linarith [tc, td, hTb.1, hTb.2, hsb.1, hsb.2]⟩

/-! ### The inputs of the price identities -/

/-- The integer data of a word's frame: the parent bounds, the child's `n = 2N + n_q`, `d = 2D + d_q`, and `ε = N d_q − n_q D = ±1`. -/
theorem pdata {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    1 ≤ (frameAt word).parents.odd.num ∧ (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den ∧
      2 ≤ (frameAt word).parents.odd.den ∧ 0 ≤ (frameAt word).parents.even.num ∧
      0 ≤ (frameAt word).parents.even.den ∧
      (frameAt word).child.num = 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num ∧
      (frameAt word).child.den = 2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den ∧
      (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
        (frameAt word).parents.even.num * (frameAt word).parents.odd.den ∧
      ((frameAt word).eps = 1 ∨ (frameAt word).eps = -1) := by
  have hD2 : 2 ≤ (frameAt word).parents.odd.den :=
    FLatticePaper.W1ArcBottom.odd_den_ge_two (frameAt word) (child_num_ge_three h)
  obtain ⟨hDp, hN0, hND⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hdq, hnq0, hnqd⟩ := (frameAt word).valid.even_bounds
  have hpar : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have heps := ZoneI1.eps_eq (frameAt word)
  have hunit := (frameAt word).eps_unit
  have hn := ZoneI1.child_num_eq (frameAt word)
  have hd := ZoneI1.child_den_eq (frameAt word)
  have hN1 : 1 ≤ (frameAt word).parents.odd.num := by
    by_contra hc
    have hN : (frameAt word).parents.odd.num = 0 := by omega
    rw [hN] at heps
    have hprod : 0 ≤ (frameAt word).parents.even.num * (frameAt word).parents.odd.den :=
      mul_nonneg hnq0 (by omega)
    rcases hunit with hu | hu
    · nlinarith
    · rcases (show (frameAt word).parents.even.num = 0 ∨ 1 ≤ (frameAt word).parents.even.num by omega) with h0 | h1
      · rw [h0] at heps
        omega
      · nlinarith [mul_le_mul_of_nonneg_right h1 (show (0:ℤ) ≤ (frameAt word).parents.odd.den by omega)]
  exact ⟨hN1, by omega, hD2, hnq0, hdq.le, hn, hd, heps, hunit⟩

/-- **(i)** The standard field of the word vanishes on the trace (the zero band of the packet). -/
theorem F_zero_of_spec (frame : ChildFrame) (F : Field) (pk : frame.Packet F) (p : Site)
    (hsp : frame.hSpectrum (frame.tGrade p)) : F p = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  unfold ChildFrame.hSpectrum at hsp
  exact pk.strips.1 p (by rcases hsp with ⟨-, a, b⟩ | ⟨-, a, b⟩ <;> omega)
    (by rcases hsp with ⟨-, a, b⟩ | ⟨-, a, b⟩ <;> omega)

/-- **(ii), phase W1.** `A(p) = 0` on the trace: the conjugate's zero band at `x = p`, with `1 − D ≤ N x₁ − D x₂ ≤ N + 2D − 1`. -/
theorem A_zero_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) (p : Site)
    (hbox : 1 ≤ p.1 ∧ p.1 ≤ (frameAt word).child.den ∧ 0 ≤ p.2 ∧ p.2 ≤ (frameAt word).child.num - 1)
    (hsp : (frameAt word).hSpectrum ((frameAt word).tGrade p)) :
    (frameAt word).sheetA (FqW word) p = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := (frameAt word).child_facts
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hn2 : 2 ≤ (frameAt word).child.num := by omega
  have hrel : (frameAt word).parents.odd.num * (frameAt word).child.den - (frameAt word).child.num *
      (frameAt word).parents.odd.den = 1 := by
    rw [hd_eq, hn_eq]
    rw [hW1] at heps
    linear_combination (-1 : ℤ) * heps
  have hsb := s_box (frameAt word).child.num (frameAt word).child.den p.1 p.2 hn0 (by omega) hbox.1 hbox.2.1 hbox.2.2.1
    hbox.2.2.2
  have hb := band_W1 (frameAt word).child.num (frameAt word).child.den (frameAt word).parents.odd.num
    (frameAt word).parents.odd.den p.1 p.2 ((frameAt word).tGrade p) ((frameAt word).sGrade p) hn0 hn2 (by omega) hN1
    (by omega) hD2 hrel rfl (by unfold ChildFrame.sGrade; rfl)
    (by unfold ChildFrame.hSpectrum at hsp; unfold ChildFrame.tGrade; exact hsp) (by unfold ChildFrame.sGrade; exact hsb)
  have e1 : ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.den := by
    rw [hcn, hcd]
    omega
  have e2 : ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.num := by
    rw [hcn, hcd]
    omega
  unfold ChildFrame.sheetA FqW
  rw [sheetShift_W1 word hW1, sub_zero]
  exact W1ZeroStrip.zeroStrip_of_strips (frameAt (conjWord word)) hSE.packet.strips p
    (by rw [e1, e2]; exact hb.1) (by rw [e1, e2]; exact hb.2)

/-- **(ii), phase W0.** `A(p) = 0` on the trace, at `x = p − l_v`, `l_v = (d_q, n_q)`. -/
theorem A_zero_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW0 : (frameAt word).eps = -1) (p : Site)
    (hbox : 1 ≤ p.1 ∧ p.1 ≤ (frameAt word).child.den ∧ 0 ≤ p.2 ∧ p.2 ≤ (frameAt word).child.num - 1)
    (hsp : (frameAt word).hSpectrum ((frameAt word).tGrade p)) :
    (frameAt word).sheetA (FqW word) p = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := (frameAt word).child_facts
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hn2 : 2 ≤ (frameAt word).child.num := by omega
  have hrel : (frameAt word).parents.odd.num * (frameAt word).child.den - (frameAt word).child.num *
      (frameAt word).parents.odd.den = -1 := by
    rw [hd_eq, hn_eq]
    rw [hW0] at heps
    linear_combination (-1 : ℤ) * heps
  have hsb := s_box (frameAt word).child.num (frameAt word).child.den p.1 p.2 hn0 (by omega) hbox.1 hbox.2.1 hbox.2.2.1
    hbox.2.2.2
  have hb := band_W0 (frameAt word).child.num (frameAt word).child.den (frameAt word).parents.odd.num
    (frameAt word).parents.odd.den p.1 p.2 ((frameAt word).tGrade p) ((frameAt word).sGrade p) hn0 hn2 (by omega) hN1
    (by omega) hD2 hrel rfl (by unfold ChildFrame.sGrade; rfl)
    (by unfold ChildFrame.hSpectrum at hsp; unfold ChildFrame.tGrade; exact hsp) (by unfold ChildFrame.sGrade; exact hsb)
  have e1 : ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.den := by
    rw [hcn, hcd]
    omega
  have e2 : ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) / 2 =
      (frameAt word).parents.odd.num := by
    rw [hcn, hcd]
    omega
  unfold ChildFrame.sheetA FqW
  rw [sheetShift_W0 word hW0]
  exact W1ZeroStrip.zeroStrip_of_strips (frameAt (conjWord word)) hSE.packet.strips (p - ((frameAt word).parents.even.den, (frameAt word).parents.even.num))
    (by rw [e1, e2]; simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hb.1, heps, hW0])
    (by rw [e1, e2]; simp only [Prod.fst_sub, Prod.snd_sub]; linarith [hb.2, heps, hW0])

/-- **(iv)** The W1 reflection step: `F(z − V_p) = F(reflH z + V_p)`, from the packet's reflection and its `V`-period. -/
theorem refl_tip (frame : ChildFrame) (F : Field) (pk : frame.Packet F) (z : Site) :
    F (z - tipVertex frame) = F ((frame.child.den + 1 - z.1, frame.child.num - 1 - z.2) + tipVertex frame) := by
  have hV := ChildFrame.child_modifiedDeck_transverse frame
  have hK := ChildFrame.child_modifiedDeck_kernel frame
  have hper := pk.periods.2 (z - tipVertex frame)
  rw [hV] at hper
  have hrefl := pk.reflection ((z - tipVertex frame) + (frame.child.num - frame.child.den, frame.child.num + frame.child.den))
  rw [hper] at hrefl
  have e : frame.centre - ((z - tipVertex frame) + (frame.child.num - frame.child.den, frame.child.num + frame.child.den)) =
      (frame.child.den + 1 - z.1, frame.child.num - 1 - z.2) + tipVertex frame := by
    unfold ChildFrame.centre
    rw [hK, hV]
    unfold tipVertex
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [e] at hrefl
  rw [hrefl]
  have hL : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT2 := ShortPassages.T_mod_two frame
  have hk : 2 * frame.symmetryConstant =
      (frame.child.den + frame.child.num) - frame.child.periodDenominator := by
    unfold ChildFrame.symmetryConstant
    omega
  unfold Fraction.periodDenominator at hk
  unfold ChildFrame.coherentConstantV
  rw [hV]
  unfold ChildFrame.centre
  rw [hK, hV]
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add]
  unfold Fraction.transverseGrade
  unfold tipVertex
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination (-1 : ℤ) * hk

/-! ### The price identities from `z ∈ freeH` alone -/

/-- The trace point `z` satisfies the box and the spectrum. -/
theorem trace_facts {word : Word} (z : Site) (hz : z ∈ (frameAt word).freeH) :
    (1 ≤ z.1 ∧ z.1 ≤ (frameAt word).child.den ∧ 0 ≤ z.2 ∧ z.2 ≤ (frameAt word).child.num - 1) ∧
      (frameAt word).hSpectrum ((frameAt word).tGrade z) := by
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  exact ⟨FreeTraceBox.freeH_box (frameAt word) (by simp only [ChildFrame.freeH, Set.mem_setOf_eq]; exact hz), hz.2.2⟩

/-- **The price in phase W0 from the trace.** `P(z) = c₀ − E_H(z)` with `E_H = 1 + min(0, Ψ − 1)`. -/
theorem price_W0_trace {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW0 : (frameAt word).eps = -1) (z : Site)
    (hz : z ∈ (frameAt word).freeH) :
    (frameAt word).price (standardField word) z =
      (frameAt word).cutPrice - (1 + min 0 (sheetPsi word z - 1)) := by
  obtain ⟨hbox, hsp⟩ := trace_facts (word := word) z hz
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  have hz0 := F_zero_of_spec (frameAt word) (standardField word) (packet_of_strong h hSE) z hsp
  have hA0 := A_zero_W0 h hSE hW0 z hbox hsp
  have hmem := mem_tip_of (frameAt word) hN1 (by omega) hD2 hnq hdq hn_eq hd_eq heps z hbox hsp
  have hFV := standardField_eq_sheetMin_of_strong h hSE hmem
  exact price_W0 h hSE hW0 z hz0 hA0 hFV

/-- **The price in phase W1 from the trace**, through the reflection `w = reflH z`. -/
theorem price_W1_trace {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hW1 : (frameAt word).eps = 1) (z : Site)
    (hz : z ∈ (frameAt word).freeH) :
    (frameAt word).price (standardField word) z =
      (frameAt word).cutPrice - 1 - min 0 (sheetPsi word (FLatticePaper.ArcPsi.reflH word z) - 1) := by
  obtain ⟨hbox, hsp⟩ := trace_facts (word := word) z hz
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := (frameAt word).child_facts
  have hz0 := F_zero_of_spec (frameAt word) (standardField word) (packet_of_strong h hSE) z hsp
  have hR := refl_tip (frameAt word) (standardField word) (packet_of_strong h hSE) z
  have hboxw : 1 ≤ (FLatticePaper.ArcPsi.reflH word z).1 ∧ (FLatticePaper.ArcPsi.reflH word z).1 ≤ (frameAt word).child.den ∧
      0 ≤ (FLatticePaper.ArcPsi.reflH word z).2 ∧ (FLatticePaper.ArcPsi.reflH word z).2 ≤ (frameAt word).child.num - 1 := by
    unfold FLatticePaper.ArcPsi.reflH
    dsimp only
    omega
  have hspw : (frameAt word).hSpectrum ((frameAt word).tGrade (FLatticePaper.ArcPsi.reflH word z)) := by
    have e := tGrade_reflH (frameAt word) z
    unfold FLatticePaper.ArcPsi.reflH
    rw [e]
    have hL : ((frameAt word).child.num + (frameAt word).child.den) % 2 = 0 := (frameAt word).child_even
    exact spec_reflect (frameAt word) _ hL hsp
  have hA0w := A_zero_W1 h hSE hW1 (FLatticePaper.ArcPsi.reflH word z) hboxw hspw
  have hmemw := mem_tip_of (frameAt word) hN1 (by omega) hD2 hnq hdq hn_eq hd_eq heps
    (FLatticePaper.ArcPsi.reflH word z) hboxw hspw
  have hFVw := standardField_eq_sheetMin_of_strong h hSE hmemw
  exact price_W1 h hSE hW1 z hz0 hR hA0w hFVw

end FLatticePaper.PriceInputs
