import FLatticePaper.Tiles.EncUpper

/-! Task 53, item 2 (encOdd / encEven): the lower facets of the six natural sources, one family per
(child type, flag, source parent), split by site parity and side. Generated from the margin identities
(sympy: lex remainder and quotient); each margin is `linarith` from its quotient and remainder. -/

namespace FLatticePaper.Tiles.EncFam

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.EncUpper

theorem fam_P1p_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = 2 * n := aOf_mk_true_le n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * (2 * n) + (2 * r) := childA_true_below n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - 2 * n := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-2*d - 2*n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n - 2*d - n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := 2 * n) (lP := 0) (aC := (1 * (2 * n) + (2 * r))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = (((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * (2 * n) + (2 * r)) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * (2 * n) + (2 * r)) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*n^2 + 4*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := 0) (aP := 2 * n) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = ((((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-e + r, e + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1p_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = (d - n) := aOf_mk_true_ge n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * ((d - n)) + ((e - r)) := childA_true_above n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (d - n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - (d - n) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*d) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n + 2*d - n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := (d - n)) (lP := 0) (aC := (1 * ((d - n)) + ((e - r)))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = (((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * ((d - n)) + ((e - r))) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * ((d - n)) + ((e - r))) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := 0) (aP := (d - n)) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = ((((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-e + r, e + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1p_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (3 * n - d) := lOf_mk_false_le n d (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (3 * n - d) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-d - n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n - 2*d - n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := n) (lP := (3 * n - d)) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = (((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 4*d - 2*n^2 - 2*n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 4*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := (3 * n - d)) (aP := n) (lC := (1 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = ((((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-e + r, e + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1p_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (d - n) := lOf_mk_false_ge n d (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((d - n)) + ((e - r)) := childL_false_above n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (d - n) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-d - n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n - n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := n) (lP := (d - n)) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = (((1 * n + r) * (-e + r) - (1 * d + e) * (e + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n + 2*d - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := (d - n)) (aP := n) (lC := (1 * ((d - n)) + ((e - r)))) (g0 := (((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) = ((((1 * d + e) + (1 * n + r)) * (-e + r) + ((1 * d + e) - (1 * n + r)) * (e + r))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-e + r, e + r) + w).1 + ((-e + r, e + r) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) - (1 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-e + r, e + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) (1 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1p (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_P1p_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_P1p_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_P1p_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_P1p_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_Q1p_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = 2 * r := aOf_mk_true_le r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * (2 * n) + (2 * r) := childA_true_below n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - 2 * r := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (e^2 + 2*e*r + 2*e - r^2 + 2*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r + 2*e - r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := 2 * r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0)) (aC := (1 * (2 * n) + (2 * r))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) = (((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) - (1 * (2 * n) + (2 * r)) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0)) = 1 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) (1 * (2 * n) + (2 * r)) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (0) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 2*e - 2*r^2 + 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := 0) (hi := ((e + r) - 2 * r)) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1p_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = (e - r) := aOf_mk_true_ge r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * ((d - n)) + ((e - r)) := childA_true_above n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (e - r) - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - (e - r) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (e^2 + 2*e*r - 2*e - r^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r - 2*e - r^2 - 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := (e - r)) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0)) (aC := (1 * ((d - n)) + ((e - r)))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) = (((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) - (1 * ((d - n)) + ((e - r))) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) (1 * ((d - n)) + ((e - r))) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (0) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := 0) (hi := ((e + r) - (e - r))) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1p_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (3 * r - e) := lOf_mk_false_le r e (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (3 * r - e) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (e^2 + 2*e*r + e - r^2 + r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r - r^2 + 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e))) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) = (((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (4*e + 2*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 2*e - 2*r^2 + 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := (3 * r - e)) (hi := ((e + r) - r)) (lC := (1 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 1 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (1 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1p_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (e - r) := lOf_mk_false_ge r e (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((d - n)) + ((e - r)) := childL_false_above n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (e - r) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (e^2 + 2*e*r + e - r^2 + r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r + 2*e - r^2 - 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r))) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) = (((1 * n + r) * (d + e + n) - (1 * d + e) * (d + 3*n + r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((d + e + n, d + 3*n + r) + w).1 + ((d + e + n, d + 3*n + r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (-2*e) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := (e - r)) (hi := ((e + r) - r)) (lC := (1 * ((d - n)) + ((e - r)))) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (1 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1p (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_Q1p_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_Q1p_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_Q1p_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_Q1p_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_P1n_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = 2 * n := aOf_mk_true_le n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * (2 * n) + (2 * r) := childA_true_below n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - 2 * n := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - 2*d + 2*n^2 - 2*n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n + 2*d - n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := 2 * n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0)) (aC := (1 * (2 * n) + (2 * r))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) = (((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) - (1 * (2 * n) + (2 * r)) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0)) = 1 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) (1 * (2 * n) + (2 * r)) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (0) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := 0) (hi := ((d + n) - 2 * n)) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1n_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = (d - n) := aOf_mk_true_ge n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * ((d - n)) + ((e - r)) := childA_true_above n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (d - n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - (d - n) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n + 2*d + 2*n^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n - 2*d - n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := (d - n)) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0)) (aC := (1 * ((d - n)) + ((e - r)))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) = (((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) - (1 * ((d - n)) + ((e - r))) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) (1 * ((d - n)) + ((e - r))) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (0) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*n^2 - 4*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := 0) (hi := ((d + n) - (d - n))) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1n_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (3 * n - d) := lOf_mk_false_le n d (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (3 * n - d) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - d + 2*n^2 - n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n - n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d))) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) = (((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*d - 2*n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := (3 * n - d)) (hi := ((d + n) - n)) (lC := (1 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 1 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (1 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1n_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = (1 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (d - n) := lOf_mk_false_ge n d (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((d - n)) + ((e - r)) := childL_false_above n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (d - n) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - d + 2*n^2 - n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < d^2 + 2*d*n + 2*d - n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aP := n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n))) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) (k := 1) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) = (((1 * n + r) * (e + r) - (1 * d + e) * (e + 3*r))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((e + r, e + 3*r) + w).1 + ((e + r, e + 3*r) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (2*d) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 4*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lP := (d - n)) (hi := ((d + n) - n)) (lC := (1 * ((d - n)) + ((e - r)))) (g0 := (((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) = ((((1 * d + e) + (1 * n + r)) * (0) + ((1 * d + e) - (1 * n + r)) * (0))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) - (1 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) (1 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P1n (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0, 0) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_P1n_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_P1n_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_P1n_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_P1n_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_Q1n_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = 2 * r := aOf_mk_true_le r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * (2 * n) + (2 * r) := childA_true_below n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - 2 * r := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (2*e + 2*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r - 2*e - r^2 - 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := 2 * r) (lQ := 0) (aC := (1 * (2 * n) + (2 * r))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = (((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * (2 * n) + (2 * r)) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * (2 * n) + (2 * r)) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-2*e^2 - 4*e*r + 2*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := 0) (aQ := 2 * r) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = ((((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-d + n, d + n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1n_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = (e - r) := aOf_mk_true_ge r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ true = 1 * ((d - n)) + ((e - r)) := childA_true_above n d r e 1 (Or.inl rfl) hb
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ true = 0 := lOf_true' ⟨1 * n + r, 1 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (e - r) - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - (e - r) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*e) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r + 2*e - r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := (e - r)) (lQ := 0) (aC := (1 * ((d - n)) + ((e - r)))) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = (((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * ((d - n)) + ((e - r))) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * ((d - n)) + ((e - r))) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-2*e^2 - 4*e*r + 2*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 2*e - 2*r^2 - 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := 0) (aQ := (e - r)) (lC := (0)) (g0 := (((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = ((((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (0)) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-d + n, d + n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1n_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (3 * r - e) := lOf_mk_false_le r e (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (3 * r - e) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (e + r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r - 2*e - r^2 + 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := r) (lQ := (3 * r - e)) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = (((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-2*e^2 - 4*e*r + 4*e + 2*r^2 + 2*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := (3 * r - e)) (aQ := r) (lC := (1 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = ((((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-d + n, d + n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1n_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨1 * n + r, 1 * d + e⟩ = ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2) := by unfold tOf; ring
  have hsumC : ((1 * n + r) + (1 * d + e)) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 1 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨1 * n + r, 1 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 1 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 1 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 1 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (e - r) := lOf_mk_false_ge r e (by omega)
  have hCa : aOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * n + r := aOf_child_false 1 n r d e
  have hCl : lOf ⟨1 * n + r, 1 * d + e⟩ false = 1 * ((d - n)) + ((e - r)) := childL_false_above n d r e 1 (Or.inl rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (e - r) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (e + r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < e^2 + 2*e*r - r^2 - 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (aQ := r) (lQ := (e - r)) (aC := (1 * n + r)) (TC := ((1 * d + e) ^ 2 + 2 * (1 * d + e) * (1 * n + r) - (1 * n + r) ^ 2)) (g0 := ((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) (k := 1) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = (((1 * n + r) * (-d + n) - (1 * d + e) * (d + n))) + tCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -1 < tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * n + r) + tOf ⟨1 * n + r, 1 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have ct := lowT1 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * n + r) hAzt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-2*e^2 - 4*e*r - 2*e + 2*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 2*e - 2*r^2 + 2*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨1 * n + r, 1 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 1) (lQ := (e - r)) (aQ := r) (lC := (1 * ((d - n)) + ((e - r)))) (g0 := (((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) = ((((1 * d + e) + (1 * n + r)) * (-d + n) + ((1 * d + e) - (1 * n + r)) * (d + n))) + sCo ⟨1 * n + r, 1 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((((-d + n, d + n) + w).1 + ((-d + n, d + n) + w).2) % 2 = 0)) = 1 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) - (1 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sB ⟨1 * n + r, 1 * d + e⟩ hsumC ((-d + n, d + n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) (1 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q1n (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w) :
    aOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨1 * n + r, 1 * d + e⟩ ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) ∧
      lOf ⟨1 * n + r, 1 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_Q1n_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_Q1n_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_Q1n_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_Q1n_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_P2p_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = 2 * n := aOf_mk_true_le n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * (2 * n) + (2 * r) := childA_true_below n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - 2 * n := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-2*d - 2*n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n - 2*d - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := 2 * n) (lP := 0) (aC := (2 * (2 * n) + (2 * r))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = (((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * (2 * n) + (2 * r)) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*n^2 + 4*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := 0) (aP := 2 * n) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = ((((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2p_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = (d - n) := aOf_mk_true_ge n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * ((d - n)) + ((e - r)) := childA_true_above n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (d - n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - (d - n) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*d) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := (d - n)) (lP := 0) (aC := (2 * ((d - n)) + ((e - r)))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = (((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * ((d - n)) + ((e - r))) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := 0) (aP := (d - n)) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = ((((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2p_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (3 * n - d) := lOf_mk_false_le n d (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (3 * n - d) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-d - n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n - 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := n) (lP := (3 * n - d)) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = (((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n - 4*d - 2*n^2 - 2*n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 4*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := (3 * n - d)) (aP := n) (lC := (2 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = ((((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2p_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w + sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w + 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (d - n) := lOf_mk_false_ge n d (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((d - n)) + ((e - r)) := childL_false_above n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (d - n) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (-d - n) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := n) (lP := (d - n)) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = (((2 * n + r) * (-d - e + n + r) - (2 * d + e) * (d + e + n + r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (2*d^2 + 4*d*n + 2*d - 2*n^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := (d - n)) (aP := n) (lC := (2 * ((d - n)) + ((e - r)))) (g0 := (((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) = ((((2 * d + e) + (2 * n + r)) * (-d - e + n + r) + ((2 * d + e) - (2 * n + r)) * (d + e + n + r))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d - e + n + r, d + e + n + r) + w).1 + ((-d - e + n + r, d + e + n + r) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) - (2 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d - e + n + r, d + e + n + r) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) (2 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2p (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_P2p_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_P2p_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_P2p_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_P2p_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_Q2p_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = 2 * r := aOf_mk_true_le r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * (2 * n) + (2 * r) := childA_true_below n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - 2 * r := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*e^2 + 4*e*r + 4*e - 2*r^2 + 4*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := 2 * r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0)) (aC := (2 * (2 * n) + (2 * r))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) = (((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0)) = 2 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((2*n, 2*d + 4*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) (2 * (2 * n) + (2 * r)) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (0) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := 0) (hi := ((e + r) - 2 * r)) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2p_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = (e - r) := aOf_mk_true_ge r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * ((d - n)) + ((e - r)) := childA_true_above n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (e - r) - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - (e - r) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*e^2 + 4*e*r - 4*e - 2*r^2) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := (e - r)) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0)) (aC := (2 * ((d - n)) + ((e - r)))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) = (((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((2*n, 2*d + 4*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) (2 * ((d - n)) + ((e - r))) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (0) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 2*r^2 - 8*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := 0) (hi := ((e + r) - (e - r))) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2p_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (3 * r - e) := lOf_mk_false_le r e (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (3 * r - e) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*e^2 + 4*e*r + 2*e - 2*r^2 + 2*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e))) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) = (((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((2*n, 2*d + 4*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (8*e + 4*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := (3 * r - e)) (hi := ((e + r) - r)) (lC := (2 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 2 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (2 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2p_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (1) hdet (Or.inl rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w - 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w - 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (e - r) := lOf_mk_false_ge r e (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((d - n)) + ((e - r)) := childL_false_above n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (e - r) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((1))) * (2*e^2 + 4*e*r + 2*e - 2*r^2 + 2*r) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_pos (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := r) (hi := (1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r))) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) = (((2 * n + r) * (2*n) - (2 * d + e) * (2*d + 4*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((2*n, 2*d + 4*n) + w).1 + ((2*n, 2*d + 4*n) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((2*n, 2*d + 4*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((1))) * (-4*e) = 0 := by
    rw [show d * r - n * e - ((1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 8*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_pos (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := (e - r)) (hi := ((e + r) - r)) (lC := (2 * ((d - n)) + ((e - r)))) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (2 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2p (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_Q2p_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_Q2p_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (1) _hn hnd hr _hre hdet (Or.inl rfl) with hb | hb
    · exact fam_Q2p_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_Q2p_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_P2n_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = 2 * n := aOf_mk_true_le n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * (2 * n) + (2 * r) := childA_true_below n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - 2 * n := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - 2*d + 2*n^2 - 2*n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := 2 * n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0)) (aC := (2 * (2 * n) + (2 * r))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) = (((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0)) = 2 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d + n + r, d + e + n + 2*r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) (2 * (2 * n) + (2 * r)) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (0) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := 0) (hi := ((d + n) - 2 * n)) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2n_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ true = (d - n) := aOf_mk_true_ge n d (by omega)
  have hPl : lOf ⟨n, d⟩ true = 0 := lOf_mk_true n d
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * ((d - n)) + ((e - r)) := childA_true_above n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (d - n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - (d - n) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n + 2*d + 2*n^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n - 2*d - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := (d - n)) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0)) (aC := (2 * ((d - n)) + ((e - r)))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) = (((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d + n + r, d + e + n + 2*r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) (2 * ((d - n)) + ((e - r))) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (0) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 2*n^2 - 4*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := 0) (hi := ((d + n) - (d - n))) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2n_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (3 * n - d) := lOf_mk_false_le n d (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (3 * n - d) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - d + 2*n^2 - n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (3 * n - d))) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) = (((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d + n + r, d + e + n + 2*r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*d - 2*n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 + 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := (3 * n - d)) (hi := ((d + n) - n)) (lC := (2 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 2 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (2 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2n_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (d ^ 2 + 2 * d * n - n ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * tCo ⟨n, d⟩ w - sCo ⟨n, d⟩ w := by
    have h := ident_tP n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (d ^ 2 + 2 * d * n - n ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = (2 * (d ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r)) * sCo ⟨n, d⟩ w - 2 * tCo ⟨n, d⟩ w := by
    have h := ident_sP n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨n, d⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨n, d⟩ false = n := aOf_mk_false n d
  have hPl : lOf ⟨n, d⟩ false = (d - n) := lOf_mk_false_ge n d (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((d - n)) + ((e - r)) := childL_false_above n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hPt : tOf ⟨n, d⟩ = (d ^ 2 + 2 * d * n - n ^ 2) := tOf_mk n d
  rw [hPm, hPt, hPl] at hA4
  have bTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ tCo ⟨n, d⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨n, d⟩ w ≤ (d + n) - n := by linarith only [hA2, hPa]
  have bSlo : (d - n) ≤ sCo ⟨n, d⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨n, d⟩ w ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-2*d^2 - 4*d*n - d + 2*n^2 - n) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*d^2 + 4*d*n + 2*d - 2*n^2 - 2*n := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tP_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aP := n) (hi := (2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - (d - n))) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) (k := 2) hD hK (by norm_num) hXt bTlo bShi (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) = (((2 * n + r) * (-d + n + r) - (2 * d + e) * (d + e + n + 2*r))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-d + n + r, d + e + n + 2*r) + w).1 + ((-d + n + r, d + e + n + 2*r) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-d + n + r, d + e + n + 2*r) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (2*d) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*d^2 + 4*d*n - 4*d - 2*n^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sP_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tP := tCo ⟨n, d⟩ w) (sP := sCo ⟨n, d⟩ w) (Dn := (d ^ 2 + 2 * d * n - n ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lP := (d - n)) (hi := ((d + n) - n)) (lC := (2 * ((d - n)) + ((e - r)))) (g0 := (((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) (k := 2) hD hK (by norm_num) hXs bThi bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) = ((((2 * d + e) + (2 * n + r)) * (0) + ((2 * d + e) - (2 * n + r)) * (0))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((0, 0) + w).1 + ((0, 0) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) - (2 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((0, 0) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) (2 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_P2n (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨n, d⟩ w) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0, 0) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_P2n_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_P2n_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_P2n_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_P2n_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

theorem fam_Q2n_e_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : 3 * n ≤ d ∧ 3 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = 2 * r := aOf_mk_true_le r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * (2 * n) + (2 * r) := childA_true_below n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : 2 * r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - 2 * r := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (4*e + 4*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := 2 * r) (lQ := 0) (aC := (2 * (2 * n) + (2 * r))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = (((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * (2 * n) + (2 * r) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * (2 * n) + (2 * r)) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * (2 * n) + (2 * r)) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*e^2 - 8*e*r + 4*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 2*r^2 + 8*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := 0) (aQ := 2 * r) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = ((((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2n_e_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : (w.1 + w.2) % 2 = 0) (hb : d ≤ 3 * n ∧ e ≤ 3 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_even (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ true = (e - r) := aOf_mk_true_ge r e (by omega)
  have hPl : lOf ⟨r, e⟩ true = 0 := lOf_mk_true r e
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ true = 2 * ((d - n)) + ((e - r)) := childA_true_above n d r e 2 (Or.inr rfl) hb
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ true = 0 := lOf_true' ⟨2 * n + r, 2 * d + e⟩
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : (e - r) - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - (e - r) := by linarith only [hA2, hPa]
  have bSlo : 0 ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (-4*e) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := (e - r)) (lQ := 0) (aC := (2 * ((d - n)) + ((e - r)))) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = (((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzT, decide_eq_true hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((d - n)) + ((e - r))) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * ((d - n)) + ((e - r))) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*e^2 - 8*e*r + 4*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := 0) (aQ := (e - r)) (lC := (0)) (g0 := (((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = ((((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (0) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 0 := by rw [hdzS, decide_eq_true hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (0)) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (0) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2n_o_b (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : 2 * n ≤ d ∧ 2 * r ≤ e) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (3 * r - e) := lOf_mk_false_le r e (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((3 * n - d)) + ((3 * r - e)) := childL_false_below n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (3 * r - e) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (2*e + 2*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r - 4*e - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := r) (lQ := (3 * r - e)) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = (((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*e^2 - 8*e*r + 8*e + 4*r^2 + 4*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r - 8*e - 2*r^2 := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := (3 * r - e)) (aQ := r) (lC := (2 * ((3 * n - d)) + ((3 * r - e)))) (g0 := (((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = ((((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((3 * n - d)) + ((3 * r - e))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * ((3 * n - d)) + ((3 * r - e)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((3 * n - d)) + ((3 * r - e)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * ((3 * n - d)) + ((3 * r - e))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2n_o_a (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w)
    (hpar : ¬ (w.1 + w.2) % 2 = 0) (hb : d ≤ 2 * n ∧ e ≤ 2 * r) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  have hb1 := hb.1
  have hb2 := hb.2
  obtain ⟨hr1, he1⟩ := re_odd n d r e (-1) hdet (Or.inr rfl) heven
  have hD : 0 < (e ^ 2 + 2 * e * r - r ^ 2) := by nlinarith only [mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have hK : 0 ≤ ((d + n) * e + (d - n) * r) := by nlinarith only [mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d + n by omega) (show (0:ℤ) < e by omega)]
  have hdzT : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hdzS : decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0) = decide ((w.1 + w.2) % 2 = 0) :=
    decide_eq_decide.mpr (by simp only [Prod.fst_add, Prod.snd_add]; omega)
  have hTC : tOf ⟨2 * n + r, 2 * d + e⟩ = ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2) := by unfold tOf; ring
  have hnumC : (2 * n + r) % 2 = 1 := by omega
  have hdenC : (2 * d + e) % 2 = 1 := by omega
  have hXt : (e ^ 2 + 2 * e * r - r ^ 2) * tCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * tCo ⟨r, e⟩ w + 2 * sCo ⟨r, e⟩ w := by
    have h := ident_tQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  have hXs : (e ^ 2 + 2 * e * r - r ^ 2) * sCo ⟨2 * n + r, 2 * d + e⟩ w = ((e ^ 2 + 2 * e * r - r ^ 2) + 2 * ((d + n) * e + (d - n) * r)) * sCo ⟨r, e⟩ w + 2 * 2 * tCo ⟨r, e⟩ w := by
    have h := ident_sQ n d e r 2 w; rw [hdet] at h; linarith only [h]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := (inH_odd (f := ⟨r, e⟩) hpar).mp hw
  dsimp only at hA1 hA2 hA3 hA4
  have hPa : aOf ⟨r, e⟩ false = r := aOf_mk_false r e
  have hPl : lOf ⟨r, e⟩ false = (e - r) := lOf_mk_false_ge r e (by omega)
  have hCa : aOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * n + r := aOf_child_false 2 n r d e
  have hCl : lOf ⟨2 * n + r, 2 * d + e⟩ false = 2 * ((d - n)) + ((e - r)) := childL_false_above n d r e 2 (Or.inr rfl) hb
  have hPm : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hPt : tOf ⟨r, e⟩ = (e ^ 2 + 2 * e * r - r ^ 2) := tOf_mk r e
  rw [hPm, hPt, hPl] at hA4
  have bTlo : r - (e ^ 2 + 2 * e * r - r ^ 2) ≤ tCo ⟨r, e⟩ w := by linarith only [hA1, hPa, hPt]
  have bThi : tCo ⟨r, e⟩ w ≤ (e + r) - r := by linarith only [hA2, hPa]
  have bSlo : (e - r) ≤ sCo ⟨r, e⟩ w := by linarith only [hA3, hPl]
  have bShi : sCo ⟨r, e⟩ w ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) := by linarith only [hA4]
  have hqt : (d * r - n * e - ((-1))) * (2*e + 2*r) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRt : 0 < 2*e^2 + 4*e*r - 2*r^2 - 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bt := base_tQ_neg (X := tCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (aQ := r) (lQ := (e - r)) (aC := (2 * n + r)) (TC := ((2 * d + e) ^ 2 + 2 * (2 * d + e) * (2 * n + r) - (2 * n + r) ^ 2)) (g0 := ((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXt bTlo bSlo (by linarith only [hqt, hRt])
  have hzt : tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = (((2 * n + r) * (-2*d + 2*n) - (2 * d + e) * (2*d + 2*n))) + tCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [tCo, Prod.fst_add, Prod.snd_add]; ring
  have hYt : -2 < tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩ := by linarith only [bt, hzt, hTC]
  have hAzt : aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * n + r := by rw [hdzT, decide_eq_false hpar, hCa]
  have hpt : (tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * n + r) + tOf ⟨2 * n + r, 2 * d + e⟩) % 2 = 0 := by
    have := par_tA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hAzt] at this; exact this
  have ct := lowT2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * n + r) hAzt hpt hYt
  rw [hdzT] at ct
  have hqs : (d * r - n * e - ((-1))) * (-4*e^2 - 8*e*r - 4*e + 4*r^2) = 0 := by
    rw [show d * r - n * e - ((-1)) = 0 by linarith only [hdet], zero_mul]
  have hRs : 0 < 2*e^2 + 4*e*r + 4*e - 2*r^2 + 4*r := by nlinarith only [hnd, hr, _hre, _hn, hb1, hb2, mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ d by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ 5 * r - 4 by omega), mul_nonneg (sub_nonneg.2 hb2) (show (0:ℤ) ≤ e + 2 * r - 4 by omega), mul_nonneg (show (0:ℤ) ≤ r by omega) (sub_nonneg.2 hb2), mul_nonneg (show (0:ℤ) ≤ r by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (show (0:ℤ) ≤ e - r - 2 by omega) (show (0:ℤ) ≤ e + r by omega), mul_nonneg (show (0:ℤ) ≤ e by omega) (show (0:ℤ) ≤ r - 1 by omega), mul_nonneg (sub_nonneg.2 hb1) (show (0:ℤ) ≤ n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega)]
  have bs := base_sQ_neg (X := sCo ⟨2 * n + r, 2 * d + e⟩ w) (tQ := tCo ⟨r, e⟩ w) (sQ := sCo ⟨r, e⟩ w) (Dn := (e ^ 2 + 2 * e * r - r ^ 2)) (K := ((d + n) * e + (d - n) * r)) (m := 2) (lQ := (e - r)) (aQ := r) (lC := (2 * ((d - n)) + ((e - r)))) (g0 := (((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) (k := 2) hD hK (by norm_num) hXs bTlo bSlo (by linarith only [hqs, hRs])
  have hzs : sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) = ((((2 * d + e) + (2 * n + r)) * (-2*d + 2*n) + ((2 * d + e) - (2 * n + r)) * (2*d + 2*n))) + sCo ⟨2 * n + r, 2 * d + e⟩ w := by simp only [sCo, Prod.fst_add, Prod.snd_add]; ring
  have hYs : -2 < sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((d - n)) + ((e - r))) := by linarith only [bs, hzs]
  have hLzs : lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((((-2*d + 2*n, 2*d + 2*n) + w).1 + ((-2*d + 2*n, 2*d + 2*n) + w).2) % 2 = 0)) = 2 * ((d - n)) + ((e - r)) := by rw [hdzS, decide_eq_false hpar, hCl]
  have hps : (sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) - (2 * ((d - n)) + ((e - r)))) % 2 = 0 := by
    have := par_sA ⟨2 * n + r, 2 * d + e⟩ hnumC hdenC ((-2*d + 2*n, 2*d + 2*n) + w); rw [hLzs] at this; exact this
  have cs := lowS2 ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) (2 * ((d - n)) + ((e - r))) hLzs hps hYs
  rw [hdzS] at cs
  exact ⟨ct, cs⟩

theorem fam_Q2n (n d e r : ℤ) (_hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = (-1)) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (hw : InH ⟨r, e⟩ w) :
    aOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) - tOf ⟨2 * n + r, 2 * d + e⟩ ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) ∧
      lOf ⟨2 * n + r, 2 * d + e⟩ (decide ((w.1 + w.2) % 2 = 0)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  by_cases hpar : (w.1 + w.2) % 2 = 0
  · rcases side3 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_Q2n_e_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
    · exact fam_Q2n_e_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar hb
  · have hpar' : ¬ (w.1 + w.2) % 2 = 0 := hpar
    rcases side2 n d r e (-1) _hn hnd hr _hre hdet (Or.inr rfl) with hb | hb
    · exact fam_Q2n_o_b n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb
    · exact fam_Q2n_o_a n d e r _hn hnd hr _hre hdet hodd heven w hw hpar' hb

end FLatticePaper.Tiles.EncFam
