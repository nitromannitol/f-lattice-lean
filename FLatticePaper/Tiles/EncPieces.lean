import FLatticePaper.Tiles.EncFam
import FLatticePaper.Tiles.SitePairScope

namespace FLatticePaper.Tiles.EncPieces

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Construction
open FLatticePaper.Tiles.EncUpper FLatticePaper.Tiles.EncFam FLatticePaper.Tiles.SitePairScope


theorem mem_zero_piece (C f : Fraction) (P : ∀ w : ℤ × ℤ, InH f w → InH C (((0 : ℤ), (0 : ℤ)) + w))
    (z : ℤ × ℤ) (hz : InH f z) : InH C z := by
  have h := P z hz
  rwa [show ((0 : ℤ), (0 : ℤ)) + z = z from by ext <;> simp] at h

theorem mem_shift_piece (C f : Fraction) (u v : ℤ × ℤ) (huv : u = v)
    (P : ∀ w : ℤ × ℤ, InH f w → InH C (v + w)) (z : ℤ × ℤ) (hz : z ∈ shiftS (HSet f) u) :
    InH C z := by
  obtain ⟨x, hx, hxz⟩ := hz
  have hxz' : x + u = z := hxz
  subst huv
  rw [← hxz', add_comm]
  exact P x hx

theorem gr_1pP_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (2*e, 2*r) := by
  have hq : (d * r - n * e - (1)) * (-1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d*e + e^2 + 2*e*n + 2*e*r - n*r - r^2 - 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pP_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pP_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (2*e, 2*r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + 2*e^2 + 4*e*n + 4*e*r - 2*n*r - 2*r^2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1pP_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (-e + r, e + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d^2 + d*e + 2*d*n + 2*e*n - n^2 - n*r := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (e, r) := by
  have hq : (d * r - n * e - (1)) * (-1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d^2 + d*e + 2*d*n + 2*e*n - n^2 - n*r - 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_2_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (d + n, d + 3*n) := by
  have hq : (d * r - n * e - (1)) * (1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_3_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (e, r) := by
  have hq : (d * r - n * e - (1)) * (1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d*e + e^2 + 2*e*n + 2*e*r - n*r - r^2 + 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_2_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (d + n, d + 3*n) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 2*d*e + 4*d*n + 4*e*n - 2*n^2 - 2*n*r := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1pQ_3_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (d + e + n, d + 3*n + r) := by
  have hq : (d * r - n * e - (1)) * (1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 3*d*e + 4*d*n + e^2 + 6*e*n + 2*e*r - 2*n^2 - 3*n*r - r^2 + 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nP_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (e + r, e + 3*r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (-1)) * (3) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d*e + e^2 + 2*e*n + 2*e*r - n*r - r^2 - 3 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nP_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (e + r, e + 3*r) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (e + r, e + 3*r) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nP_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nP_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (e + r, e + 3*r) := by
  have hq : (d * r - n * e - (-1)) * (4) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + 2*e^2 + 4*e*n + 4*e*r - 2*n*r - 2*r^2 - 4 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (2*d, 2*n) := by
  have hq : (d * r - n * e - (-1)) * (3) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d^2 + d*e + 2*d*n + 2*e*n - n^2 - n*r - 3 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (2*d + e, 2*n + r) := by
  have hq : (d * r - n * e - (-1)) * (2) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d^2 + d*e + 2*d*n + 2*e*n - n^2 - n*r - 2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_2_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_3_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ tCo ⟨1 * n + r, 1 * d + e⟩ (-d + e + n, d + n + r) := by
  have hq : (d * r - n * e - (-1)) * (-1) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (2*d, 2*n) := by
  have hq : (d * r - n * e - (-1)) * (4) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 2*d*e + 4*d*n + 4*e*n - 2*n^2 - 2*n*r - 4 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (2*d + e, 2*n + r) := by
  have hq : (d * r - n * e - (-1)) * (5) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 3*d*e + 4*d*n + e^2 + 6*e*n + 2*e*r - 2*n^2 - 3*n*r - r^2 - 5 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_2_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_1nQ_3_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨1 * n + r, 1 * d + e⟩ (-d + n, d + n) ≤ sCo ⟨1 * n + r, 1 * d + e⟩ (-d + e + n, d + n + r) := by
  have hq : (d * r - n * e - (-1)) * (1) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ d*e + e^2 + 2*e*n + 2*e*r - n*r - r^2 - 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (e, r) := by
  have hq : (d * r - n * e - (1)) * (1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 3*d*e + 4*d*n + e^2 + 6*e*n + 2*e*r - 2*n^2 - 3*n*r - r^2 + 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-d + e + n, d + n + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_2_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-e + r, e + r) := by
  have hq : (d * r - n * e - (1)) * (1) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + d*e + 4*d*n + 2*e*n - 2*n^2 - n*r + 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_3_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (e, r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-d + e + n, d + n + r) := by
  have hq : (d * r - n * e - (1)) * (-2) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 - 2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_2_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-e + r, e + r) := by
  have hq : (d * r - n * e - (1)) * (2) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pP_3_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-d - e + n + r, d + e + n + r) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pQ_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (2*n, 2*d + 4*n) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 4*d^2 + 2*d*e + 8*d*n + 4*e*n - 4*n^2 - 2*n*r := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pQ_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : tCo ⟨2 * n + r, 2 * d + e⟩ (2*n, 2*d + 4*n) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (2*n, 2*d + 4*n) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2pQ_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (1)) * (0) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2pQ_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = 1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (2*n, 2*d + 4*n) := by
  have hq : (d * r - n * e - (1)) * (-2) = 0 := by
    rw [show d * r - n * e - (1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 4*d^2 + 2*d*e + 8*d*n + 4*e*n - 4*n^2 - 2*n*r - 2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (-1)) * (5) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + 3*d*e + 4*d*n + e^2 + 6*e*n + 2*e*r - 2*n^2 - 3*n*r - r^2 - 5 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n, d + n) := by
  have hq : (d * r - n * e - (-1)) * (4) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 - 4 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_2_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (r, e + 2*r) := by
  have hq : (d * r - n * e - (-1)) * (1) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d^2 + d*e + 4*d*n + 2*e*n - 2*n^2 - n*r - 1 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_3_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-d + n, d + n) := by
  have hq : (d * r - n * e - (-1)) * (-2) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_2_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (r, e + 2*r) := by
  have hq : (d * r - n * e - (-1)) * (6) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 - 6 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nP_3_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ ((0 : ℤ), (0 : ℤ)) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-d + n + r, d + e + n + 2*r) := by
  have hq : (d * r - n * e - (-1)) * (4) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 2*d*e + e^2 + 4*e*n + 2*e*r - 2*n*r - r^2 - 4 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nQ_0_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (2*d, 2*n) := by
  have hq : (d * r - n * e - (-1)) * (4) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 4*d^2 + 2*d*e + 8*d*n + 4*e*n - 4*n^2 - 2*n*r - 4 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nQ_1_t (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : tCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) ≤ tCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold tCo; dsimp only; linarith only [hq, hg]

theorem gr_2nQ_0_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (2*d, 2*n) := by
  have hq : (d * r - n * e - (-1)) * (6) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 4*d^2 + 2*d*e + 8*d*n + 4*e*n - 4*n^2 - 2*n*r - 6 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem gr_2nQ_1_s (n d e r : ℤ) (_hn : 1 ≤ n) (_hnd : n < d) (_hr : 1 ≤ r) (_hre : r < e)
    (hdet : d * r - n * e = -1) : sCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) ≤ sCo ⟨2 * n + r, 2 * d + e⟩ (-2*d + 2*n, 2*d + 2*n) := by
  have hq : (d * r - n * e - (-1)) * (0) = 0 := by
    rw [show d * r - n * e - (-1) = 0 by linarith only [hdet], zero_mul]
  have hg : 0 ≤ 0 := by nlinarith only [_hnd, _hr, _hre, _hn, mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < d + n by omega), mul_pos (show (0:ℤ) < n by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < e + r by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < e by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < r by omega) (show (0:ℤ) < n by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < d by omega), mul_pos (show (0:ℤ) < e - r by omega) (show (0:ℤ) < r by omega), mul_pos (show (0:ℤ) < d - n by omega) (show (0:ℤ) < n by omega)]
  unfold sCo; dsimp only; linarith only [hq, hg]

theorem pc_1pP_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((2*e, 2*r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((2*e : ℤ) + (2*r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-e + r : ℤ) + (e + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (2*e, 2*r) (-e + r, e + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (2*e, 2*r) (-e + r, e + r) (-e + r, e + r) hvev (gr_1pP_0_t n d e r hn hnd hr hre hdet) (gr_1pP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (-e + r, e + r) (-e + r, e + r) hvrev (gr_1pP_1_t n d e r hn hnd hr hre hdet) (gr_1pP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1pP_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((-e + r, e + r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-e + r : ℤ) + (e + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((2*e : ℤ) + (2*r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (2*e, 2*r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (-e + r, e + r) (-e + r, e + r) hvev (gr_1pP_1_t n d e r hn hnd hr hre hdet) (gr_1pP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (2*e, 2*r) (-e + r, e + r) (-e + r, e + r) hvrev (gr_1pP_0_t n d e r hn hnd hr hre hdet) (gr_1pP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1pQ_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ (((0 : ℤ), (0 : ℤ)) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  have hvrev : ((d + e + n : ℤ) + (d + 3*n + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (d + e + n, d + 3*n + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1pQ_0_t n d e r hn hnd hr hre hdet) (gr_1pQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + e + n, d + 3*n + r) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1pQ_3_t n d e r hn hnd hr hre hdet) (gr_1pQ_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1pQ_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((e, r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((e : ℤ) + (r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((d + n : ℤ) + (d + 3*n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (e, r) (d + n, d + 3*n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (e, r) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1pQ_1_t n d e r hn hnd hr hre hdet) (gr_1pQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + n, d + 3*n) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1pQ_2_t n d e r hn hnd hr hre hdet) (gr_1pQ_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1pQ_2 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((d + n, d + 3*n) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((d + n : ℤ) + (d + 3*n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((e : ℤ) + (r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + n, d + 3*n) (e, r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + n, d + 3*n) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1pQ_2_t n d e r hn hnd hr hre hdet) (gr_1pQ_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (e, r) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1pQ_1_t n d e r hn hnd hr hre hdet) (gr_1pQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1pQ_3 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((d + e + n, d + 3*n + r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((d + e + n : ℤ) + (d + 3*n + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ))
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (d + e + n, d + 3*n + r) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1pQ_3_t n d e r hn hnd hr hre hdet) (gr_1pQ_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (d + e + n, d + 3*n + r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1pQ_0_t n d e r hn hnd hr hre hdet) (gr_1pQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nP_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ (((0 : ℤ), (0 : ℤ)) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  have hvrev : ((e + r : ℤ) + (e + 3*r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (e + r, e + 3*r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (e + r, e + 3*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1nP_0_t n d e r hn hnd hr hre hdet) (gr_1nP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (e + r, e + 3*r) (e + r, e + 3*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1nP_1_t n d e r hn hnd hr hre hdet) (gr_1nP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nP_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((e + r, e + 3*r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((e + r : ℤ) + (e + 3*r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (e + r, e + 3*r) ((0 : ℤ), (0 : ℤ))
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ (e + r, e + 3*r) (e + r, e + 3*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_1nP_1_t n d e r hn hnd hr hre hdet) (gr_1nP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (e + r, e + 3*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_1nP_0_t n d e r hn hnd hr hre hdet) (gr_1nP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nQ_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((2*d, 2*n) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((2*d : ℤ) + (2*n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d + e + n : ℤ) + (d + n + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-d + e + n, d + n + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-d + n, d + n) (-d + n, d + n) hvev (gr_1nQ_0_t n d e r hn hnd hr hre hdet) (gr_1nQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + e + n, d + n + r) (-d + n, d + n) (-d + n, d + n) hvrev (gr_1nQ_3_t n d e r hn hnd hr hre hdet) (gr_1nQ_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nQ_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((2*d + e, 2*n + r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((2*d + e : ℤ) + (2*n + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d + n : ℤ) + (d + n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d + e, 2*n + r) (-d + n, d + n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d + e, 2*n + r) (-d + n, d + n) (-d + n, d + n) hvev (gr_1nQ_1_t n d e r hn hnd hr hre hdet) (gr_1nQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + n, d + n) (-d + n, d + n) (-d + n, d + n) hvrev (gr_1nQ_2_t n d e r hn hnd hr hre hdet) (gr_1nQ_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nQ_2 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((-d + n, d + n) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((-d + n : ℤ) + (d + n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((2*d + e : ℤ) + (2*n + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + n, d + n) (2*d + e, 2*n + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + n, d + n) (-d + n, d + n) (-d + n, d + n) hvev (gr_1nQ_2_t n d e r hn hnd hr hre hdet) (gr_1nQ_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d + e, 2*n + r) (-d + n, d + n) (-d + n, d + n) hvrev (gr_1nQ_1_t n d e r hn hnd hr hre hdet) (gr_1nQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_1nQ_3 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨1 * n + r, 1 * d + e⟩ ((-d + e + n, d + n + r) + w) := by
  have hμC : muOf ⟨1 * n + r, 1 * d + e⟩ = 2 := by
    apply muOf_mk_two; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((-d + e + n : ℤ) + (d + n + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((2*d : ℤ) + (2*n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + e + n, d + n + r) (2*d, 2*n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (-d + e + n, d + n + r) (-d + n, d + n) (-d + n, d + n) hvev (gr_1nQ_3_t n d e r hn hnd hr hre hdet) (gr_1nQ_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨1 * n + r, 1 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-d + n, d + n) (-d + n, d + n) hvrev (gr_1nQ_0_t n d e r hn hnd hr hre hdet) (gr_1nQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q1n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pP_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((e, r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((e : ℤ) + (r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d - e + n + r : ℤ) + (d + e + n + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (e, r) (-d - e + n + r, d + e + n + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (e, r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvev (gr_2pP_0_t n d e r hn hnd hr hre hdet) (gr_2pP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvrev (gr_2pP_3_t n d e r hn hnd hr hre hdet) (gr_2pP_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pP_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-d + e + n, d + n + r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-d + e + n : ℤ) + (d + n + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-e + r : ℤ) + (e + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + e + n, d + n + r) (-e + r, e + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + e + n, d + n + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvev (gr_2pP_1_t n d e r hn hnd hr hre hdet) (gr_2pP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvrev (gr_2pP_2_t n d e r hn hnd hr hre hdet) (gr_2pP_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pP_2 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-e + r, e + r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-e + r : ℤ) + (e + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d + e + n : ℤ) + (d + n + r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (-d + e + n, d + n + r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-e + r, e + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvev (gr_2pP_2_t n d e r hn hnd hr hre hdet) (gr_2pP_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + e + n, d + n + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvrev (gr_2pP_1_t n d e r hn hnd hr hre hdet) (gr_2pP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pP_3 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-d - e + n + r, d + e + n + r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-d - e + n + r : ℤ) + (d + e + n + r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((e : ℤ) + (r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d - e + n + r, d + e + n + r) (e, r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvev (gr_2pP_3_t n d e r hn hnd hr hre hdet) (gr_2pP_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (e, r) (-d - e + n + r, d + e + n + r) (-d - e + n + r, d + e + n + r) hvrev (gr_2pP_0_t n d e r hn hnd hr hre hdet) (gr_2pP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pQ_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ (((0 : ℤ), (0 : ℤ)) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  have hvrev : ((2*n : ℤ) + (2*d + 4*n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (2*n, 2*d + 4*n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (2*n, 2*d + 4*n) ((0 : ℤ), (0 : ℤ)) hvev (gr_2pQ_0_t n d e r hn hnd hr hre hdet) (gr_2pQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*n, 2*d + 4*n) (2*n, 2*d + 4*n) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2pQ_1_t n d e r hn hnd hr hre hdet) (gr_2pQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2pQ_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((2*n, 2*d + 4*n) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((2*n : ℤ) + (2*d + 4*n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*n, 2*d + 4*n) ((0 : ℤ), (0 : ℤ))
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*n, 2*d + 4*n) (2*n, 2*d + 4*n) ((0 : ℤ), (0 : ℤ)) hvev (gr_2pQ_1_t n d e r hn hnd hr hre hdet) (gr_2pQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2p n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ ((0 : ℤ), (0 : ℤ)) (2*n, 2*d + 4*n) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2pQ_0_t n d e r hn hnd hr hre hdet) (gr_2pQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2p n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nP_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ (((0 : ℤ), (0 : ℤ)) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d + n + r : ℤ) + (d + e + n + 2*r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (-d + n + r, d + e + n + 2*r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_2nP_0_t n d e r hn hnd hr hre hdet) (gr_2nP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n + r, d + e + n + 2*r) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2nP_3_t n d e r hn hnd hr hre hdet) (gr_2nP_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nP_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-d + n, d + n) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-d + n : ℤ) + (d + n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((r : ℤ) + (e + 2*r : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n, d + n) (r, e + 2*r)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n, d + n) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_2nP_1_t n d e r hn hnd hr hre hdet) (gr_2nP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (r, e + 2*r) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2nP_2_t n d e r hn hnd hr hre hdet) (gr_2nP_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nP_2 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((r, e + 2*r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((r : ℤ) + (e + 2*r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-d + n : ℤ) + (d + n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (r, e + 2*r) (-d + n, d + n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (r, e + 2*r) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_2nP_2_t n d e r hn hnd hr hre hdet) (gr_2nP_2_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n, d + n) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2nP_1_t n d e r hn hnd hr hre hdet) (gr_2nP_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nP_3 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨n, d⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-d + n + r, d + e + n + 2*r) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨n, d⟩ = 2 := muOf_mk_two n d (by omega)
  have hvev : ((-d + n + r : ℤ) + (d + e + n + 2*r : ℤ)) % 2 = 0 := by omega
  have hvrev : ((0 : ℤ) + (0 : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ))
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ (-d + n + r, d + e + n + 2*r) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvev (gr_2nP_3_t n d e r hn hnd hr hre hdet) (gr_2nP_3_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨n, d⟩ ((0 : ℤ), (0 : ℤ)) (-d + n + r, d + e + n + 2*r) ((0 : ℤ), (0 : ℤ)) hvrev (gr_2nP_0_t n d e r hn hnd hr hre hdet) (gr_2nP_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_P2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nQ_0 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((2*d, 2*n) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((2*d : ℤ) + (2*n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((-2*d + 2*n : ℤ) + (2*d + 2*n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-2*d + 2*n, 2*d + 2*n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) hvev (gr_2nQ_0_t n d e r hn hnd hr hre hdet) (gr_2nQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) hvrev (gr_2nQ_1_t n d e r hn hnd hr hre hdet) (gr_2nQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem pc_2nQ_1 (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    ∀ w : ℤ × ℤ, InH ⟨r, e⟩ w → InH ⟨2 * n + r, 2 * d + e⟩ ((-2*d + 2*n, 2*d + 2*n) + w) := by
  have hμC : muOf ⟨2 * n + r, 2 * d + e⟩ = 1 := by
    apply muOf_mk_one; omega
  have hμF : muOf ⟨r, e⟩ = 1 := muOf_mk_one r e (by omega)
  have hvev : ((-2*d + 2*n : ℤ) + (2*d + 2*n : ℤ)) % 2 = 0 := by omega
  have hvrev : ((2*d : ℤ) + (2*n : ℤ)) % 2 = 0 := by omega
  exact piece_sub ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (-2*d + 2*n, 2*d + 2*n) (2*d, 2*n)
    (fun w => by unfold FLatticePaper.Tiles.EncUpper.refl; rw [hμC, hμF]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring)
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) hvev (gr_2nQ_1_t n d e r hn hnd hr hre hdet) (gr_2nQ_1_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2n n d e r hn hnd hr hre hdet hodd heven w hw))
    (lowOK_origin ⟨2 * n + r, 2 * d + e⟩ ⟨r, e⟩ (2*d, 2*n) (-2*d + 2*n, 2*d + 2*n) (-2*d + 2*n, 2*d + 2*n) hvrev (gr_2nQ_0_t n d e r hn hnd hr hre hdet) (gr_2nQ_0_s n d e r hn hnd hr hre hdet) (fun w hw => fam_Q2n n d e r hn hnd hr hre hdet hodd heven w hw))

theorem encEven_F (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    evenChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ ⊆ HSet ⟨2 * n + r, 2 * d + e⟩ := by
  intro z hz
  simp only [evenChildS, Set.mem_union] at hz
  rcases hz with ((((h0 | h1) | h2) | h3) | h4) | h5
  · exact mem_zero_piece _ _ (pc_2pQ_0 n d e r hn hnd hr hre hdet hodd heven) z h0
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2pQ_1 n d e r hn hnd hr hre hdet hodd heven) z h1
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even; rfl) (pc_2pP_0 n d e r hn hnd hr hre hdet hodd heven) z h2
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2pP_1 n d e r hn hnd hr hre hdet hodd heven) z h3
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk.injEq]; constructor <;> ring) (pc_2pP_2 n d e r hn hnd hr hre hdet hodd heven) z h4
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2pP_3 n d e r hn hnd hr hre hdet hodd heven) z h5

theorem encEven_T (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    evenChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ ⊆ HSet ⟨2 * n + r, 2 * d + e⟩ := by
  intro z hz
  simp only [evenChildS, Set.mem_union] at hz
  rcases hz with ((((h0 | h1) | h2) | h3) | h4) | h5
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd; rfl) (pc_2nQ_0 n d e r hn hnd hr hre hdet hodd heven) z h0
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2nQ_1 n d e r hn hnd hr hre hdet hodd heven) z h1
  · exact mem_zero_piece _ _ (pc_2nP_0 n d e r hn hnd hr hre hdet hodd heven) z h2
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk.injEq]; constructor <;> ring) (pc_2nP_1 n d e r hn hnd hr hre hdet hodd heven) z h3
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2nP_2 n d e r hn hnd hr hre hdet hodd heven) z h4
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_2nP_3 n d e r hn hnd hr hre hdet hodd heven) z h5

theorem encOdd_F (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    oddChildS false (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ ⊆ HSet ⟨1 * n + r, 1 * d + e⟩ := by
  intro z hz
  simp only [oddChildS, Set.mem_union] at hz
  rcases hz with ((((h0 | h1) | h2) | h3) | h4) | h5
  · exact mem_zero_piece _ _ (pc_1pQ_0 n d e r hn hnd hr hre hdet hodd heven) z h0
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even; rfl) (pc_1pQ_1 n d e r hn hnd hr hre hdet hodd heven) z h1
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_1pQ_2 n d e r hn hnd hr hre hdet hodd heven) z h2
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_1pQ_3 n d e r hn hnd hr hre hdet hodd heven) z h3
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_1pP_0 n d e r hn hnd hr hre hdet hodd heven) z h4
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk.injEq]; constructor <;> ring) (pc_1pP_1 n d e r hn hnd hr hre hdet hodd heven) z h5

theorem encOdd_T (n d e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0) :
    oddChildS true (HSet ⟨n, d⟩) (HSet ⟨r, e⟩) ⟨n, d⟩ ⟨r, e⟩ ⊆ HSet ⟨1 * n + r, 1 * d + e⟩ := by
  intro z hz
  simp only [oddChildS, Set.mem_union] at hz
  rcases hz with ((((h0 | h1) | h2) | h3) | h4) | h5
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd; rfl) (pc_1nQ_0 n d e r hn hnd hr hre hdet hodd heven) z h0
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Odd texV1Even; rfl) (pc_1nQ_1 n d e r hn hnd hr hre hdet hodd heven) z h1
  · exact mem_shift_piece _ _ _ _ (by unfold texV2; simp only [Prod.mk.injEq]; constructor <;> ring) (pc_1nQ_2 n d e r hn hnd hr hre hdet hodd heven) z h2
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_1nQ_3 n d e r hn hnd hr hre hdet hodd heven) z h3
  · exact mem_zero_piece _ _ (pc_1nP_0 n d e r hn hnd hr hre hdet hodd heven) z h4
  · exact mem_shift_piece _ _ _ _ (by unfold texV1Even texV2; simp only [Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring) (pc_1nP_1 n d e r hn hnd hr hre hdet hodd heven) z h5

/-- The even-child inclusion for every proper pair (the field `encEven` of `PairHyps`). -/
theorem encEven_all (p q : Fraction) (h : ParPair p q) :
    evenChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q ⊆ HSet ((Parents.mk p q).current .even) := by
  obtain ⟨pn, pd⟩ := p
  obtain ⟨qn, qd⟩ := q
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  have hC : (Parents.mk ⟨pn, pd⟩ ⟨qn, qd⟩).current .even = ⟨2 * pn + qn, 2 * pd + qd⟩ := by
    simp [Parents.current, Parents.combine]
  rw [hC]
  have hodd : (pn + pd) % 2 = 1 := h5
  have heven : (qn + qd) % 2 = 0 := h6
  rcases h7 with hD | hD
  · have hδ : pd * qn - pn * qd = -1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_true (show Fraction.det ⟨pn, pd⟩ ⟨qn, qd⟩ = 1 from hD)]
    exact encEven_T pn pd qd qn (by omega) h2 (by omega) h4 hδ (by omega) (by omega)
  · have hδ : pd * qn - pn * qd = 1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_false (by intro hc; simp only [Fraction.det] at hc; linarith)]
    exact encEven_F pn pd qd qn (by omega) h2 (by omega) h4 hδ (by omega) (by omega)

/-- The odd-child inclusion for every proper pair (the field `encOdd` of `PairHyps`). -/
theorem encOdd_all (p q : Fraction) (h : ParPair p q) :
    oddChildS (decide (p.det q = 1)) (HSet p) (HSet q) p q ⊆ HSet ((Parents.mk p q).current .odd) := by
  obtain ⟨pn, pd⟩ := p
  obtain ⟨qn, qd⟩ := q
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  have hC : (Parents.mk ⟨pn, pd⟩ ⟨qn, qd⟩).current .odd = ⟨1 * pn + qn, 1 * pd + qd⟩ := by
    simp [Parents.current, Parents.combine]
  rw [hC]
  have hodd : (pn + pd) % 2 = 1 := h5
  have heven : (qn + qd) % 2 = 0 := h6
  rcases h7 with hD | hD
  · have hδ : pd * qn - pn * qd = -1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_true (show Fraction.det ⟨pn, pd⟩ ⟨qn, qd⟩ = 1 from hD)]
    exact encOdd_T pn pd qd qn (by omega) h2 (by omega) h4 hδ (by omega) (by omega)
  · have hδ : pd * qn - pn * qd = 1 := by
      simp only [Fraction.det] at hD; linarith
    rw [decide_eq_false (by intro hc; simp only [Fraction.det] at hc; linarith)]
    exact encOdd_F pn pd qd qn (by omega) h2 (by omega) h4 hδ (by omega) (by omega)

end FLatticePaper.Tiles.EncPieces
