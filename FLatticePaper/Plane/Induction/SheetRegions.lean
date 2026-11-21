import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.Binary

/-! The sheet regions: the zero and harmonic windows of the sheets `A` and `C` of the odd parent, through the
quarter-turn `Z(x, y) = (−y, x − 1)`. Each window bound reduces, by the relation `N d − D n = ε` and the
bounds `1 ≤ N < D`, `2N ≤ n`, `2D ≤ d`, to a polynomial inequality in `D, n, d` proved by `nlinarith`. -/

namespace FLatticePaper.Induction
open Farey

/-! ### The quarter-turn of a standard field -/

private theorem sr_mapSite_neg (x : Site) :
    QuarterTurn.counterclockwise.mapSite (0, -1) x = (-x.2, x.1 - 1) := by
  ext <;> simp [QuarterTurn.mapSite, QuarterTurn.turn, sub_eq_add_neg]

/-- The harmonic grid is antisymmetric under the quarter-turn: `h₀(Zx) + h₀(x) = 0`. -/
theorem harmonicGrid_quarterTurn (x : Site) :
    harmonicGrid (QuarterTurn.counterclockwise.mapSite (0, -1) x) + harmonicGrid x = 0 := by
  have h1 := harmonicGrid_exact (QuarterTurn.counterclockwise.mapSite (0, -1) x)
  have h2 := harmonicGrid_exact x
  rw [sr_mapSite_neg] at h1 ⊢
  dsimp only at h1
  have hpar : (-x.2 + (x.1 - 1)) % 2 + (x.1 + x.2) % 2 = 1 := by omega
  have hsum : 4 * (harmonicGrid (-x.2, x.1 - 1) + harmonicGrid x) = 0 := by
    linear_combination h1 + h2 - hpar
  omega

theorem quarterTurnField_eq_zero {conj : ChildFrame} {G : Field} (hG : conj.HasStrips G) {x : Site}
    (hlo : 1 - 2 * conj.child.den ≤ conj.sGrade (QuarterTurn.counterclockwise.mapSite (0, -1) x))
    (hhi : conj.sGrade (QuarterTurn.counterclockwise.mapSite (0, -1) x) ≤ 2 * (conj.child.den + conj.child.num) - 1) :
    quarterTurnField G x = 0 := by
  unfold quarterTurnField
  rw [hG.2 _ hlo hhi]
  linarith [harmonicGrid_quarterTurn x]

theorem quarterTurnField_eq_harmonic {conj : ChildFrame} {G : Field} (hG : conj.HasStrips G) {x : Site}
    (hlo : 1 - conj.child.den ≤ conj.tGrade (QuarterTurn.counterclockwise.mapSite (0, -1) x))
    (hhi : conj.tGrade (QuarterTurn.counterclockwise.mapSite (0, -1) x) ≤ conj.child.num + 2 * conj.child.den - 1) :
    quarterTurnField G x = harmonicGrid x := by
  unfold quarterTurnField
  rw [hG.1 _ hlo hhi, zero_add]

/-! ### Arithmetic of the windows -/


theorem srQ_A1e (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n - D*n^2 - d^2 + d*n + d - n := by
  nlinarith

theorem srQ_A1o (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n - D*n^2 - 2*d^2 + 2*d*n + 3*d - n := by
  nlinarith

theorem srQ_B1e (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^3 + 2*D*d^2*n + 2*D*d^2 - D*d*n^2 + 4*D*d*n - 2*D*n^2 - d^3 - 2*d^2*n + d*n^2 + 2*d - 2*n := by
  nlinarith

theorem srQ_B1o (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^3 + 3*D*d^2*n + D*d*n^2 - D*n^3 - d^3 - 2*d^2*n - d^2 + d*n^2 + 2*d*n + 2*d - n^2 := by
  nlinarith

theorem srQ_A2e (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n - D*n^2 + d^2 - 3*d*n - d + n := by
  nlinarith

theorem srQ_A2o (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n - D*n^2 - 2*d*n + d + n := by
  nlinarith

theorem srQ_B2e (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^3 + 2*D*d^2*n + 2*D*d^2 - D*d*n^2 + 4*D*d*n - 2*D*n^2 - d^3 - 2*d^2*n + d*n^2 - 2*d*n - 2*d + 2*n := by
  nlinarith

theorem srQ_B2o (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^3 + 3*D*d^2*n + D*d*n^2 - D*n^3 - d^3 - 2*d^2*n - d^2 + d*n^2 - 2*d*n + 2*d + n^2 := by
  nlinarith

theorem srQ_A3e (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 - 4*d*n + 2*n^2 + 4 := by
  nlinarith

theorem srQ_A3o (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^3 + 3*D*d^2*n + 2*D*d^2 + D*d*n^2 + 4*D*d*n - D*n^3 - 2*D*n^2 - 2*d^3 - 4*d^2*n - d^2 + 2*d*n^2 + 4*d*n + 2*d - n^2 - 2*n := by
  nlinarith

theorem srQ_B3e (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 + 2*d*n + 6*d - 2*n := by
  nlinarith

theorem srQ_B3o (D n d : ℤ) (hc1 : d ≤ D*n + 1) (_hc2 : D*n + 1 ≤ D*d - d) (_hc3 : 2*(D*n+1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 + 4*d*n + 2*d - 2*n := by
  nlinarith

theorem srQ_A4e (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^4 + 4*D*d^3*n - 2*D*d^2*n^2 - 2*d^4 - 4*d^3*n - 2*d^3 + 2*d^2*n^2 - 2*d^2*n + 4*d^2 := by
  have hT : d^2 ≤ d^2 + 2*d*n - n^2 := by nlinarith
  have hX : 0 < (D-1)*(d^2 + 2*d*n - n^2) - (d + n - 2) := by nlinarith
  have hfac : 2*D*d^4 + 4*D*d^3*n - 2*D*d^2*n^2 - 2*d^4 - 4*d^3*n - 2*d^3 + 2*d^2*n^2 - 2*d^2*n + 4*d^2
      = 2*d^2*((D-1)*(d^2 + 2*d*n - n^2) - (d + n - 2)) := by ring
  rw [hfac]
  have hd2 : 0 < d^2 := by positivity
  exact mul_pos (mul_pos (by norm_num) hd2) hX

theorem srQ_A4o (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < D*d^4 + 3*D*d^3*n + 2*D*d^3 + D*d^2*n^2 + 4*D*d^2*n - D*d*n^3 - 2*D*d*n^2 - 2*d^4 - 4*d^3*n - d^3 + 2*d^2*n^2 - 2*d^2*n - 2*d^2 + d*n^2 + 2*d*n := by
  have hT : d^2 ≤ d^2 + 2*d*n - n^2 := by nlinarith
  have hTpos : 0 < d^2 + 2*d*n - n^2 := by nlinarith
  have hL : 0 ≤ (D-2)*((d^2 + 2*d*n - n^2)*(d + n + 2)) := mul_nonneg (by omega) (by positivity)
  have hbr : 0 < 2*(d^2 + 2*d*n - n^2)*(n+2) - (d^2 + 2*d*n + 2*d - n^2 - 2*n) := by nlinarith
  have hY : 0 < D*(d^2 + 2*d*n - n^2)*(d+n+2) - 2*d*(d^2 + 2*d*n - n^2) - (d^2 + 2*d*n + 2*d - n^2 - 2*n) := by nlinarith
  have hfac : D*d^4 + 3*D*d^3*n + 2*D*d^3 + D*d^2*n^2 + 4*D*d^2*n - D*d*n^3 - 2*D*d*n^2 - 2*d^4 - 4*d^3*n - d^3 + 2*d^2*n^2 - 2*d^2*n - 2*d^2 + d*n^2 + 2*d*n
      = d*(D*(d^2 + 2*d*n - n^2)*(d+n+2) - 2*d*(d^2 + 2*d*n - n^2) - (d^2 + 2*d*n + 2*d - n^2 - 2*n)) := by ring
  rw [hfac]
  exact mul_pos (by omega) hY

theorem srQ_B4e (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^3 + 4*D*d^2*n - 2*D*d*n^2 - 4*d^2*n + 2*d^2 + 2*d*n := by
  nlinarith

theorem srQ_B4o (D n d : ℤ) (hc1 : d ≤ D*n - 1) (_hc2 : D*n - 1 ≤ D*d - d) (_hc3 : 2*(D*n-1) ≤ n*d) (hD2 : 2 ≤ D) (hc4 : 2*D ≤ d) (_hn : 1 ≤ n) (_hnd : n + 2 ≤ d) (_hd : 3 ≤ d) :
    0 < 2*D*d^3 + 4*D*d^2*n - 2*D*d*n^2 - 2*d^2*n - 2*d^2 + 2*d*n := by
  nlinarith

theorem srP_A1e (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A1e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n) = D*d^2 + 2*D*d*n - D*n^2 - d^2 + d*n + d - n := by
    linear_combination (-d^2 + d*n + d - n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A1o (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d + n + 2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A1o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d + n + 2) = D*d^2 + 2*D*d*n - D*n^2 - 2*d^2 + 2*d*n + 3*d - n := by
    linear_combination (-d^2 + d*n + d - n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d + n + 2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B1e (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2 - 2*n := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B1e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2 - 2*n) = D*d^3 + 2*D*d^2*n + 2*D*d^2 - D*d*n^2 + 4*D*d*n - 2*D*n^2 - d^3 - 2*d^2*n + d*n^2 + 2*d - 2*n := by
    linear_combination (2*d*n + 2*d - 2*n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2 - 2*n) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B1o (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 - n + 2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B1o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 - n + 2) = D*d^3 + 3*D*d^2*n + D*d*n^2 - D*n^3 - d^3 - 2*d^2*n - d^2 + d*n^2 + 2*d*n + 2*d - n^2 := by
    linear_combination (3*d*n - n^2) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 - n + 2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A3e (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 - 4*d*n + 2*n^2 + 4 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A3e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 - 4*d*n + 2*n^2 + 4 = 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 - 4*d*n + 2*n^2 + 4 := by ring
  rw [hX]; exact hQ

theorem srP_A3o (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d^2 + 4*D*d*n + 2*D*d - D*n^2 + 2*D*n - N*d^2 + 2*N*d*n + 2*N*d - N*n^2 - 2*N*n - 2*d^2 - 4*d*n + 2*n^2 + 2*n := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A3o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d^2 + 4*D*d*n + 2*D*d - D*n^2 + 2*D*n - N*d^2 + 2*N*d*n + 2*N*d - N*n^2 - 2*N*n - 2*d^2 - 4*d*n + 2*n^2 + 2*n) = D*d^3 + 3*D*d^2*n + 2*D*d^2 + D*d*n^2 + 4*D*d*n - D*n^3 - 2*D*n^2 - 2*d^3 - 4*d^2*n - d^2 + 2*d*n^2 + 4*d*n + 2*d - n^2 - 2*n := by
    linear_combination (-d^2 + 2*d*n + 2*d - n^2 - 2*n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d^2 + 4*D*d*n + 2*D*d - D*n^2 + 2*D*n - N*d^2 + 2*N*d*n + 2*N*d - N*n^2 - 2*N*n - 2*d^2 - 4*d*n + 2*n^2 + 2*n) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B3e (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < 2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d - 2*n + 4 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B3e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d - 2*n + 4) = 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 + 2*d*n + 6*d - 2*n := by
    linear_combination (4*d*n + 2*d - 2*n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d - 2*n + 4) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B3o (N D n d : ℤ) (hrel : N*d = D*n + 1) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < 2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + 1 := by rw [← hrel]; nlinarith
  have hc2 : D*n + 1 ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + 1) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B3o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d) = 2*D*d^2 + 4*D*d*n - 2*D*n^2 - 2*d^2 + 4*d*n + 2*d - 2*n := by
    linear_combination (4*d*n + 2*d - 2*n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (2*D*d - 4*D*n^2 + 2*D*n + 4*N*d*n + 2*N*d - 2*N*n - 2*d) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A2e (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - 2*n := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A2e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - 2*n) = D*d^2 + 2*D*d*n - D*n^2 + d^2 - 3*d*n - d + n := by
    linear_combination (-d^2 + d*n + d - n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - 2*n) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A2o (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d - n + 2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A2o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d - n + 2) = D*d^2 + 2*D*d*n - D*n^2 - 2*d*n + d + n := by
    linear_combination (-d^2 + d*n + d - n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d*n + D*d - D*n^2 + D*n - N*d^2 + N*d*n + N*d - N*n - d - n + 2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B2e (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B2e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2) = D*d^3 + 2*D*d^2*n + 2*D*d^2 - D*d*n^2 + 4*D*d*n - 2*D*n^2 - d^3 - 2*d^2*n + d*n^2 - 2*d*n - 2*d + 2*n := by
    linear_combination (2*d*n + 2*d - 2*n) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d^2 + 2*D*d*n + 2*D*d - 3*D*n^2 + 2*D*n + 2*N*d*n + 2*N*d - 2*N*n - d^2 - 2*d*n + n^2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B2o (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 + n + 2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B2o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^1 * (D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 + n + 2) = D*d^3 + 3*D*d^2*n + D*d*n^2 - D*n^3 - d^3 - 2*d^2*n - d^2 + d*n^2 - 2*d*n + 2*d + n^2 := by
    linear_combination (3*d*n - n^2) * hrel
  have hdm : 0 < d^1 := by positivity
  have hprod : 0 < d^1 * (D*d^2 + 3*D*d*n - 2*D*n^2 + 3*N*d*n - N*n^2 - d^2 - 2*d*n - d + n^2 + n + 2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A4e (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < -4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + 2*D*d^2 + 4*D*d*n + 4*D*d - 2*D*n^2 + 4*D*n + 4*N^2*d^2 - 4*N^2*d*n + 4*N*d - 4*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2 - 2*n + 4 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A4e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^2 * (-4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + 2*D*d^2 + 4*D*d*n + 4*D*d - 2*D*n^2 + 4*D*n + 4*N^2*d^2 - 4*N^2*d*n + 4*N*d - 4*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2 - 2*n + 4) = 2*D*d^4 + 4*D*d^3*n - 2*D*d^2*n^2 - 2*d^4 - 4*d^3*n - 2*d^3 + 2*d^2*n^2 - 2*d^2*n + 4*d^2 := by
    linear_combination (4*D*d^3 + 4*D*d^2*n + 4*N*d^3 - 4*N*d^2*n) * hrel
  have hdm : 0 < d^2 := by positivity
  have hprod : 0 < d^2 * (-4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + 2*D*d^2 + 4*D*d*n + 4*D*d - 2*D*n^2 + 4*D*n + 4*N^2*d^2 - 4*N^2*d*n + 4*N*d - 4*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2 - 2*n + 4) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_A4o (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < -4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + D*d^2 + 4*D*d*n + 6*D*d - D*n^2 + 6*D*n + 4*N^2*d^2 - 4*N^2*d*n - N*d^2 + 2*N*d*n + 6*N*d - N*n^2 - 6*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_A4o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^2 * (-4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + D*d^2 + 4*D*d*n + 6*D*d - D*n^2 + 6*D*n + 4*N^2*d^2 - 4*N^2*d*n - N*d^2 + 2*N*d*n + 6*N*d - N*n^2 - 6*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2) = D*d^4 + 3*D*d^3*n + 2*D*d^3 + D*d^2*n^2 + 4*D*d^2*n - D*d*n^3 - 2*D*d*n^2 - 2*d^4 - 4*d^3*n - d^3 + 2*d^2*n^2 - 2*d^2*n - 2*d^2 + d*n^2 + 2*d*n := by
    linear_combination (4*D*d^3 + 4*D*d^2*n + 4*N*d^3 - 4*N*d^2*n - d^3 + 2*d^2*n + 2*d^2 - d*n^2 - 2*d*n) * hrel
  have hdm : 0 < d^2 := by positivity
  have hprod : 0 < d^2 * (-4*D^2*d*n - 4*D^2*n^2 + 4*D*N*d^2 + 4*D*N*n^2 + D*d^2 + 4*D*d*n + 6*D*d - D*n^2 + 6*D*n + 4*N^2*d^2 - 4*N^2*d*n - N*d^2 + 2*N*d*n + 6*N*d - N*n^2 - 6*N*n - 2*d^2 - 4*d*n - 2*d + 2*n^2) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B4e (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < 4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 4 := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B4e D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^2 * (4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 4) = 2*D*d^3 + 4*D*d^2*n - 2*D*d*n^2 - 4*d^2*n + 2*d^2 + 2*d*n := by
    linear_combination (-4*D*d^3 - 4*D*d^2*n - 4*N*d^3 + 4*N*d^2*n + 4*d^2*n + 2*d^2 - 2*d*n) * hrel
  have hdm : 0 < d^2 := by positivity
  have hprod : 0 < d^2 * (4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 4) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le

theorem srP_B4o (N D n d : ℤ) (hrel : N*d = D*n + (-1)) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D)
    (h2N : 2*N ≤ n) (h2D : 2*D ≤ d) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) :
    0 < 4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 2*n := by
  have hD2 : 2 ≤ D := by omega
  have hc1 : d ≤ D*n + (-1) := by rw [← hrel]; nlinarith
  have hc2 : D*n + (-1) ≤ D*d - d := by rw [← hrel]; nlinarith
  have hc3 : 2*(D*n + (-1)) ≤ n*d := by rw [← hrel]; nlinarith
  have hQ := srQ_B4o D n d hc1 hc2 hc3 hD2 h2D hn hnd hd
  have hX : d^2 * (4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 2*n) = 2*D*d^3 + 4*D*d^2*n - 2*D*d*n^2 - 2*d^2*n - 2*d^2 + 2*d*n := by
    linear_combination (-4*D*d^3 - 4*D*d^2*n - 4*N*d^3 + 4*N*d^2*n + 4*d^2*n + 2*d^2 - 2*d*n) * hrel
  have hdm : 0 < d^2 := by positivity
  have hprod : 0 < d^2 * (4*D^2*d*n + 4*D^2*n^2 - 4*D*N*d^2 - 4*D*N*n^2 - 2*D*d - 4*D*n^2 - 2*D*n - 4*N^2*d^2 + 4*N^2*d*n + 4*N*d*n - 2*N*d + 2*N*n + 2*n) := by rw [hX]; exact hQ
  exact pos_of_mul_pos_right hprod hdm.le


/-! Core region lemmas: the bounds on `C t ± s` and `2t + C s`, and on the shifted sheet, from the
parity rectangle `E` (even and odd branches) and the arithmetic of the P-lemmas. -/

theorem sr_core_low_eps1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n + 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2))
    (ht : 1 - d ≤ t) : -(D*T) < (D*(d+n) + N*(d-n))*t + s := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  have hCt := mul_le_mul_of_nonneg_left ht hC
  rcases hE with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -⟩
  · have := srP_A1e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have := srP_A1o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

theorem sr_core_up_eps1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n + 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)) :
    (D*(d+n) + N*(d-n))*t + s < (N + 2*D)*T := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  rcases hE with ⟨-, h2, -, h4⟩ | ⟨-, h2, -, h4⟩
  · have hCt := mul_le_mul_of_nonneg_left h2 hC
    have := srP_B1e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC
    have := srP_B1o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

theorem sr_core_low_epsm1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n - 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2))
    (ht : 1 - d ≤ t) : -(D*T) < (D*(d+n) + N*(d-n))*t - s + T := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  have hCt := mul_le_mul_of_nonneg_left ht hC
  rcases hE with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩
  · have := srP_A2e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have := srP_A2o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

theorem sr_core_up_epsm1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n - 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)) :
    (D*(d+n) + N*(d-n))*t - s + T < (N + 2*D)*T := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  rcases hE with ⟨-, h2, h3, -⟩ | ⟨-, h2, h3, -⟩
  · have hCt := mul_le_mul_of_nonneg_left h2 hC
    have := srP_B2e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have hCt := mul_le_mul_of_nonneg_left h2 hC
    have := srP_B2o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

theorem sr_core_low_harm1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n + 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)) :
    -(2*D*T) < 2*t + (D*(d+n) + N*(d-n))*s := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  rcases hE with ⟨h1, -, h3, -⟩ | ⟨h1, -, h3, -⟩
  · have hCs := mul_le_mul_of_nonneg_left h3 hC
    have := srP_A3e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have hCs := mul_le_mul_of_nonneg_left h3 hC
    have := srP_A3o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

theorem sr_core_up_harm1 (N D n d T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n + 1) (hT : T = d^2 + 2*d*n - n^2)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2))
    (hs2 : s ≤ 2*(d+n) - 2) :
    2*t + (D*(d+n) + N*(d-n))*s < (2*D + 2*N)*T := by
  subst hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  have hCs := mul_le_mul_of_nonneg_left hs2 hC
  rcases hE with ⟨-, h2, -, -⟩ | ⟨-, h2, -, -⟩
  · have := srP_B3e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have := srP_B3o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

/-! The odd parent `0/1`: the child `1/d`, with the sibling `1/1` and `ε = -1`. -/

theorem sr_N0_low (N D n d T t s : ℤ) (hN : N = 0) (hD : D = 1) (hn : n = 1)
    (hT : T = d^2 + 2*d*n - n^2) (hd : 3 ≤ d)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2))
    (ht : 1 - d ≤ t) : -(D*T) < (D*(d+n) + N*(d-n))*t - s + T := by
  subst hN hD hn
  subst hT
  have hd1 : (0:ℤ) ≤ d + 1 := by omega
  have hct := mul_le_mul_of_nonneg_left ht hd1
  rcases hE with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩
  · nlinarith
  · nlinarith

theorem sr_N0_up (N D n d T t s : ℤ) (hN : N = 0) (hD : D = 1) (hn : n = 1)
    (hT : T = d^2 + 2*d*n - n^2) (hd : 3 ≤ d)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)) :
    (D*(d+n) + N*(d-n))*t - s + T < (N + 2*D)*T := by
  subst hN hD hn
  subst hT
  have hd1 : (0:ℤ) ≤ d + 1 := by omega
  rcases hE with ⟨-, h2, h3, -⟩ | ⟨-, h2, h3, -⟩
  · have hct := mul_le_mul_of_nonneg_left h2 hd1
    nlinarith
  · have hct := mul_le_mul_of_nonneg_left h2 hd1
    nlinarith


/-! ### The frame data of a sheet -/

private theorem sr_child_num (frame : ChildFrame) :
    frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

private theorem sr_child_den (frame : ChildFrame) :
    frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
  simp [ChildFrame.child, Parents.current, Parents.combine]

private theorem sr_eps_def (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den :=
  rfl

private theorem sr_eps_eq (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num :=
  frame.eps_eq

private theorem sr_shift (frame : ChildFrame) :
    frame.sheetShift = ((1 - frame.phaseW) * frame.parents.even.den, (1 - frame.phaseW) * frame.parents.even.num) := by
  ext <;> simp [ChildFrame.sheetShift, Fraction.unmodifiedDeck]

private theorem sr_offset (frame : ChildFrame) :
    frame.sheetOffset = (frame.parents.even.num - frame.parents.even.den + frame.eps * frame.parents.even.den,
      frame.parents.even.num + frame.parents.even.den + frame.eps * frame.parents.even.num) := by
  ext <;> simp [ChildFrame.sheetOffset, Fraction.unmodifiedDeck]

/-- The parity rectangle `E` in the grades `t`, `s`, in the two parity branches. -/
private theorem sr_E_disj (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) :
    (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧
      0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∨
    (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
  rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

private theorem sr_conj (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate) :
    conj.child.num = frame.parents.odd.den - frame.parents.odd.num ∧
      conj.child.den = frame.parents.odd.den + frame.parents.odd.num := by
  rw [hconj, Fraction.rotate_of_odd frame.valid.odd_parity]
  exact ⟨rfl, rfl⟩

/-- The `s`-grade of the child is even, so `s ≤ 2L − 1` gives `s ≤ 2L − 2`. -/
private theorem sr_sGrade_le (frame : ChildFrame) {z : Site}
    (hs : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 := by
  have hev := frame.child_even
  unfold Fraction.Even at hev
  obtain ⟨m, hm⟩ : ∃ m, frame.child.den + frame.child.num = 2 * m := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨k, hk'⟩ : ∃ k, frame.sGrade z = 2 * k := by
    refine ⟨m * z.1 + (m - frame.child.num) * z.2, ?_⟩
    unfold ChildFrame.sGrade
    linear_combination (z.1 + z.2) * hm
  omega

/-- The identity `T · t_p = C t + ε s`, the parent's grade in the child's coordinates. -/
private theorem sr_tp_identity (frame : ChildFrame) (z : Site) :
    frame.child.periodDenominator * (frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2) =
      (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.tGrade z
        + (frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num) * frame.sGrade z := by
  unfold ChildFrame.tGrade ChildFrame.sGrade Fraction.periodDenominator
  ring

/-- The identity `T · s_p = 2ε t + C s`, the parent's `s`-grade in the child's coordinates. -/
private theorem sr_sp_identity (frame : ChildFrame) (x : Site) :
    frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * x.1
          + (frame.parents.odd.den - frame.parents.odd.num) * x.2) =
      2 * (frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num) * frame.tGrade x
        + (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.sGrade x := by
  unfold ChildFrame.tGrade ChildFrame.sGrade Fraction.periodDenominator
  ring

/-- The sheet's `u = t_p(z − shift)` lies in the zero-strip window `[1 − D, N + 2D − 1]`. -/
private theorem sr_u_bounds (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon)
    (ht : 1 - frame.child.den ≤ frame.tGrade z) :
    1 - frame.parents.odd.den ≤ frame.parents.odd.num * (z.1 - frame.sheetShift.1)
        - frame.parents.odd.den * (z.2 - frame.sheetShift.2) ∧
      frame.parents.odd.num * (z.1 - frame.sheetShift.1)
        - frame.parents.odd.den * (z.2 - frame.sheetShift.2) ≤ frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hn := sr_child_num frame
  have hd := sr_child_den frame
  obtain ⟨hnpos, hnd, hdiff, hd3, hTdef⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator :=
    Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hE := sr_E_disj frame hz
  have hdef := sr_eps_def frame
  have heps := sr_eps_eq frame
  have hid0 := sr_tp_identity frame z
  rcases frame.eps_unit with he | he
  · -- ε = 1: the shift vanishes and `u = t_p(z)`
    have hW : frame.phaseW = 1 := by
      rcases frame.phaseW_cases with ⟨-, h⟩ | ⟨h', -⟩
      · exact h
      · rw [he] at h'; norm_num at h'
    have hsh1 : frame.sheetShift.1 = 0 := by rw [sr_shift, hW]; simp
    have hsh2 : frame.sheetShift.2 = 0 := by rw [sr_shift, hW]; simp
    rw [hsh1, hsh2, sub_zero, sub_zero]
    have hdN : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
      rw [← heps]; exact he
    rw [hdN, one_mul] at hid0
    have hN1 : 1 ≤ frame.parents.odd.num := by
      by_contra h
      have h0 : frame.parents.odd.num = 0 := by omega
      rw [h0] at hdef
      nlinarith [mul_nonneg hnq0 hDpos.le]
    have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
    have h2N : 2 * frame.parents.odd.num ≤ frame.child.num := by omega
    have h2D : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
    have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num + 1 := by
      linarith
    have hlow := sr_core_low_eps1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE ht
    have hup := sr_core_up_eps1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE
    generalize frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2 = u at hid0 ⊢
    have h1 : frame.child.periodDenominator * (-frame.parents.odd.den) < frame.child.periodDenominator * u := by
      rw [hid0]; linarith
    have h2 : frame.child.periodDenominator * u < frame.child.periodDenominator * (frame.parents.odd.num + 2 * frame.parents.odd.den) := by
      rw [hid0]; linarith
    have l1 := lt_of_mul_lt_mul_left h1 hTpos.le
    have l2 := lt_of_mul_lt_mul_left h2 hTpos.le
    have l1' := Int.add_one_le_iff.mpr l1
    have l2' := Int.add_one_le_iff.mpr l2
    constructor <;> linarith
  · -- ε = -1: the shift is the even sibling's kernel `(dq, nq)`
    have hW : frame.phaseW = 0 := by
      rcases frame.phaseW_cases with ⟨h', -⟩ | ⟨-, h⟩
      · rw [he] at h'; norm_num at h'
      · exact h
    have hsh1 : frame.sheetShift.1 = frame.parents.even.den := by rw [sr_shift, hW]; simp
    have hsh2 : frame.sheetShift.2 = frame.parents.even.num := by rw [sr_shift, hW]; simp
    rw [hsh1, hsh2]
    have hdq' : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = -1 := by
      rw [← hdef]; exact he
    have hdN : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
      rw [← heps]; exact he
    have hid : frame.child.periodDenominator * (frame.parents.odd.num * (z.1 - frame.parents.even.den)
        - frame.parents.odd.den * (z.2 - frame.parents.even.num)) =
        (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.tGrade z
          - frame.sGrade z + frame.child.periodDenominator := by
      have e1 : frame.child.periodDenominator * (frame.parents.odd.num * (z.1 - frame.parents.even.den)
          - frame.parents.odd.den * (z.2 - frame.parents.even.num)) =
          frame.child.periodDenominator * (frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2)
          - frame.child.periodDenominator * (frame.parents.odd.num * frame.parents.even.den
            - frame.parents.even.num * frame.parents.odd.den) := by ring
      rw [e1, hid0, hdN, ← hdef, he]
      ring
    by_cases h0 : frame.parents.odd.num = 0
    · have hnqD : frame.parents.even.num * frame.parents.odd.den = 1 := by
        rw [h0] at hdq'; linarith
      have hnq1 : frame.parents.even.num = 1 := Int.eq_one_of_mul_eq_one_right hnq0 hnqD
      have hD1 : frame.parents.odd.den = 1 := Int.eq_one_of_mul_eq_one_left hDpos.le hnqD
      have hn1 : frame.child.num = 1 := by rw [hn, h0, hnq1]; norm_num
      have hlow := sr_N0_low _ _ _ _ _ _ _ h0 hD1 hn1 hTdef hd3 hE ht
      have hup := sr_N0_up _ _ _ _ _ _ _ h0 hD1 hn1 hTdef hd3 hE
      generalize frame.parents.odd.num * (z.1 - frame.parents.even.den)
        - frame.parents.odd.den * (z.2 - frame.parents.even.num) = u at hid ⊢
      have h1 : frame.child.periodDenominator * (-frame.parents.odd.den) < frame.child.periodDenominator * u := by
        rw [hid]; linarith
      have h2 : frame.child.periodDenominator * u < frame.child.periodDenominator * (frame.parents.odd.num + 2 * frame.parents.odd.den) := by
        rw [hid]; linarith
      have l1 := lt_of_mul_lt_mul_left h1 hTpos.le
      have l2 := lt_of_mul_lt_mul_left h2 hTpos.le
      have l1' := Int.add_one_le_iff.mpr l1
      have l2' := Int.add_one_le_iff.mpr l2
      constructor <;> linarith
    · have hN1 : 1 ≤ frame.parents.odd.num := by omega
      have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
      have h2N : 2 * frame.parents.odd.num ≤ frame.child.num := by omega
      have h2D : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
      have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num - 1 := by
        linarith
      have hlow := sr_core_low_epsm1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE ht
      have hup := sr_core_up_epsm1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE
      generalize frame.parents.odd.num * (z.1 - frame.parents.even.den)
        - frame.parents.odd.den * (z.2 - frame.parents.even.num) = u at hid ⊢
      have h1 : frame.child.periodDenominator * (-frame.parents.odd.den) < frame.child.periodDenominator * u := by
        rw [hid]; linarith
      have h2 : frame.child.periodDenominator * u < frame.child.periodDenominator * (frame.parents.odd.num + 2 * frame.parents.odd.den) := by
        rw [hid]; linarith
      have l1 := lt_of_mul_lt_mul_left h1 hTpos.le
      have l2 := lt_of_mul_lt_mul_left h2 hTpos.le
      have l1' := Int.add_one_le_iff.mpr l1
      have l2' := Int.add_one_le_iff.mpr l2
      constructor <;> linarith

/-- The sheet `A` vanishes on the `t`-window: `A(z) = 0` when `t(z) ≥ 1 − d`. -/
theorem ChildFrame.sheetA_eq_zero (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hG : conj.HasStrips G) {z : Site} (hz : z ∈ frame.closedPolygon)
    (ht : 1 - frame.child.den ≤ frame.tGrade z) : frame.sheetA (quarterTurnField G) z = 0 := by
  obtain ⟨hcn, hcd⟩ := sr_conj frame conj hconj
  obtain ⟨hu1, hu2⟩ := sr_u_bounds frame hz ht
  unfold ChildFrame.sheetA
  apply quarterTurnField_eq_zero hG
  · unfold ChildFrame.sGrade
    rw [hcn, hcd, sr_mapSite_neg]
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith
  · unfold ChildFrame.sGrade
    rw [hcn, hcd, sr_mapSite_neg]
    simp only [Prod.fst_sub, Prod.snd_sub]
    linarith


/-- The sheet-`C` lower bound: `s_p` on the shifted point, with the sibling's coordinates as variables. -/
theorem sr_core_low_C (N D n d nq dq T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n - 1) (hT : T = d^2 + 2*d*n - n^2)
    (hnq : nq = n - 2*N) (hdq : dq = d - 2*D)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2)) :
    -(2*D*T) < -2*t + (D*(d+n) + N*(d-n))*s
      + (2*(n*(nq-dq) - d*(nq+dq)) - (D*(d+n) + N*(d-n))*((d+n)*(nq-dq) + (d-n)*(nq+dq))) := by
  subst hnq hdq hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  rcases hE with ⟨-, h2, h3, -⟩ | ⟨-, h2, h3, -⟩
  · have hCs := mul_le_mul_of_nonneg_left h3 hC
    have := srP_A4e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have hCs := mul_le_mul_of_nonneg_left h3 hC
    have := srP_A4o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

/-- The sheet-`C` upper bound. -/
theorem sr_core_up_C (N D n d nq dq T t s : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2*N ≤ n) (h2D : 2*D ≤ d)
    (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hd : 3 ≤ d) (hrel : N*d = D*n - 1) (hT : T = d^2 + 2*d*n - n^2)
    (hnq : nq = n - 2*N) (hdq : dq = d - 2*D)
    (hE : (2 - T ≤ t ∧ t ≤ d + n - 2 ∧ 0 ≤ s ∧ s ≤ T + 2*n) ∨ (n - T ≤ t ∧ t ≤ d ∧ 2 - d + n ≤ s ∧ s ≤ T + d + n - 2))
    (hs2 : s ≤ 2*(d+n) - 2) :
    -2*t + (D*(d+n) + N*(d-n))*s
      + (2*(n*(nq-dq) - d*(nq+dq)) - (D*(d+n) + N*(d-n))*((d+n)*(nq-dq) + (d-n)*(nq+dq))) < (2*D + 2*N)*T := by
  subst hnq hdq hT
  have hC : 0 ≤ D*(d+n) + N*(d-n) := by nlinarith
  have hCs := mul_le_mul_of_nonneg_left hs2 hC
  rcases hE with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
  · have := srP_B4e N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith
  · have := srP_B4o N D n d hrel hN1 hND h2N h2D hn hnd hd
    nlinarith

/-- `sheet_eq_harmonic`: on the `E`-window, the sheet equals the harmonic grid, with `ε = ±1`.
The hypothesis `0 < N` excludes the odd parent `0/1`: there the sheet `C` branch is not determined by the
strips of the conjugate `1/1` (its value at the site `(0, 0)` reads `G(2, −1)`, a site outside both windows). -/
theorem ChildFrame.sheet_eq_harmonic (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate)
    {G : Field} (hG : conj.HasStrips G) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hs : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1) (hN : 0 < frame.parents.odd.num) :
    (if frame.eps = 1 then frame.sheetA (quarterTurnField G) z else frame.sheetC (quarterTurnField G) z) =
      harmonicGrid z := by
  obtain ⟨hcn, hcd⟩ := sr_conj frame conj hconj
  have hE := sr_E_disj frame hz
  have hs2 := sr_sGrade_le frame hs
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hn := sr_child_num frame
  have hd := sr_child_den frame
  obtain ⟨hnpos, hnd, hdiff, hd3, hTdef⟩ := frame.child_facts
  have hdef := sr_eps_def frame
  have heps := sr_eps_eq frame
  have hid0 := sr_tp_identity frame z
  have hN1 : 1 ≤ frame.parents.odd.num := by omega
  have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
  have h2N : 2 * frame.parents.odd.num ≤ frame.child.num := by omega
  have h2D : 2 * frame.parents.odd.den ≤ frame.child.den := by omega
  rcases frame.eps_unit with he | he
  · -- ε = 1: the sheet `A` is `qtf G z`, and `G(Zz)` is in the zero strip
    rw [if_pos he]
    have hW : frame.phaseW = 1 := by
      rcases frame.phaseW_cases with ⟨-, h⟩ | ⟨h', -⟩
      · exact h
      · rw [he] at h'; norm_num at h'
    have hsh1 : frame.sheetShift.1 = 0 := by rw [sr_shift, hW]; simp
    have hsh2 : frame.sheetShift.2 = 0 := by rw [sr_shift, hW]; simp
    unfold ChildFrame.sheetA
    have hzs : z - frame.sheetShift = z := by
      ext
      · rw [Prod.fst_sub, hsh1, sub_zero]
      · rw [Prod.snd_sub, hsh2, sub_zero]
    rw [hzs]
    have hdN : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
      rw [← heps]; exact he
    rw [hdN, one_mul] at hid0
    have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num + 1 := by
      linarith
    have hlow := sr_core_low_harm1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE
    have hup := sr_core_up_harm1 _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hE hs2
    have hTpos : 0 < frame.child.periodDenominator :=
      Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
    have hsp := sr_sp_identity frame z
    rw [hdN] at hsp
    set sp := (frame.parents.odd.den + frame.parents.odd.num) * z.1 + (frame.parents.odd.den - frame.parents.odd.num) * z.2 with hsp_def
    have h1 : frame.child.periodDenominator * (-(2 * frame.parents.odd.den)) < frame.child.periodDenominator * sp := by
      rw [hsp]; linarith
    have h2 : frame.child.periodDenominator * sp < frame.child.periodDenominator * (2 * frame.parents.odd.den + 2 * frame.parents.odd.num) := by
      rw [hsp]; linarith
    have l1 := lt_of_mul_lt_mul_left h1 hTpos.le
    have l2 := lt_of_mul_lt_mul_left h2 hTpos.le
    have l1' := Int.add_one_le_iff.mpr l1
    have l2' := Int.add_one_le_iff.mpr l2
    apply quarterTurnField_eq_harmonic hG
    · unfold ChildFrame.tGrade
      rw [hcn, hcd, sr_mapSite_neg]
      dsimp only
      linarith
    · unfold ChildFrame.tGrade
      rw [hcn, hcd, sr_mapSite_neg]
      dsimp only
      linarith
  · -- ε = -1: the sheet `C` is `qtf G (z − Vq) + a_q·(z − lv) + c_e`
    rw [if_neg (by rw [he]; norm_num)]
    have hW : frame.phaseW = 0 := by
      rcases frame.phaseW_cases with ⟨h', -⟩ | ⟨-, h⟩
      · rw [he] at h'; norm_num at h'
      · exact h
    have hsh1 : frame.sheetShift.1 = frame.parents.even.den := by rw [sr_shift, hW]; simp
    have hsh2 : frame.sheetShift.2 = frame.parents.even.num := by rw [sr_shift, hW]; simp
    have hdN : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
      rw [← heps]; exact he
    have hdq' : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = -1 := by
      rw [← hdef]; exact he
    have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by omega
    have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by omega
    have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num - 1 := by
      linarith
    have hlow := sr_core_low_C _ _ _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hnq hdq hE
    have hup := sr_core_up_C _ _ _ _ _ _ _ _ _ hN1 hND h2N h2D (by omega) (by omega) hd3 hrel hTdef hnq hdq hE hs2
    have hTpos : 0 < frame.child.periodDenominator :=
      Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
    -- the shifted point `x = z − V_q`
    have hx : z - frame.sheetShift - frame.sheetOffset =
        (z.1 - (frame.parents.even.num - frame.parents.even.den), z.2 - (frame.parents.even.num + frame.parents.even.den)) := by
      rw [sr_shift, sr_offset, he, hW]
      ext
      · simp
        ring
      · simp
        ring
    unfold ChildFrame.sheetC
    rw [hx]
    have hspx : frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * (z.1 - (frame.parents.even.num - frame.parents.even.den))
        + (frame.parents.odd.den - frame.parents.odd.num) * (z.2 - (frame.parents.even.num + frame.parents.even.den)))
        = -2 * frame.tGrade z + (frame.parents.odd.den * (frame.child.den + frame.child.num)
            + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.sGrade z
          + (2 * (frame.child.num * (frame.parents.even.num - frame.parents.even.den)
                - frame.child.den * (frame.parents.even.num + frame.parents.even.den))
            - (frame.parents.odd.den * (frame.child.den + frame.child.num)
                + frame.parents.odd.num * (frame.child.den - frame.child.num))
              * ((frame.child.den + frame.child.num) * (frame.parents.even.num - frame.parents.even.den)
                + (frame.child.den - frame.child.num) * (frame.parents.even.num + frame.parents.even.den))) := by
      unfold ChildFrame.tGrade ChildFrame.sGrade Fraction.periodDenominator
      linear_combination (2 * (frame.child.num * (z.1 - (frame.parents.even.num - frame.parents.even.den))
        - frame.child.den * (z.2 - (frame.parents.even.num + frame.parents.even.den)))) * hdN
    set sp := (frame.parents.odd.den + frame.parents.odd.num) * (z.1 - (frame.parents.even.num - frame.parents.even.den))
      + (frame.parents.odd.den - frame.parents.odd.num) * (z.2 - (frame.parents.even.num + frame.parents.even.den)) with hsp_def
    have h1 : frame.child.periodDenominator * (-(2 * frame.parents.odd.den)) < frame.child.periodDenominator * sp := by
      rw [hspx]; linarith
    have h2 : frame.child.periodDenominator * sp < frame.child.periodDenominator * (2 * frame.parents.odd.den + 2 * frame.parents.odd.num) := by
      rw [hspx]; linarith
    have l1 := lt_of_mul_lt_mul_left h1 hTpos.le
    have l2 := lt_of_mul_lt_mul_left h2 hTpos.le
    have l1' := Int.add_one_le_iff.mpr l1
    have l2' := Int.add_one_le_iff.mpr l2
    have hqtf : quarterTurnField G (z.1 - (frame.parents.even.num - frame.parents.even.den),
        z.2 - (frame.parents.even.num + frame.parents.even.den)) =
        harmonicGrid (z.1 - (frame.parents.even.num - frame.parents.even.den),
          z.2 - (frame.parents.even.num + frame.parents.even.den)) := by
      apply quarterTurnField_eq_harmonic hG
      · unfold ChildFrame.tGrade
        rw [hcn, hcd, sr_mapSite_neg]
        dsimp only
        linarith
      · unfold ChildFrame.tGrade
        rw [hcn, hcd, sr_mapSite_neg]
        dsimp only
        linarith
    rw [hqtf]
    have hce := frame.sheetConstant_exact
    rw [hW] at hce
    unfold Fraction.periodDenominator at hce
    unfold ChildFrame.siblingSlope
    simp only [Prod.fst_sub, Prod.snd_sub, hsh1, hsh2]
    have hx4 := harmonicGrid_exact (z.1 - (frame.parents.even.num - frame.parents.even.den),
      z.2 - (frame.parents.even.num + frame.parents.even.den))
    have hz4 := harmonicGrid_exact z
    dsimp only at hx4
    have hpar : (z.1 - (frame.parents.even.num - frame.parents.even.den) + (z.2 - (frame.parents.even.num + frame.parents.even.den))) % 2
        = (z.1 + z.2) % 2 := by omega
    have key : 4 * (harmonicGrid (z.1 - (frame.parents.even.num - frame.parents.even.den),
          z.2 - (frame.parents.even.num + frame.parents.even.den))
        + (frame.parents.even.num * (z.1 - frame.parents.even.den) - frame.parents.even.den * (z.2 - frame.parents.even.num))
        + frame.sheetConstant) = 4 * harmonicGrid z := by
      linear_combination hx4 - hz4 + 2 * hce - hpar
    linarith

end FLatticePaper.Induction
