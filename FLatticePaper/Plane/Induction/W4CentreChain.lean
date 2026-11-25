import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # W4 (Q34): the centre star of a conjugate freeH point, as integer arithmetic

Parent fraction `N/D` with `1 ≤ N < D` (`D − N` and `D + N` odd), parent period `T = D² + 2DN − N²`.
The conjugate frame has child `(n', d') = (D − N, D + N)`, so `L' = 2D`, `c' = 2N`, period `2T`, and
`s'(z) = 2D z₁ + 2N z₂`. Its kernel is `U' = (D + N, D − N)` (`s'(U') = 2T`) and its transverse is
`V' = (−2N, 2D)` (`s'(V') = 0`). The parent grade is `t_p(z) = N z₁ − D z₂`, and `Y x = I − zTurn x = (1 + x₂, −x₁)`
satisfies `s'(Y x) = 2D − 2 t_p(x)` (`UnitBound.sGrade_conj_zTurn`).

A class (ii) root has `Y x = h + j U' − i V'` with `h` a conjugate freeH centre. The H-web index `k` gives the
grade `t_p(x) + k T`, so `m := k − j` gives the root grade `g = D − σ + m T`, where `σ = s'(h)/2 = D h₁ + N h₂`.

* `tp_identity`: `t_p(x) = D − σ − j T` (no `i`-dependence).
* `odd_centre_cases`: an odd centre has `D ≤ σ ≤ T − N` (`ArcFrame.freeH_vertex_bounds`); the root condition forces
  `(m, σ) = (1, T − N)` or `(0, D)`.
* `even_centre_no_root`: an even centre (`2D ≤ σ ≤ T − D − N`) carries no H-web root.
* the band `hsy` (`1 − D ≤ g_y ∧ g_y + 1 ≤ N + 2D − 1`) on the star members, in each case. The one failure is the
  `m = 1` case with the input `h − (0,1)·` at `D = N + 1` (`band_m1_neg_fails`), which must be excluded by the direction
  of the target edge. -/

namespace FLatticePaper.W4CentreChain

/-- **The parent grade of a class (ii) root.** `Y x = h + j U' − i V'` with `Y x = (1 + x₂, −x₁)` gives
`t_p(x) = D − σ(h) − j T`, where `σ(h) = D h₁ + N h₂` is half the conjugate `s`-grade of `h`. The index `i` drops out. -/
theorem tp_identity (N D h1 h2 i j x1 x2 : ℤ)
    (hY1 : 1 + x2 = h1 + j * (D + N) + 2 * N * i)
    (hY2 : -x1 = h2 + j * (D - N) - 2 * D * i) :
    N * x1 - D * x2 = D - (D * h1 + N * h2) - j * (D ^ 2 + 2 * D * N - N ^ 2) := by
  linear_combination (-D) * hY1 + (-N) * hY2

/-- **Odd centres: the admissible (m, σ).** The odd freeH bounds give `D ≤ σ ≤ T − N`. The H-web root condition
on `g = D − σ + m T` (the `HRootWeb` disjuncts for the parent) then forces `m ∈ {0, 1}`, with `(1, T − N)` or `(0, D)`. -/
theorem odd_centre_cases (N D T σ m : ℤ) (hN : 1 ≤ N) (hND : N < D) (hT : 1 ≤ T)
    (hσ1 : D ≤ σ) (hσ2 : σ ≤ T - N)
    (hroot : (1 ≤ D - σ + m * T ∧ D - σ + m * T ≤ N + D - 1) ∨ D - σ + m * T = 0 ∨
      D - σ + m * T = N + D ∨ (N ≤ D - σ + m * T ∧ D - σ + m * T ≤ D) ∨ D - σ + m * T = D + 1) :
    (m = 1 ∧ σ = T - N) ∨ (m = 0 ∧ σ = D) := by
  have hm : m = 0 ∨ m = 1 := by
    rcases (show m ≤ -1 ∨ m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h | h
    · exfalso
      have hmT : m * T ≤ -T := by nlinarith
      rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hmT : 2 * T ≤ m * T := by nlinarith
      rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
  rcases hm with rfl | rfl
  · have hσD : σ = D := by
      rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
    exact Or.inr ⟨rfl, hσD⟩
  · have hσT : σ = T - N := by
      rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
    exact Or.inl ⟨rfl, hσT⟩

/-- **Even centres carry no H-web root.** With `2D ≤ σ ≤ T − D − N` (`freeH_vertex_bounds`, even case), the grade
`g = D − σ + m T` lies outside every H-web disjunct for every `m`. -/
theorem even_centre_no_root (N D T σ m : ℤ) (hN : 1 ≤ N) (hND : N < D) (hT : 1 ≤ T)
    (hσ1 : 2 * D ≤ σ) (hσ2 : σ ≤ T - D - N) :
    ¬ ((1 ≤ D - σ + m * T ∧ D - σ + m * T ≤ N + D - 1) ∨ D - σ + m * T = 0 ∨
      D - σ + m * T = N + D ∨ (N ≤ D - σ + m * T ∧ D - σ + m * T ≤ D) ∨ D - σ + m * T = D + 1) := by
  intro hroot
  rcases (show m ≤ -1 ∨ m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h | h
  · have hmT : m * T ≤ -T := by nlinarith
    rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
  · subst h
    rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
  · subst h
    rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith
  · have hmT : 2 * T ≤ m * T := by nlinarith
    rcases hroot with ⟨h1, h2⟩ | h1 | h1 | ⟨h1, h2⟩ | h1 <;> linarith

/-- **Neighbours of an odd centre.** The input `(h₁, h₂ + 1)` has `σ + N`; the input `(h₁, h₂ − 1)` has `σ − N`. -/
theorem sigma_odd_neighbours (N D h1 h2 : ℤ) :
    D * h1 + N * (h2 + 1) = (D * h1 + N * h2) + N ∧ D * h1 + N * (h2 - 1) = (D * h1 + N * h2) - N := by
  constructor <;> ring

/-- **Band, case `m = 1`, target `σ' = T` (the input `(h₁, h₂ + 1)`).** The grade is `g_y = D`. -/
theorem band_m1_pos (N D T : ℤ) (hN : 1 ≤ N) (hND : N < D) :
    1 - D ≤ D - T + 1 * T ∧ D - T + 1 * T + 1 ≤ N + 2 * D - 1 := by
  constructor <;> linarith

/-- **Band, case `m = 1`, target `σ' = T − 2N` (the input `(h₁, h₂ − 1)`).** The grade is `g_y = D + 2N`, and the band
holds exactly when `N + 2 ≤ D`. -/
theorem band_m1_neg (N D T : ℤ) (hN : 1 ≤ N) (hDN : N + 2 ≤ D) :
    1 - D ≤ D - (T - 2 * N) + 1 * T ∧ D - (T - 2 * N) + 1 * T + 1 ≤ N + 2 * D - 1 := by
  constructor <;> linarith

/-- **The failure of the `m = 1` band for the input `(h₁, h₂ − 1)` when `D = N + 1`.** The upper end is exceeded by one. -/
theorem band_m1_neg_fails (N D T : ℤ) (hD : D = N + 1) :
    ¬ (D - (T - 2 * N) + 1 * T + 1 ≤ N + 2 * D - 1) := by
  intro h
  linarith

/-- **Band, case `m = 0`, `σ = D`, target `σ' = D − N` (the input `(h₁, h₂ − 1)`).** The grade is `g_y = N`. -/
theorem band_m0_neg (N D T : ℤ) (hN : 1 ≤ N) (hD : 1 ≤ D) :
    1 - D ≤ D - (D - N) + 0 * T ∧ D - (D - N) + 0 * T + 1 ≤ N + 2 * D - 1 := by
  constructor <;> linarith

/-- **Band, case `m = 0`, `σ = D`, target `σ' = D + N` (the input `(h₁, h₂ + 1)`).** The grade is `g_y = −N`. -/
theorem band_m0_pos (N D T : ℤ) (hN : 1 ≤ N) (hND : N < D) :
    1 - D ≤ D - (D + N) + 0 * T ∧ D - (D + N) + 0 * T + 1 ≤ N + 2 * D - 1 := by
  constructor <;> linarith

end FLatticePaper.W4CentreChain
