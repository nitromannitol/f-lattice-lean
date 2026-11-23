import FLatticePaper.Plane.Induction.ChartShift

/-! Task 66 (2)(c): the chart separation, in the `s`-grade. Both shifted ends of a non-exit input edge take the same
representative: either `x` itself (chart `k = 0`, the first chart) or `x − ε U` (chart `k = ε`, the adjacent chart), where
`x = z + σ`, `σ = ε U_p`, `s(σ) = 2 ε C` with `C = D L + N (d − n)`, and `s(U) = T`.

The windows of the closed polygon are `W_e = [0, T + 2n]` (even sites) and `W_o = [2 − d + n, T + L − 2]` (odd sites), with
even endpoints; both ends of an input edge have `s`-values differing by `L` or `d − n` (both `≤ L`); and `0 ≤ 2C ≤ T`.
So a mixed configuration would have a gap of at least `L + 2 > L`: the separation is linear arithmetic. -/

namespace FLatticePaper.Induction

theorem sep_even_centre (T C n d sc si ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T % 2 = 0) (hC0 : 0 ≤ 2 * C)
    (hC1 : 2 * C ≤ T) (hsc : sc % 2 = 0) (hsi : si % 2 = 0)
    (hstep : si = sc + (d + n) ∨ si = sc - (d + n) ∨ si = sc + (d - n) ∨ si = sc - (d - n))
    (hscw : 0 ≤ sc ∧ sc ≤ T + 2 * n) (hsiw : 2 - d + n ≤ si ∧ si ≤ T + (d + n) - 2) :
    ((0 ≤ sc + 2 * ε * C ∧ sc + 2 * ε * C ≤ T + 2 * n) ∧
        (2 - d + n ≤ si + 2 * ε * C ∧ si + 2 * ε * C ≤ T + (d + n) - 2)) ∨
      ((0 ≤ sc + 2 * ε * C - ε * T ∧ sc + 2 * ε * C - ε * T ≤ T + 2 * n) ∧
        (2 - d + n ≤ si + 2 * ε * C - ε * T ∧ si + 2 * ε * C - ε * T ≤ T + (d + n) - 2)) := by
  rcases hε with rfl | rfl <;> omega

theorem sep_odd_centre (T C n d sc si ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT : T % 2 = 0) (hC0 : 0 ≤ 2 * C)
    (hC1 : 2 * C ≤ T) (hsc : sc % 2 = 0) (hsi : si % 2 = 0)
    (hstep : si = sc + (d + n) ∨ si = sc - (d + n) ∨ si = sc + (d - n) ∨ si = sc - (d - n))
    (hscw : 2 - d + n ≤ sc ∧ sc ≤ T + (d + n) - 2) (hsiw : 0 ≤ si ∧ si ≤ T + 2 * n) :
    ((2 - d + n ≤ sc + 2 * ε * C ∧ sc + 2 * ε * C ≤ T + (d + n) - 2) ∧
        (0 ≤ si + 2 * ε * C ∧ si + 2 * ε * C ≤ T + 2 * n)) ∨
      ((2 - d + n ≤ sc + 2 * ε * C - ε * T ∧ sc + 2 * ε * C - ε * T ≤ T + (d + n) - 2) ∧
        (0 ≤ si + 2 * ε * C - ε * T ∧ si + 2 * ε * C - ε * T ≤ T + 2 * n)) := by
  rcases hε with rfl | rfl <;> omega

end FLatticePaper.Induction
