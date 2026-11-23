import FLatticePaper.Plane.Induction.ChildFrame

/-! # Task 74 (2): the two offers of the odd seed (fixer Q14), as integer identities

With the odd parent `p = (D, N)` (`D + N` odd), the even sibling `q = (e, r)` (`e + r` even), the seed parameter
`ε = N e − D r ∈ {1, −1}`, `W = (1 + ε)/2`, `k = (−1, −2)`, `B = D² + 2DN − N²`, `H = (B + D + N)/2` and
`J₀ = (e² + 2er − r² − e − r)/2`, the two transported offers at the seed vanish after adding the harmonic summand:

* offer one:  `h₀(z) + t_p(q + k) − H + (1 − W) J = 0`,
* offer two:  `h₀(z) + h₀(y) + W J = 0`,

where `z = (D + N − 1, D − N + 1) + (1 − W)(e + r, e − r)`, `Y = Z z + U` with `Z(x, y) = (−y, x − 1)`, `U = (2D + e, 2N + r)`,
`J = t_q(Y − (1 − W) q) + J₀ + 2W` with `t_q(x) = r x₁ − e x₂`, and `y = V_p − ε V_q + k` with `V_h = (h_y − h_x, h_x + h_y)`.
The statements below are the four cases `ε = ±1` of the two offers. The harmonic values use `harmonicGrid_exact`, and the parity of
each argument is fixed by the parity of `D + N`, `e + r`. The certificates come from a Gröbner reduction (`w1_odd_seed_cert.py`). -/

namespace FLatticePaper.W1OddSeedId

open FLatticePaper FLatticePaper.Induction

/-- `4 h₀ x` at an even site is the numerator. -/
theorem four_harmonic_even (x : Site) (h : (x.1 + x.2) % 2 = 0) :
    4 * harmonicGrid x = x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 := by
  rw [harmonicGrid_exact, h, sub_zero]

/-- `4 h₀ x` at an odd site is the numerator minus one. -/
theorem four_harmonic_odd (x : Site) (h : (x.1 + x.2) % 2 = 1) :
    4 * harmonicGrid x = x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - 1 := by
  rw [harmonicGrid_exact, h]

/-- **Offer one, `ε = +1` (`W = 1`).** The seed `z = (D + N − 1, D − N + 1)` and `v = q + k = (e − 1, r − 2)`:
`h₀(z) + t_p(v) − H = 0`, with `t_p(x) = N x₁ − D x₂` and `2H = B + D + N`. -/
theorem offer_one_pos (D N e r H : ℤ) (hrel : N * e - D * r = 1)
    (hH : 2 * H = D ^ 2 + 2 * D * N - N ^ 2 + (D + N)) :
    harmonicGrid (D + N - 1, D - N + 1) + (N * (e - 1) - D * (r - 2)) - H = 0 := by
  have hz : 4 * harmonicGrid (D + N - 1, D - N + 1) =
      (D + N - 1) ^ 2 + 2 * (D + N - 1) * (D - N + 1) - (D - N + 1) ^ 2 - 2 * (D - N + 1) :=
    four_harmonic_even _ (by simp only; omega)
  have h4 : 4 * (harmonicGrid (D + N - 1, D - N + 1) + (N * (e - 1) - D * (r - 2)) - H) = 0 := by
    linear_combination hz + 4 * hrel - 2 * hH
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- **Offer two, `ε = +1` (`W = 1`).** `y = (N − D − (r − e) − 1, D + N − (e + r) − 2)` (odd), and
`J = r Y₁ − e Y₂ + J₀ + 2` with `Y = (−(D − N + 1) + 2D + e, D + N − 2 + 2N + r)`:
`h₀(z) + h₀(y) + J = 0`. -/
theorem offer_two_pos (D N e r J0 : ℤ) (hrel : N * e - D * r = 1)
    (hJ : 2 * J0 = e ^ 2 + 2 * e * r - r ^ 2 - e - r) :
    harmonicGrid (D + N - 1, D - N + 1) +
      harmonicGrid (N - D - (r - e) - 1, D + N - (e + r) - 2) +
      (r * (-(D - N + 1) + 2 * D + e) - e * (D + N - 2 + 2 * N + r) + J0 + 2) = 0 := by
  have hz : 4 * harmonicGrid (D + N - 1, D - N + 1) =
      (D + N - 1) ^ 2 + 2 * (D + N - 1) * (D - N + 1) - (D - N + 1) ^ 2 - 2 * (D - N + 1) :=
    four_harmonic_even _ (by simp only; omega)
  have hy : 4 * harmonicGrid (N - D - (r - e) - 1, D + N - (e + r) - 2) =
      (N - D - (r - e) - 1) ^ 2 + 2 * (N - D - (r - e) - 1) * (D + N - (e + r) - 2) -
        (D + N - (e + r) - 2) ^ 2 - 2 * (D + N - (e + r) - 2) - 1 :=
    four_harmonic_odd _ (by simp only; omega)
  have h4 : 4 * (harmonicGrid (D + N - 1, D - N + 1) +
      harmonicGrid (N - D - (r - e) - 1, D + N - (e + r) - 2) +
      (r * (-(D - N + 1) + 2 * D + e) - e * (D + N - 2 + 2 * N + r) + J0 + 2)) = 0 := by
    linear_combination hz + hy - 8 * hrel + 2 * hJ
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- **Offer one, `ε = −1` (`W = 0`).** The seed `z = (D + N − 1 + e + r, D − N + 1 + e − r)`, `v = (e − 1, r − 2)`, and
`J = r (Y₁ − e) − e (Y₂ − r) + J₀` with `Y = Z z + U`, `U = (2D + e, 2N + r)`:
`h₀(z) + t_p(v) − H + J = 0`. -/
theorem offer_one_neg (D N e r H J0 : ℤ) (hrel : N * e - D * r = -1)
    (hH : 2 * H = D ^ 2 + 2 * D * N - N ^ 2 + (D + N))
    (hJ : 2 * J0 = e ^ 2 + 2 * e * r - r ^ 2 - e - r) :
    harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) + (N * (e - 1) - D * (r - 2)) - H +
      (r * ((-(D - N + 1 + e - r)) + 2 * D + e - e) - e * ((D + N - 1 + e + r - 1) + 2 * N + r - r) + J0) = 0 := by
  have hz : 4 * harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) =
      (D + N - 1 + e + r) ^ 2 + 2 * (D + N - 1 + e + r) * (D - N + 1 + e - r) -
        (D - N + 1 + e - r) ^ 2 - 2 * (D - N + 1 + e - r) :=
    four_harmonic_even _ (by simp only; omega)
  have h4 : 4 * (harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) + (N * (e - 1) - D * (r - 2)) - H +
      (r * ((-(D - N + 1 + e - r)) + 2 * D + e - e) - e * ((D + N - 1 + e + r - 1) + 2 * N + r - r) + J0)) = 0 := by
    linear_combination hz - 4 * hrel - 2 * hH + 2 * hJ
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- **Offer two, `ε = −1` (`W = 0`).** The harmonic summands cancel: `h₀(z) + h₀(y) = 0` for
`y = (N − D + r − e − 1, D + N + e + r − 2)` (the second offer has no affine term at `W = 0`; the identity holds with no relation). -/
theorem offer_two_neg (D N e r : ℤ) :
    harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) +
      harmonicGrid (N - D + r - e - 1, D + N + e + r - 2) = 0 := by
  have hz : 4 * harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) =
      (D + N - 1 + e + r) ^ 2 + 2 * (D + N - 1 + e + r) * (D - N + 1 + e - r) -
        (D - N + 1 + e - r) ^ 2 - 2 * (D - N + 1 + e - r) :=
    four_harmonic_even _ (by simp only; omega)
  have hy : 4 * harmonicGrid (N - D + r - e - 1, D + N + e + r - 2) =
      (N - D + r - e - 1) ^ 2 + 2 * (N - D + r - e - 1) * (D + N + e + r - 2) -
        (D + N + e + r - 2) ^ 2 - 2 * (D + N + e + r - 2) - 1 :=
    four_harmonic_odd _ (by simp only; omega)
  have h4 : 4 * (harmonicGrid (D + N - 1 + e + r, D - N + 1 + e - r) +
      harmonicGrid (N - D + r - e - 1, D + N + e + r - 2)) = 0 := by
    linear_combination hz + hy
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

end FLatticePaper.W1OddSeedId
