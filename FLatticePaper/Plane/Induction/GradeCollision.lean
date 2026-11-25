import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Task 72 / Q31 psi (i): two parent grades of the same residue mod `r` coincide, except the pair `{0, r}`.

With the odd parent `N/D` (`r = D + N`, `c_p = D − N`): an even grade lies in `[0, E]` (`E ≤ 2N`), an odd grade in `[lo, r]` with
`lo ≥ −c_p`. If `r` divides the difference of two such grades, they are equal, or they are `{0, r}`. The cross-parity collision
`{2N, −c_p}` is excluded by `E ≤ 2N − 2` (phase `ε = +1`) or `lo ≥ 2 − c_p` (phase `ε = −1`). -/

namespace FLatticePaper.GradeCollision

/-- **Residue collision of parent grades.** -/
theorem grade_collision (N D E lo g1 g2 : ℤ) (hN : 0 < N) (hcp : 0 < D - N)
    (hodd : (D + N) % 2 = 1) (hE : E ≤ 2 * N) (hlo : -(D - N) ≤ lo)
    (hEx : E ≤ 2 * N - 2 ∨ 2 - (D - N) ≤ lo)
    (h1 : (g1 % 2 = 0 ∧ 0 ≤ g1 ∧ g1 ≤ E) ∨ (g1 % 2 = 1 ∧ lo ≤ g1 ∧ g1 ≤ D + N))
    (h2 : (g2 % 2 = 0 ∧ 0 ≤ g2 ∧ g2 ≤ E) ∨ (g2 % 2 = 1 ∧ lo ≤ g2 ∧ g2 ≤ D + N))
    (hdiv : (D + N) ∣ g1 - g2) :
    g1 = g2 ∨ (g1 = 0 ∧ g2 = D + N) ∨ (g1 = D + N ∧ g2 = 0) := by
  obtain ⟨t, ht⟩ := hdiv
  have hr : 0 < D + N := by omega
  have hb1 : g1 - g2 < 2 * (D + N) := by
    rcases h1 with ⟨p1, a1, b1⟩ | ⟨p1, a1, b1⟩ <;> rcases h2 with ⟨p2, a2, b2⟩ | ⟨p2, a2, b2⟩ <;> omega
  have hb2 : -(2 * (D + N)) < g1 - g2 := by
    rcases h1 with ⟨p1, a1, b1⟩ | ⟨p1, a1, b1⟩ <;> rcases h2 with ⟨p2, a2, b2⟩ | ⟨p2, a2, b2⟩ <;> omega
  have htlt : t < 2 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.mp hc) hr.le
    linarith
  have htgt : -2 < t := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.mp hc) hr.le
    linarith
  have hcases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · have e : g1 - g2 = -(D + N) := by linarith
    rcases h1 with ⟨p1, a1, b1⟩ | ⟨p1, a1, b1⟩ <;> rcases h2 with ⟨p2, a2, b2⟩ | ⟨p2, a2, b2⟩ <;> omega
  · have e : g1 - g2 = 0 := by linarith
    omega
  · have e : g1 - g2 = D + N := by linarith
    rcases h1 with ⟨p1, a1, b1⟩ | ⟨p1, a1, b1⟩ <;> rcases h2 with ⟨p2, a2, b2⟩ | ⟨p2, a2, b2⟩ <;> omega


/-- **The sharp odd floor in phase `ε = −1`.** An odd native grade `g = r x + c_p j` with `s = L x + c j ≥ 2 − c` and `j ≥ 0`
is not `−c_p`: `L g = r s − 2ε j` and `r c = c_p L + 2ε` would give `0 ≥ 2r + 2 + 2j`. -/
theorem odd_grade_ne_low (N D n d ε x j : ℤ) (hε : ε = N * d - D * n) (hε1 : ε = -1)
    (hr : 0 ≤ D + N) (hj : 0 ≤ j) (hs : 2 - (d - n) ≤ (d + n) * x + (d - n) * j)
    (hg : (D + N) * x + (D - N) * j = -(D - N)) : False := by
  have hrc : (D + N) * (d - n) = (D - N) * (d + n) + 2 * ε := by rw [hε]; ring
  have hkey : (d + n) * ((D + N) * x + (D - N) * j) =
      (D + N) * ((d + n) * x + (d - n) * j) - 2 * ε * j := by rw [hε]; ring
  rw [hg, hε1] at hkey
  rw [hε1] at hrc
  have hrs := mul_le_mul_of_nonneg_left hs hr
  linarith

end FLatticePaper.GradeCollision
