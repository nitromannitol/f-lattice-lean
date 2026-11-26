import FLatticePaper.Plane.Induction.ChildFrame

/-! # Algebra of the opposite collar (integer identities)

Parent integers `N, D` (odd parent), `nq, dq` (even parent), child `n, d`, `ε = N d − D n`.
`T = d² + 2dn − n²`, `C = D(d+n) + N(d−n)`. The grade of `v` is `t = n v₁ − d v₂`, `s = (d+n) v₁ + (d−n) v₂`, and the parent
`s`-grade is `σ = (D+N) v₁ + (D−N) v₂`. These are the identities used by the opposite window. -/

namespace FLatticePaper.OppAlg

open FLatticePaper.Induction

/-- `T = d² + 2dn − n²`. -/
def TT (n d : ℤ) : ℤ := d ^ 2 + 2 * d * n - n ^ 2

/-- `C = D(d+n) + N(d−n)`. -/
def CC (N D n d : ℤ) : ℤ := D * (d + n) + N * (d - n)

/-- `T σ = 2ε t + C s` for every site. -/
theorem sigma_identity {N D n d ε : ℤ} (hε : ε = N * d - D * n) (v1 v2 : ℤ) :
    TT n d * ((D + N) * v1 + (D - N) * v2) = 2 * ε * (n * v1 - d * v2) + CC N D n d * ((d + n) * v1 + (d - n) * v2) := by
  subst hε
  unfold TT CC
  ring

/-- `C d = D T + ε(d − n)`. -/
theorem CC_mul_d {N D n d ε : ℤ} (hε : ε = N * d - D * n) : CC N D n d * d = D * TT n d + ε * (d - n) := by
  subst hε
  unfold TT CC
  ring

/-- `C n = N T − ε(d + n)`. -/
theorem CC_mul_n {N D n d ε : ℤ} (hε : ε = N * d - D * n) : CC N D n d * n = N * TT n d - ε * (d + n) := by
  subst hε
  unfold TT CC
  ring

/-- `C (d + n) = (D + N) T − 2 ε n`. -/
theorem CC_mul_L {N D n d ε : ℤ} (hε : ε = N * d - D * n) :
    CC N D n d * (d + n) = (D + N) * TT n d - 2 * ε * n := by
  subst hε
  unfold TT CC
  ring

/-- `T ≡ 2 (mod 4)` for odd `n, d`: hence `T / 2` is odd. -/
theorem TT_mod_four {n d : ℤ} (hn : n % 2 = 1) (hd : d % 2 = 1) : TT n d % 4 = 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, d = 2 * a + 1 := ⟨d / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
  have e : TT (2 * b + 1) (2 * a + 1) = 2 + 4 * (a ^ 2 + 2 * a + 2 * a * b - b ^ 2) := by
    unfold TT
    ring
  rw [e]
  omega

/-- The harmonic grid under the shift `(2D, 2N)`. -/
theorem harmonic_shift_2Up (x1 x2 D N : ℤ) :
    harmonicGrid (x1 + 2 * D, x2 + 2 * N) =
      harmonicGrid (x1, x2) + (D + N) * x1 + (D - N) * x2 + (D ^ 2 + 2 * D * N - N ^ 2 - N) := by
  have e1 := harmonicGrid_exact (x1 + 2 * D, x2 + 2 * N)
  have e2 := harmonicGrid_exact (x1, x2)
  have hp : ((x1 + 2 * D) + (x2 + 2 * N)) % 2 = (x1 + x2) % 2 := by omega
  simp only at e1
  rw [hp] at e1
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination e1 - e2

/-- The constant identity at `ε = −1` (parent query `y − V_q` with the even parent `(d_q, n_q)`). -/
theorem h0_identity_minus (nq dq y1 y2 ce : ℤ) (hce : 2 * ce = dq * dq + 2 * dq * nq - nq * nq - dq - nq) :
    harmonicGrid (y1 - (nq - dq), y2 - (nq + dq)) + nq * (y1 - dq) - dq * (y2 - nq) + ce = harmonicGrid (y1, y2) := by
  have e1 := harmonicGrid_exact (y1 - (nq - dq), y2 - (nq + dq))
  have e2 := harmonicGrid_exact (y1, y2)
  have hp : (y1 - (nq - dq) + (y2 - (nq + dq))) % 2 = (y1 + y2) % 2 := by omega
  simp only at e1
  rw [hp] at e1
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination e1 - e2 + 2 * hce

/-- The constant identity at `ε = +1`, with the parent relation `N d_q − D n_q = 1` (the point `y = z − K`). -/
theorem h0_identity_plus {N D nq dq y1 y2 ce : ℤ} (hε : N * dq - D * nq = 1)
    (hce : 2 * ce = dq * dq + 2 * dq * nq - nq * nq - dq - nq + 4) :
    harmonicGrid (y1 - (nq - dq), y2 - (nq + dq)) + nq * (y1 + (2 * D + dq)) - dq * (y2 + (2 * N + nq)) + ce =
      harmonicGrid (y1, y2) := by
  have e1 := harmonicGrid_exact (y1 - (nq - dq), y2 - (nq + dq))
  have e2 := harmonicGrid_exact (y1, y2)
  have hp : (y1 - (nq - dq) + (y2 - (nq + dq))) % 2 = (y1 + y2) % 2 := by omega
  simp only at e1
  rw [hp] at e1
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination e1 - e2 + 2 * hce - 8 * hε

end FLatticePaper.OppAlg
