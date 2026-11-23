import FLatticePaper.Plane.Induction.ZoneHarmonic

/-! # The sheet identity of the zone of I1 (task 49, step (b) of the fix)

With the even parent `n_q/d_q` (so `U_q = (d_q, n_q)`, `V_q = (n_q − d_q, n_q + d_q)`, `a_q = (n_q, −d_q)`), the odd parent `N/D`,
`ε = N d_q − n_q D = ±1` and `W = (1 + ε)/2`, the sheet `C(z) = f(z − lv − e) + a_q·(z − lv) + c_e` with `lv = (1 − W) U_q`,
`e = V_q + ε U_q`, `c_e = c_q + 2W` (`2 c_q = T_q − d_q − n_q`) equals `h₀(w) + (f(q) − h₀(q))` where `w = z − W U`, `U = U_p + U_q`,
`q = w − V_q`. The proof uses the `U_p`-periodicity of `f` (for `W = 1`) and the harmonic shift along `V_q`.
-/

namespace FLatticePaper.Induction
open FLatticePaper

namespace ZoneSheet

/-- The sheet `C` of the zone in coordinates, equal to the harmonic expression `h₀(w) + (f q − h₀ q)`. -/
theorem sheet_eq_harmonic (F : Field) (N D nq dq cq W z1 z2 : ℤ)
    (hW : (W = 0 ∧ N * dq - nq * D = -1) ∨ (W = 1 ∧ N * dq - nq * D = 1))
    (hcq : 2 * cq = dq * dq + 2 * dq * nq - nq * nq - dq - nq)
    (hfUp : ∀ x : Site, quarterTurnField F (x + (2 * D, 2 * N)) = quarterTurnField F x) :
    quarterTurnField F (z1 - (1 - W) * dq - (nq - dq + (N * dq - nq * D) * dq),
        z2 - (1 - W) * nq - (nq + dq + (N * dq - nq * D) * nq))
      + (nq * (z1 - (1 - W) * dq) - dq * (z2 - (1 - W) * nq)) + (cq + 2 * W)
    = harmonicGrid (z1 - W * (2 * D + dq), z2 - W * (2 * N + nq))
      + (quarterTurnField F (z1 - W * (2 * D + dq) - (nq - dq), z2 - W * (2 * N + nq) - (nq + dq))
        - harmonicGrid (z1 - W * (2 * D + dq) - (nq - dq), z2 - W * (2 * N + nq) - (nq + dq))) := by
  have hc : 2 * cq = -2 * nq * (-dq) - nq ^ 2 + (-dq) ^ 2 - nq + (-dq) := by
    linear_combination hcq
  have hh := ZoneHarmonic.harmonicGrid_sub_shift (z1 - W * (2 * D + dq), z2 - W * (2 * N + nq)) nq (-dq) cq hc
  have e : (z1 - W * (2 * D + dq), z2 - W * (2 * N + nq)) - (nq + -dq, nq - -dq)
      = (z1 - W * (2 * D + dq) - (nq - dq), z2 - W * (2 * N + nq) - (nq + dq)) := by
    ext <;> simp
    ring
  rw [e] at hh
  simp only at hh
  rcases hW with ⟨rfl, hε⟩ | ⟨rfl, hε⟩
  · have hy : (z1 - (1 - 0) * dq - (nq - dq + (N * dq - nq * D) * dq),
        z2 - (1 - 0) * nq - (nq + dq + (N * dq - nq * D) * nq))
        = (z1 - 0 * (2 * D + dq) - (nq - dq), z2 - 0 * (2 * N + nq) - (nq + dq)) := by
      rw [hε]
      ext <;> simp <;> ring
    rw [hy]
    linear_combination (-1 : ℤ) * hh
  · have hy : (z1 - (1 - 1) * dq - (nq - dq + (N * dq - nq * D) * dq),
        z2 - (1 - 1) * nq - (nq + dq + (N * dq - nq * D) * nq))
        = (z1 - 1 * (2 * D + dq) - (nq - dq), z2 - 1 * (2 * N + nq) - (nq + dq)) + (2 * D, 2 * N) := by
      rw [hε]
      ext <;> simp <;> ring
    rw [hy, hfUp]
    linear_combination (-1 : ℤ) * hh + (-2 : ℤ) * hε

end ZoneSheet

end FLatticePaper.Induction
