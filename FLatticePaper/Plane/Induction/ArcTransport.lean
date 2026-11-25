import Mathlib.Tactic.Ring

/-! Task 72 / Q29, the exact integer identities of the H-arc transport. The receiver is `n/d`, its odd parent `N/D`, and
`r = D + N`, `L = d + n`, `η = N d − D n`. The identities are pure ring identities; they are the algebra behind the transport
`k = j − d_q` (phase 0) and `k = d − 1 − j` (phase 1), and the shift `t_p(x) = t_p(w) − (1 − W) η`. -/

namespace FLatticePaper.ArcTransport

/-- `L t_p(w) = r t(w) + η u` with `t_p(w) = N w₁ − D w₂`, `t(w) = n w₁ − d w₂`, `u = w₁ + w₂`. -/
theorem trace_identity (N D n d w₁ w₂ : ℤ) :
    (d + n) * (N * w₁ - D * w₂) =
      (D + N) * (n * w₁ - d * w₂) + (N * d - D * n) * (w₁ + w₂) := by
  ring

/-- `r n = N L − η`. -/
theorem r_mul_n (N D n d : ℤ) : (D + N) * n = N * (d + n) - (N * d - D * n) := by
  ring

/-- `r d = D L + η`. -/
theorem r_mul_d (N D n d : ℤ) : (D + N) * d = D * (d + n) + (N * d - D * n) := by
  ring

/-- The transport shift: with `x = w − (1 − W) (d_q, n_q)` and the parent relation `N d_q − D n_q = η`,
`t_p(x) = t_p(w) − (1 − W) η`. -/
theorem shift_identity (N D n d dq nq W w₁ w₂ : ℤ) (hq : N * dq - D * nq = N * d - D * n) :
    N * (w₁ - (1 - W) * dq) - D * (w₂ - (1 - W) * nq) =
      (N * w₁ - D * w₂) - (1 - W) * (N * d - D * n) := by
  rw [← hq]
  ring

end FLatticePaper.ArcTransport
