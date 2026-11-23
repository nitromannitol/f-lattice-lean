import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.ZoneHarmonic

/-! # The harmonic region of I2 (task 49, the fix's harmonic region, eq. (4))

With `U_q = (d_q, n_q)`, `V_p = (−(D − N), D + N)` and `ε = N d_q − n_q D`, the harmonic residue
`R(u) = f(u − U_q) − h₀(u)` (with `f = quarterTurnField F`) changes by `−ε` under `u ↦ u + V_p`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace HarmI2

/-- The harmonic residue `R(u) = f(u − U_q) − h₀(u)` (eq. (4) of the fix). -/
def harmR (F : Site → ℤ) (dq nq : ℤ) (u : Site) : ℤ :=
  quarterTurnField F (u.1 - dq, u.2 - nq) - harmonicGrid u

/-- An integer `c` with `2c = 2ND − N² + D² − N − D`, the constant of the shift along `(N − D, N + D)`. -/
theorem exists_half_pair (N D : ℤ) :
    ∃ c : ℤ, 2 * c = -2 * N * (-D) - N ^ 2 + (-D) ^ 2 - N + (-D) := by
  obtain ⟨l, hl⟩ := Int.even_mul_succ_self N
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self D
  exact ⟨N * D - l + k, by linear_combination hl - hk⟩

/-- The shift `u ↦ u + V_p` changes the residue by `−ε`. -/
theorem harmR_shift_Vp (F : Site → ℤ) (N D nq dq : ℤ) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y)
    (u : Site) :
    harmR F dq nq (u.1 + -(D - N), u.2 + (D + N)) = harmR F dq nq u - (N * dq - nq * D) := by
  obtain ⟨c, hc⟩ := exists_half_pair N D
  have hZ : F (-((u.2 - nq) + (D + N)), (u.1 - dq) - (D - N) - 1) = F (-(u.2 - nq), (u.1 - dq) - 1) :=
    ZoneHarmonic.fZ_add_Vp F N D hK (u.1 - dq, u.2 - nq)
  have h1 := ZoneHarmonic.harmonicGrid_sub_shift (u.1 + -(D - N) - dq, u.2 + (D + N) - nq) N (-D) c hc
  have e1 : (u.1 + -(D - N) - dq, u.2 + (D + N) - nq) - (N + -D, N - -D) = (u.1 - dq, u.2 - nq) := by
    ext
    · first | (simp; done) | (simp; ring)
    · first | (simp; done) | (simp; ring)
  rw [e1] at h1
  have h2 := ZoneHarmonic.harmonicGrid_sub_shift (u.1 + -(D - N), u.2 + (D + N)) N (-D) c hc
  have e2 : (u.1 + -(D - N), u.2 + (D + N)) - (N + -D, N - -D) = u := by
    ext
    · first | (simp; done) | (simp; ring)
    · first | (simp; done) | (simp; ring)
  rw [e2] at h2
  simp only at h1 h2
  unfold harmR
  rw [quarterTurnField, quarterTurnField]
  simp only [quarterTurn_site]
  ring_nf at hZ h1 h2 ⊢
  linear_combination hZ + h1 - h2

end HarmI2

end FLatticePaper.Induction
