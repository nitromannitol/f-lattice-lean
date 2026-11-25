import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.ZoneI1

/-! Task 72 / Q31 step 2, the algebraic core of the clipped identity.

With `σ = ε U_p` (`ChildFrame.shortShift`), `U_p = (2D, 2N)` and `U_q = (d_q, n_q)`:
* `F(z − σ) = F(z + U_p)` when `ε = −1` (exact rewriting);
* `F(z − σ) = F(z + U_q)` when `ε = 1`, by the kernel period `(d, n) = U_p + U_q` with constant `0`;
* the harmonic translation `h0(z − V_q) + a_q·z − s = h0(z)` with `2s = L_q − T_q` (`harmonicGrid_sub_V`). -/

namespace FLatticePaper.ClippedCore

open FLatticePaper FLatticePaper.Induction

/-- The kernel of the child is `U = (d, n)`. -/
theorem kernel_eq_UD (frame : ChildFrame) :
    frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := by
  have hk : frame.child.modifiedDeck.kernel = frame.child.modifiedDeck.combine 1 0 := by
    unfold Farey.PeriodDeck.combine
    simp
  rw [hk, ChainDeck.combine_eq_vec]
  ext <;> simp

/-- **Case `ε = −1`:** `F(z − σ) = F(z + U_p)`. -/
theorem sigma_shift_neg (frame : ChildFrame) {F : Field} (z : Site) (hε : frame.eps = -1) :
    F (z - frame.shortShift) = F (z + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num)) := by
  have e : z - frame.shortShift = z + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
    unfold ChildFrame.shortShift
    rw [hε]
    ext <;> simp
  rw [e]

/-- **Case `ε = 1`:** `F(z − σ) = F(z + U_q)`, by the kernel period with constant `0`. -/
theorem sigma_shift_pos (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (z : Site)
    (hε : frame.eps = 1) :
    F (z - frame.shortShift) = F (z + (frame.parents.even.den, frame.parents.even.num)) := by
  have hper := hP.periods.1 (z - (2 * frame.parents.odd.den, 2 * frame.parents.odd.num))
  rw [kernel_eq_UD, frame.coherentConstantU_eq_zero, add_zero] at hper
  have hd := FLatticePaper.Induction.ZoneI1.child_den_eq frame
  have hn := FLatticePaper.Induction.ZoneI1.child_num_eq frame
  have e1 : z - frame.shortShift = z - (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
    unfold ChildFrame.shortShift
    rw [hε]
    ext <;> simp
  have e2 : z - (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) +
      (frame.child.den, frame.child.num) = z + (frame.parents.even.den, frame.parents.even.num) := by
    rw [hd, hn]
    ext <;> simp <;> ring
  rw [e1, ← hper, e2]

/-- **The harmonic translation identity** `h0(z − V_q) + a_q·z − s = h0(z)` for `2s = L_q − T_q`. -/
theorem harmonic_translate_Vq (nq dq : ℤ) (z : Site) (s : ℤ)
    (hs : 2 * s = nq + dq - (dq ^ 2 + 2 * dq * nq - nq ^ 2)) :
    harmonicGrid (z.1 - (nq - dq), z.2 - (nq + dq)) + (nq * z.1 - dq * z.2) - s = harmonicGrid z := by
  have := harmonicGrid_sub_V nq dq z.1 z.2 s hs
  rw [this]
  ring

/-- The parent grade of the transverse vector of the even parent: `s_p(V_q) = −2 ε`, with `ε = N d_q − D n_q`. -/
theorem sp_Vq (N D nq dq : ℤ) :
    (D + N) * (nq - dq) + (D - N) * (nq + dq) = -2 * (N * dq - D * nq) := by
  ring

end FLatticePaper.ClippedCore
