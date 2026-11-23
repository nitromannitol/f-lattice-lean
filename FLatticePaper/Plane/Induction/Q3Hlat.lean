import FLatticePaper.Plane.Induction.Q3Bridge
import FLatticePaper.Plane.Induction.Q3Adjacent

/-! Task 59, paragraph 5: the lattice bridge `−ε U_q = δ₀ + j U_p` proved from the frame data (no Farey identity beyond
`t_p(U_q) = ε` and `t_p(δ₀) = −1`, which is derived from `conj.child = rotate` and the child-of-parents relation).

Steps:
* `t_p(−ε U_q) = −ε²`, since `t_p(U_q) = N d_q − D n_q = ε`; hence `t_p(−εU_q) = −1`.
* `t_p(δ₀) = −ε_c · Y` with `Y = (D+N) N_c − (D−N) D_c = det(conj.odd, conj.child) = ε_c`; hence `t_p(δ₀) = −1`.
* So the difference `Δ = −ε U_q − δ₀` has `t_p(Δ) = 0`, i.e. `N a = D b`; `gcd(N, D) = 1` gives `Δ = k (D, N)`.
* `Δ_1 + Δ_2 = k (D+N)` is even (`d_q + n_q` is even, `ε_c D_c` contributes an even term) and `D+N` is odd, so `k` is even.
  Hence `Δ = j (2D, 2N) = j U_p`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame

theorem eps_sq_one (frame : ChildFrame) : frame.eps * frame.eps = 1 := by
  rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num

/-- `det(conj.odd, conj.child) = ε_c`, written with the rotated child `(D−N, D+N)`. -/
theorem conj_child_det (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate) :
    (frame.parents.odd.den + frame.parents.odd.num) * conj.parents.odd.num -
      (frame.parents.odd.den - frame.parents.odd.num) * conj.parents.odd.den = conj.eps := by
  have hn := (conj_child_num_den hconj).1
  have hd := (conj_child_num_den hconj).2
  have h2 : conj.child.den * conj.parents.odd.num - conj.child.num * conj.parents.odd.den = conj.eps := by
    simp only [ChildFrame.child, ChildFrame.eps, Parents.current, Parents.combine, Fraction.det]
    ring
  rw [hn, hd] at h2
  linarith

/-- The lattice bridge: `−ε U_q = δ₀ + j U_p` for an integer `j`, with `U_q = (d_q, n_q)`, `U_p = 2(D, N)`. -/
theorem lattice_bridge_exists (frame conj : ChildFrame) (hconj : conj.child = frame.parents.odd.rotate) :
    ∃ j : ℤ, (-frame.eps * frame.parents.even.den, -frame.eps * frame.parents.even.num) =
      (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den),
          conj.eps * (conj.parents.odd.num - conj.parents.odd.den)) +
        (j * (2 * frame.parents.odd.den), j * (2 * frame.parents.odd.num)) := by
  have hdetU : frame.parents.odd.num * frame.parents.even.den -
      frame.parents.even.num * frame.parents.odd.den = frame.eps := frame.eps_det_even
  have hX := conj_child_det frame conj hconj
  have hε := frame.eps_sq_one
  have hεc := conj.eps_sq_one
  have hunit := frame.valid.unit_det
  have hD : 0 < frame.parents.odd.den := frame.valid.odd_bounds.1
  have hev : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hod : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  -- Bezout: N and D are coprime, from det(odd, even) = ±1 (with the even parent's dq, nq).
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.parents.odd.num + v * frame.parents.odd.den = 1 := by
    rcases hunit with h | h
    · exact ⟨frame.parents.even.den, -frame.parents.even.num, by unfold Fraction.det at h; linear_combination h⟩
    · exact ⟨-frame.parents.even.den, frame.parents.even.num, by unfold Fraction.det at h; linear_combination (-1 : ℤ) * h⟩
  -- the difference Δ = (a, b) = −ε U_q − δ₀ satisfies N a = D b (t_p(Δ) = 0)
  set a : ℤ := -frame.eps * frame.parents.even.den -
    (-conj.eps * (conj.parents.odd.num + conj.parents.odd.den)) with ha
  set b : ℤ := -frame.eps * frame.parents.even.num -
    conj.eps * (conj.parents.odd.num - conj.parents.odd.den) with hb
  have hA : frame.parents.odd.num * a = frame.parents.odd.den * b := by
    rw [ha, hb]
    linear_combination (-frame.eps) * hdetU + conj.eps * hX - hε + hεc
  -- a = D k with k = u b + v a
  have hak : a = frame.parents.odd.den * (u * b + v * a) := by
    linear_combination (-a) * huv + u * hA
  have hbk : b = frame.parents.odd.num * (u * b + v * a) := by
    apply mul_left_cancel₀ (ne_of_gt hD)
    linear_combination (-1 : ℤ) * hA + frame.parents.odd.num * hak
  -- evenness: a + b = k (D + N) is even, and D + N is odd
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.parents.even.num + frame.parents.even.den = 2 * m :=
    ⟨(frame.parents.even.num + frame.parents.even.den) / 2, by omega⟩
  set k : ℤ := u * b + v * a with hk
  have hsum : (frame.parents.odd.num + frame.parents.odd.den) * k =
      2 * (-frame.eps * m + conj.eps * conj.parents.odd.den) := by
    have hab : a + b = (frame.parents.odd.num + frame.parents.odd.den) * k := by
      linear_combination hak + hbk
    have hab2 : a + b = 2 * (-frame.eps * m + conj.eps * conj.parents.odd.den) := by
      rw [ha, hb]
      linear_combination (-frame.eps) * hm
    linarith
  have hkeven : Even k := by
    have h1 : Even ((frame.parents.odd.num + frame.parents.odd.den) * k) :=
      ⟨-frame.eps * m + conj.eps * conj.parents.odd.den, by rw [hsum]; ring⟩
    rcases Int.even_mul.mp h1 with h | h
    · exfalso
      rw [Int.even_iff] at h
      omega
    · exact h
  obtain ⟨j, hj⟩ := hkeven
  refine ⟨j, ?_⟩
  have ha' : a = j * (2 * frame.parents.odd.den) := by
    rw [hak, hj]
    ring
  have hb' : b = j * (2 * frame.parents.odd.num) := by
    rw [hbk, hj]
    ring
  rw [ha] at ha'
  rw [hb] at hb'
  apply Prod.ext
  · simp only [Prod.fst_add]
    linarith
  · simp only [Prod.snd_add]
    linarith

end ChildFrame

end FLatticePaper.Induction
