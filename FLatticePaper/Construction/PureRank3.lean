import FLatticePaper.Construction.PureRank2

-- PureRank3: part 3 of 5; declarations from free_root_gate to gate_int_one_left.
namespace FLatticePaper.PureRank
open Classical

set_option maxHeartbeats 400000 in
/-- The free-root gate: for a free native point with prescribed direction `(dx,dy)`, every rank of the target `p + (dx,dy)`
is below the rank of the point. -/
theorem free_root_gate (d : ℤ) (hd : 3 ≤ d) (x y dx dy : ℤ) (hf : IsFreeP d (x, y))
    (hdir : prescribedFree d (x, y) = (dx, dy)) (r : ℤ) (hr : RankOf d (x + dx, y + dy) r) :
    r < valMinus d (x, y) := by
  simp only [prescribedFree] at hdir
  unfold IsFreeP at hf
  split_ifs at hdir with h1 h2 h3
  · simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    unfold IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hf
    rcases hf with ⟨hy, hx1, hxd⟩ | ⟨hx0, hy0⟩ | ⟨hs, hy1, hy2⟩ | ⟨hx2, hyd⟩
    · subst hy
      rw [valMinus_H_even d x (by omega) hxd (by omega)]
      exact gate_H_even_all d x hd (by omega) hxd (by omega) r
        (by rwa [show x + -1 = x - 1 by ring, show (0:ℤ) + 0 = 0 by ring] at hr)
    · subst hx0; subst hy0
      rw [valMinus_origin d]
      exact gate_origin_all d hd r (by rwa [show (0:ℤ) + -1 = -1 by ring, show (0:ℤ) + 0 = 0 by ring] at hr)
    · exfalso; omega
    · subst hx2; subst y
      rw [valMinus_Vlast d hd]
      exact gate_Vlast_all d hd r
        (by rwa [show 2 - d + -1 = 1 - d by ring, show d + 0 = d by ring] at hr)
  · simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    have hy : y = 0 := h2.1
    have hx1 : 1 ≤ x := h2.2.1
    have hxd : x ≤ d := h2.2.2
    have hxd' : x = d := h3
    subst hy
    rw [hxd'] at hr ⊢
    rw [valMinus_H_odd d d (by omega) le_rfl (by omega)]
    exact gate_H_d_all d hd r (by rwa [show d + 0 = d by ring, show (0:ℤ) + 1 = 1 by ring] at hr)
  · simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    have hy : y = 0 := h2.1
    have hx1 : 1 ≤ x := h2.2.1
    have hxd : x ≤ d := h2.2.2
    have hxlt : x < d := lt_of_le_of_ne hxd h3
    subst hy
    rw [valMinus_H_odd d x hx1 hxd (by omega)]
    exact gate_H_odd_all d x hd hx1 hxlt (by omega) r
      (by rwa [show x + 0 = x by ring, show (0:ℤ) + -1 = -1 by ring] at hr)
  · simp only [Prod.mk.injEq] at hdir
    obtain ⟨rfl, rfl⟩ := hdir
    have hnH : ¬ (y = 0 ∧ 1 ≤ x ∧ x ≤ d) := fun h => h2 (show IsHc d (x, y) from ⟨h.1, h.2.1, h.2.2⟩)
    rcases hf with ⟨hy, hx1, hxd⟩ | ⟨hx0, hy0⟩ | ⟨hs, hy1, hy2⟩ | ⟨hx2, hyd⟩
    · exact absurd ⟨hy, hx1, hxd⟩ hnH
    · exfalso; omega
    · have hyx : y = 1 - x := by omega
      subst hyx
      rw [valMinus_V_odd d x (by omega) (by omega)]
      exact gate_V_odd_all d x hd (by omega) (by omega) r
        (by rwa [show x + 0 = x by ring, show 1 - x + 1 = 2 - x by ring] at hr)
    · exfalso; omega

/-! ## The bulk gates (step (ii)): drops along the parity-axis edges that the white predicate can retain

Interior points (native, not free, below the top row, off the anti-diagonal, not `(d,1)`) and the boundary families. Each gate
states that every rank of the target is below the rank of the source. The retained edges are a subset of the listed directions, which
the white predicate (next section) establishes. -/

set_option hygiene false in
/-- The target-side analysis of a gate: every representative translate of the target has a rank below the bound. -/
macro "gate_tac" : tactic => `(tactic| (
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)))

/-- Interior values for `x ≥ 1`, off the diagonal `x+y = d+1`: `valMinus = 4d − 4 − 2x + parity`. -/
theorem valMinus_int_right (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : 1 ≤ x) (hdiag : x + y ≠ d + 1) :
    valMinus d (x, y) = 4 * d - 4 - 2 * x + (x + y) % 2 := by
  have h1 : ¬ IsHc d (x, y) := fun h => hf (Or.inl h)
  have h2 : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  have h3 : ¬ (x + y = d + 1 ∧ 1 ≤ x) := fun h => hdiag h.1
  dsimp only [valMinus]
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg (show ¬ (x ≤ 0) by omega)]

/-- Interior values for `x ≥ 1` on the diagonal `x+y = d+1`: `valMinus = 2x`. -/
theorem valMinus_int_diag (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : 1 ≤ x) (hdiag : x + y = d + 1) :
    valMinus d (x, y) = 2 * x := by
  have h1 : ¬ IsHc d (x, y) := fun h => hf (Or.inl h)
  have h2 : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  dsimp only [valMinus]
  rw [if_neg h1, if_neg h2, if_pos (show x + y = d + 1 ∧ 1 ≤ x from ⟨hdiag, hx⟩)]

/-- The interior value on the left: `valMinus = 2x − 4 + parity` for an interior point with `x ≤ 0`. -/
theorem valMinus_int_left (d x y : ℤ) (hf : ¬ IsFreeP d (x, y)) (hx : x ≤ 0) :
    valMinus d (x, y) = 2 * x - 4 + (x + y) % 2 := by
  have h1 : ¬ IsHc d (x, y) := fun h => by
    obtain ⟨-, h1x, -⟩ := h
    have : 1 ≤ x := h1x
    omega
  have h2 : ¬ IsVc d (x, y) := fun h => hf (Or.inr h)
  have h3 : ¬ (x + y = d + 1 ∧ 1 ≤ x) := fun h => by omega
  dsimp only [valMinus]
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos hx]

set_option maxHeartbeats 400000 in
/-- Interior even point with `x ≤ 0` (its retained edge is `(−1, 0)`): the target `(x−1, y)` has every rank below the point's rank. -/
theorem gate_int_left_even (d x y : ℤ) (hd : 3 ≤ d) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hpar : (x + y) % 2 = 0) (hx : x ≤ 0) (r : ℤ) (hr : RankOf d (x - 1, y) r) :
    r < valMinus d (x, y) := by
  rw [valMinus_int_left d x y hf hx]
  have hb : 2 - d ≤ x ∧ 0 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 ∧ y ≤ d + 1 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  rcases rep_cases d _ hrep with hF | hR
  all_goals
    interval_cases i <;> interval_cases j <;>
    (unfold valMinus; simp only [shiftP, IsHc, IsVc, IsFreeP, NativeP, Prod.mk.injEq] at *; split_ifs <;> omega)


theorem gate_int_right_even_am2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) (-1))) :
    valMinus d (shiftP d (x + 1, y) (-2) (-1)) - (-2) * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

set_option maxHeartbeats 400000 in
theorem gate_int_right_even_am2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) 0)) :
    valMinus d (shiftP d (x + 1, y) (-2) 0) - (-2) * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_am2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-2) 1)) :
    valMinus d (shiftP d (x + 1, y) (-2) 1) - (-2) * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_am1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) (-1))) :
    valMinus d (shiftP d (x + 1, y) (-1) (-1)) - (-1) * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_am1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) 0)) :
    valMinus d (shiftP d (x + 1, y) (-1) 0) - (-1) * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_am1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) (-1) 1)) :
    valMinus d (shiftP d (x + 1, y) (-1) 1) - (-1) * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a0_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 (-1))) :
    valMinus d (shiftP d (x + 1, y) 0 (-1)) - 0 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a0_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 0)) :
    valMinus d (shiftP d (x + 1, y) 0 0) - 0 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a0_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 0 1)) :
    valMinus d (shiftP d (x + 1, y) 0 1) - 0 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a1_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 (-1))) :
    valMinus d (shiftP d (x + 1, y) 1 (-1)) - 1 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a1_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 0)) :
    valMinus d (shiftP d (x + 1, y) 1 0) - 1 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a1_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 1 1)) :
    valMinus d (shiftP d (x + 1, y) 1 1) - 1 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a2_m1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 (-1))) :
    valMinus d (shiftP d (x + 1, y) 2 (-1)) - 2 * (2 * d) + (-1) * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a2_0 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 0)) :
    valMinus d (shiftP d (x + 1, y) 2 0) - 2 * (2 * d) + 0 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even_a2_1 (d x y : ℤ) (hB : 3 ≤ d ∧ d % 2 = 1 ∧ y ≤ d ∧ x + y ≠ d + 1 ∧ ¬ (x = d ∧ y = 1) ∧ 1 ≤ x ∧ (x + y) % 2 = 0 ∧ 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) (hrep : IsRepP d (shiftP d (x + 1, y) 2 1)) :
    valMinus d (shiftP d (x + 1, y) 2 1) - 2 * (2 * d) + 1 * (2 * (d + 1)) < 4 * d - 4 - 2 * x + (x + y) % 2 := by
  rcases rep_cases d _ hrep with hF | hR
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, IsFreeP, Prod.mk.injEq] at hF ⊢
    split_ifs <;> omega
  · unfold valMinus
    simp only [shiftP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hR ⊢
    split_ifs <;> omega

theorem gate_int_right_even (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (hdiag : x + y ≠ d + 1) (h5 : ¬ (x = d ∧ y = 1)) (hx : 1 ≤ x) (hpar : (x + y) % 2 = 0)
    (r : ℤ) (hr : RankOf d (x + 1, y) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_right d x y hf hx hdiag]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  obtain ⟨i, j, hi, hrep, rfl⟩ := hr
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  interval_cases i <;> interval_cases j
  · exact gate_int_right_even_am2_m1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_am2_0 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_am2_1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_am1_m1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_am1_0 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_am1_1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a0_m1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a0_0 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a0_1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a1_m1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a1_0 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a1_1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a2_m1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a2_0 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep
  · exact gate_int_right_even_a2_1 d x y ⟨hd, hdodd, hy, hdiag, h5, hx, hpar, hb1, hb2, hb3, hb4, hb5⟩ hrep

set_option maxHeartbeats 400000 in
/-- Interior even point on the diagonal `x + y = d+1` with `x ≥ 1`: the target `(x+1, y)` has every rank below `2x`. -/
theorem gate_int_diag_right (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (h5 : ¬ (x = d ∧ y = 1)) (hx : 1 ≤ x) (hdiag : x + y = d + 1)
    (r : ℤ) (hr : RankOf d (x + 1, y) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_diag d x y hf hx hdiag]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf
  gate_tac

set_option maxHeartbeats 400000 in
/-- The point `(1, y)` (even, off the diagonal, `y < d`): the left neighbour `(0, y)` has every rank below the point's. -/
theorem gate_int_one_left (d x y : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (hn : NativeP d (x, y))
    (hf : ¬ IsFreeP d (x, y)) (hy : y ≤ d) (hx1 : x = 1) (hdiag : x + y ≠ d + 1)
    (hpar : (x + y) % 2 = 0) (r : ℤ) (hr : RankOf d (x - 1, y) r) : r < valMinus d (x, y) := by
  rw [valMinus_int_right d x y hf (by omega) hdiag]
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 1 ≤ y ∧ 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    unfold NativeP at hn
    unfold IsFreeP IsHc IsVc at hf
    simp only [Prod.mk.injEq] at hn hf
    omega
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  clear hn hf hdiag
  gate_tac

