import FLatticePaper.Plane.Induction.TwosSlipMono

/-! Task 72 / twos base: the chain potential `Φ = D + P(· + σ)` (sign `+1`) does not increase along the selected inputs.

Since `σ = (1,1) − U`, the chain potential is `Φ(z) = D(z) + P(z + (1,1)) + 1` (`twosP_negU`). The claim `Ψ(j) ≤ Ψ(u)` for
`Ψ = D + P(· + (1,1))` is a combination of the slip claim `D(j) ≤ D(u)` and the price band at the shifted pair: it holds when
`D(j) < D(u)` or when the price band of the shifted centre implies that of the shifted input. Each branch supplies its own
lattice translate `t` for the shifted pair (`t = 0` for most, `t = -U` or `-V` on a few boundary strips), with the price
character `c` of `t`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The price indicator of a key point: `0` off the band `TwosDelta`, `1` on it. -/
noncomputable def twosDi (k : ℕ) (z1 z2 : ℤ) : ℤ := if TwosDelta k z1 z2 then 1 else 0

/-- The price of a key point, in the indicator form `C - δ` with the constant `C = k²+5k+5`. -/
theorem twosP_eq_sub (k : ℕ) {z1 z2 : ℤ} (hk : TwosKey (2 * (k : ℤ) + 4) z1 z2) (C : ℤ)
    (hC : C = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5) : twosP k (z1, z2) = C - twosDi k z1 z2 := by
  unfold twosDi
  rcases twos_price_delta k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hP : twosP k (z1, z2) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := h1
    rw [if_neg h2, hP, hC]
    ring
  · have hP : twosP k (z1, z2) = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 4 := h1
    rw [if_pos h2, hP, hC]
    ring

/-- The indicator is `0` or `1`. -/
theorem twosDi_zero_or_one (k : ℕ) (z1 z2 : ℤ) : twosDi k z1 z2 = 0 ∨ twosDi k z1 z2 = 1 := by
  unfold twosDi
  split_ifs <;> simp

/-- **The chain claim along a translated shifted pair.** For a translate `(t1, t2)` of the shifted pair with price character
`c`, the chain claim follows from the slip claim and the band disjunction at the translated pair. -/
theorem twosChain_le_tr (k : ℕ) {u j : ℤ × ℤ} (t1 t2 c : ℤ)
    (hP : ∀ z1 z2 : ℤ, twosP k (z1 + t1, z2 + t2) = twosP k (z1, z2) + c)
    (hD : twosSlip k j ≤ twosSlip k u)
    (hu : TwosKey (2 * (k : ℤ) + 4) (u.1 + 1 + t1) (u.2 + 1 + t2))
    (hj : TwosKey (2 * (k : ℤ) + 4) (j.1 + 1 + t1) (j.2 + 1 + t2))
    (hdisj : (¬ TwosDelta k (u.1 + 1 + t1) (u.2 + 1 + t2) ∨ TwosDelta k (j.1 + 1 + t1) (j.2 + 1 + t2)) ∨
      twosSlip k j < twosSlip k u) :
    twosSlip k j + twosP k (j.1 + 1, j.2 + 1) ≤ twosSlip k u + twosP k (u.1 + 1, u.2 + 1) := by
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := ⟨_, rfl⟩
  have hPu : twosP k (u.1 + 1 + t1, u.2 + 1 + t2) = twosP k (u.1 + 1, u.2 + 1) + c := hP (u.1 + 1) (u.2 + 1)
  have hPj : twosP k (j.1 + 1 + t1, j.2 + 1 + t2) = twosP k (j.1 + 1, j.2 + 1) + c := hP (j.1 + 1) (j.2 + 1)
  have eu := twosP_eq_sub k hu C hC
  have ej := twosP_eq_sub k hj C hC
  have bu := twosDi_zero_or_one k (u.1 + 1 + t1) (u.2 + 1 + t2)
  have bj := twosDi_zero_or_one k (j.1 + 1 + t1) (j.2 + 1 + t2)
  have hdi : (twosDi k (u.1 + 1 + t1) (u.2 + 1 + t2) = 0 ∨ twosDi k (j.1 + 1 + t1) (j.2 + 1 + t2) = 1) ∨
      twosSlip k j < twosSlip k u := by
    rcases hdisj with (h | h) | h
    · left
      left
      unfold twosDi
      by_cases hu' : TwosDelta k (u.1 + 1 + t1) (u.2 + 1 + t2)
      · exact absurd hu' h
      · simp [hu']
    · left
      right
      unfold twosDi
      simp [h]
    · exact Or.inr h
  clear hdisj
  have eu' : twosP k (u.1 + 1, u.2 + 1) = C - twosDi k (u.1 + 1 + t1) (u.2 + 1 + t2) - c := by
    have : twosP k (u.1 + 1 + t1, u.2 + 1 + t2) = C - twosDi k (u.1 + 1 + t1) (u.2 + 1 + t2) := eu
    linarith
  have ej' : twosP k (j.1 + 1, j.2 + 1) = C - twosDi k (j.1 + 1 + t1) (j.2 + 1 + t2) - c := by
    have : twosP k (j.1 + 1 + t1, j.2 + 1 + t2) = C - twosDi k (j.1 + 1 + t1) (j.2 + 1 + t2) := ej
    linarith
  rw [eu', ej']
  clear eu ej hPu hPj hP eu' ej' hC
  omega

/-- The translation `0` of the shifted pair. -/
theorem twosP_shift0 (k : ℕ) : ∀ z1 z2 : ℤ, twosP k (z1 + 0, z2 + 0) = twosP k (z1, z2) + 0 := by
  intro z1 z2
  simp

/-- The translation `-U` of the shifted pair: the price rises by one. -/
theorem twosP_shiftU (k : ℕ) : ∀ z1 z2 : ℤ,
    twosP k (z1 + -(2 * (k : ℤ) + 5), z2 + -(2 * (k : ℤ) + 3)) = twosP k (z1, z2) + 1 := by
  intro z1 z2
  have h := twosP_negU k z1 z2
  rw [sub_eq_add_neg, sub_eq_add_neg] at h
  linarith

/-- The translation `-V` of the shifted pair: the price does not change. -/
theorem twosP_shiftV (k : ℕ) : ∀ z1 z2 : ℤ,
    twosP k (z1 + 2, z2 + -(4 * (k : ℤ) + 8)) = twosP k (z1, z2) + 0 := by
  intro z1 z2
  have h := twosP_negV k z1 z2
  rw [sub_neg_eq_add, sub_eq_add_neg] at h
  linarith


/-- The translation `V` of the shifted pair: the price does not change. -/
theorem twosP_shiftVp (k : ℕ) : ∀ z1 z2 : ℤ, twosP k (z1 + -2, z2 + (4 * (k : ℤ) + 8)) = twosP k (z1, z2) + 0 := by
  intro z1 z2
  have h := twosP_V k z1 z2
  linarith

/-- Chain claim, free family `H0` (sign `+1`). -/
theorem chainD_p_H0 (k : ℕ) {x y : ℤ} (h : x = 1 ∧ y = 0) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) (x + (-2)) (y + (4 * (k : ℤ) + 8)) := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (0) + (-2)) (y + (-1) + (4 * (k : ℤ) + 8)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (-2)) (y + (4 * (k : ℤ) + 8)))
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (0) + (-2)) (y + (-1) + (4 * (k : ℤ) + 8)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  have ru := twosSlip_V k (x) (y)
  have ru := twosSlip_V k (x + (0)) (y + (-1))
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) (freeD_p_H0 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Hlt` (sign `+1`). -/
theorem chainD_p_Hlt (k : ℕ) {x y : ℤ} (h : 2 ≤ x ∧ x ≤ 2 * (k : ℤ) + 3 ∧ y = x - 2) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) (x + (-2)) (y + (4 * (k : ℤ) + 8)) := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (1) + (-2)) (y + (0) + (4 * (k : ℤ) + 8)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (-2)) (y + (4 * (k : ℤ) + 8)))
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (1) + (-2)) (y + (0) + (4 * (k : ℤ) + 8)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  have ru := twosSlip_V k (x) (y)
  have ru := twosSlip_V k (x + (1)) (y + (0))
  by_cases hx : x = 2 * (k : ℤ) + 3
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) 0 0 0 (twosP_shift0 k) (freeD_p_Hlt k h) ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) (-2) (4 * (k : ℤ) + 8) 0 (twosP_shiftVp k) (freeD_p_Hlt k h) ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Heq` (sign `+1`). -/
theorem chainD_p_Heq (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 4 ∧ y = 2 * (k : ℤ) + 2) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) (freeD_p_Heq k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Hodd` (sign `+1`). -/
theorem chainD_p_Hodd (k : ℕ) {x y : ℤ} (h : x = 2 * (k : ℤ) + 5 ∧ y = 2 * (k : ℤ) + 2) :
    twosSlip k (x + (0), y + (1)) + twosP k (x + (0) + 1, y + (1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (1)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (1))) (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) (freeD_p_Hodd k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `V0` (sign `+1`). -/
theorem chainD_p_V0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ y = 0) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) 0 0 0 (twosP_shift0 k) (freeD_p_V0 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Ve0` (sign `+1`). -/
theorem chainD_p_Ve0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 0)) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) 0 0 0 (twosP_shift0 k) (freeD_p_Ve0 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Vo0` (sign `+1`). -/
theorem chainD_p_Vo0 (k : ℕ) {x y : ℤ} (h : x = 0 ∧ 0 < y ∧ y < 2 * (k : ℤ) + 4 ∧ (y % 2 = 1)) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) (freeD_p_Vo0 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Ve1` (sign `+1`). -/
theorem chainD_p_Ve1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 ≤ y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 1)) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) 0 0 0 (twosP_shift0 k) (freeD_p_Ve1 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Vo1a` (sign `+1`). -/
theorem chainD_p_Vo1a (k : ℕ) {x y : ℤ} (h : x = -1 ∧ y = 2 * (k : ℤ) + 4) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) (x + (2 * (k : ℤ) + 5)) (y + (2 * (k : ℤ) + 3)) := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (0) + (2 * (k : ℤ) + 5)) (y + (-1) + (2 * (k : ℤ) + 3)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (2 * (k : ℤ) + 5)) (y + (2 * (k : ℤ) + 3)))
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (0) + (2 * (k : ℤ) + 5)) (y + (-1) + (2 * (k : ℤ) + 3)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  have ru := twosSlip_U k (x) (y)
  have ru := twosSlip_U k (x + (0)) (y + (-1))
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) (freeD_p_Vo1a k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, free family `Vo1` (sign `+1`). -/
theorem chainD_p_Vo1 (k : ℕ) {x y : ℤ} (h : x = -1 ∧ 2 * (k : ℤ) + 4 < y ∧ y < 2 * (2 * (k : ℤ) + 4) ∧ (y % 2 = 0)) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hkU : TwosKey (2 * (k : ℤ) + 4) x y := by unfold TwosKey; omega
  have hkJ : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) x y)
  have v2 := twos_slip_value k (by unfold TwosKey; omega : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)))
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) (freeD_p_Vo1 k h) ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- **The free branch of the chain claim.** -/
theorem freeChain_mono (k : ℕ) {x y : ℤ} (hF : FreeSite (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (freeDisp (2 * (k : ℤ) + 4) 1 x y).1, y + (freeDisp (2 * (k : ℤ) + 4) 1 x y).2) +
        twosP k (x + (freeDisp (2 * (k : ℤ) + 4) 1 x y).1 + 1, y + (freeDisp (2 * (k : ℤ) + 4) 1 x y).2 + 1) ≤
      twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hF' := hF
  unfold FreeSite FreeHSite FreeVSite at hF'
  · rcases hF' with (h | h | h) | (h | h)
    · rw [freeDisp_H0 h]; exact chainD_p_H0 k h
    · rw [freeDisp_Heven (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      by_cases hea : x = 2 * (k : ℤ) + 4
      · exact chainD_p_Heq k ⟨hea, by omega⟩
      · exact chainD_p_Hlt k ⟨by omega, by omega, by omega⟩
    · rw [freeDisp_Hodd (by unfold FreeHSite; omega) (by omega) (by unfold EvenSite; dsimp only; omega)]
      exact chainD_p_Hodd k ⟨by omega, by omega⟩
    · by_cases hz : x = 0 ∧ y = 0
      · rw [freeDisp_V0 hz]; exact chainD_p_V0 k hz
      · by_cases he : EvenSite (x, y)
        · rw [freeDisp_Veven (by unfold FreeVSite; omega) hz he]
          exact chainD_p_Ve0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
        · rw [freeDisp_Vodd (by unfold FreeVSite; omega) hz he]
          exact chainD_p_Vo0 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
    · by_cases he : EvenSite (x, y)
      · rw [freeDisp_Veven (by unfold FreeVSite; omega) (by omega) he]
        exact chainD_p_Ve1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩
      · rw [freeDisp_Vodd (by unfold FreeVSite; omega) (by omega) he]
        by_cases hay : y = 2 * (k : ℤ) + 4
        · exact chainD_p_Vo1a k ⟨by omega, hay⟩
        · exact chainD_p_Vo1 k ⟨by omega, by omega, by omega, by unfold EvenSite at he; dsimp only at he; omega⟩

/-- Chain claim, candidate guard `low_down` (sign `+1`). -/
theorem chainC_low_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_low_down k hn hL hm
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandLow at hL
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, candidate guard `low_up` (sign `+1`). -/
theorem chainC_low_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hL : CandLow (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (k : ℤ) + 4 - 1) :
    twosSlip k (x + (0), y + (1)) + twosP k (x + (0) + 1, y + (1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_low_up k hn hL hm
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandLow at hL
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  by_cases hex : x = 2 * (k : ℤ) + 4 ∧ y = 2 * (2 * (k : ℤ) + 4) - 3
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (1))) (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (1))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, candidate guard `high_down` (sign `+1`). -/
theorem chainC_high_down (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k (x + (0), y + (-1)) + twosP k (x + (0) + 1, y + (-1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_high_down k hn hH hm
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandHigh at hH
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (-1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (-1))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, candidate guard `high_up` (sign `+1`). -/
theorem chainC_high_up (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hH : CandHigh (2 * (k : ℤ) + 4) x y) (hm : ¬ y < 2 * (2 * (k : ℤ) + 4) - 1) :
    twosSlip k (x + (0), y + (1)) + twosP k (x + (0) + 1, y + (1) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_high_up k hn hH hm
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandHigh at hH
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (0)) (y + (1)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  by_cases hex : x = 2 * (k : ℤ) + 4 - 2 ∧ y = 3 * (2 * (k : ℤ) + 4) - 3
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (1))) 2 (-(4 * (k : ℤ) + 8)) 0 (twosP_shiftV k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (0), y + (1))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, candidate guard `E` (sign `+1`). -/
theorem chainC_E (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hE : CandE (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (1), y + (0)) + twosP k (x + (1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_E k hn hE
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandE at hE
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  by_cases hex : x = 2 * (k : ℤ) + 4
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) (-(2 * (k : ℤ) + 5)) (-(2 * (k : ℤ) + 3)) 1 (twosP_shiftU k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)
  · refine twosChain_le_tr k (u := (x, y)) (j := (x + (1), y + (0))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
    all_goals try dsimp only
    all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- Chain claim, candidate guard `W` (sign `+1`). -/
theorem chainC_W (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hW : CandW (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (-1), y + (0)) + twosP k (x + (-1) + 1, y + (0) + 1) ≤ twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  have hD := candD_mono_W k hn hW
  have hk1 : TwosKey (2 * (k : ℤ) + 4) x y := twosKey_of_native hn
  unfold NativeT at hn
  unfold CandW at hW
  have hk2 : TwosKey (2 * (k : ℤ) + 4) (x + (-1)) (y + (0)) := by unfold TwosKey; omega
  have v1 := twos_slip_value k hk1
  have v2 := twos_slip_value k hk2
  unfold TwosSlipZ0 TwosSlipZ2 at v1 v2
  refine twosChain_le_tr k (u := (x, y)) (j := (x + (-1), y + (0))) 0 0 0 (twosP_shift0 k) hD ?_ ?_ ?_
  all_goals try dsimp only
  all_goals first | (unfold TwosKey; omega) | (unfold TwosDelta; omega)

/-- **The candidate branch of the chain claim.** -/
theorem chainC_mono (k : ℕ) {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hg : CandGuard (2 * (k : ℤ) + 4) x y) :
    twosSlip k (x + (candDisp (2 * (k : ℤ) + 4) x y).1, y + (candDisp (2 * (k : ℤ) + 4) x y).2) +
        twosP k (x + (candDisp (2 * (k : ℤ) + 4) x y).1 + 1, y + (candDisp (2 * (k : ℤ) + 4) x y).2 + 1) ≤
      twosSlip k (x, y) + twosP k (x + 1, y + 1) := by
  rcases hg with hL | hH | hE | hW
  · by_cases hm : y < 2 * (k : ℤ) + 4 - 1
    · rw [candDisp_low_down hL hm]; exact chainC_low_down k hn hL hm
    · rw [candDisp_low_up hL hm]; exact chainC_low_up k hn hL hm
  · by_cases hm : y < 2 * (2 * (k : ℤ) + 4) - 1
    · rw [candDisp_high_down hH hm]; exact chainC_high_down k hn hH hm
    · rw [candDisp_high_up hH hm]; exact chainC_high_up k hn hH hm
  · rw [candDisp_E hE]; exact chainC_E k hn hE
  · rw [candDisp_W hW]; exact chainC_W k hn hW


end FLatticePaper.TwosEPolicy
