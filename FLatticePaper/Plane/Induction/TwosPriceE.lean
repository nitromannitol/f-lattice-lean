import FLatticePaper.Plane.Induction.TwosTileCover
import FLatticePaper.Plane.Induction.TwosDrifts

/-! Task 72 / twos base: the price range of `standardField (2^(k+1))` on its closed polygon, from the native tile.

On the closed polygon `E`, with `d = 2k+4`, `m = k+2`, the price is `P(z) = F(z) − F(z − v) + ((k+1) z₁ − (k+2) z₂)` for the
parent shift `v = (1, −(d−1))`. The three shifts of `twos_shift_cover` give `F(z − v)` as the near-one closed form at a shifted
point (case A: `z − v`; case B: `z − v − V`, with the transverse constant `cV = 1 − d² − 3d` and the transverse grade; case C:
`z − v + U`). The quadratic terms of the closed form cancel exactly (`sq_div4_add`), and what is left is a piecewise linear
bound on `E`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- `(q + 2c)²/4 = q²/4 + q c + c²` (exact: the difference is a multiple of four). -/
theorem sq_div4_add (q c : ℤ) : (q + 2 * c) ^ 2 / 4 = q ^ 2 / 4 + q * c + c ^ 2 := by
  have h : (q + 2 * c) ^ 2 = q ^ 2 + 4 * (q * c + c ^ 2) := by ring
  rw [h, Int.add_mul_ediv_left _ (q * c + c ^ 2) (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-- The cut price of `2^(k+1)`: `k² + 5k + 5`. -/
theorem twos_cutPrice (k : ℕ) :
    (frameAt (List.replicate (k + 1) Digit.two)).cutPrice = (k : ℤ) ^ 2 + 5 * (k : ℤ) + 5 := by
  unfold ChildFrame.cutPrice
  rw [twos_eps_explicit, twos_parents_explicit]
  simp [Fraction.periodDenominator]
  ring_nf
  omega

/-- The price of `2^(k+1)` in explicit form: `P(z) = F z − F(z₁−1, z₂+2k+3) + ((k+1) z₁ − (k+2) z₂)`. -/
theorem twos_price_unfold (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).price (standardField (List.replicate (k + 1) Digit.two)) z =
      standardField (List.replicate (k + 1) Digit.two) z -
        standardField (List.replicate (k + 1) Digit.two) (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)) +
        (((k : ℤ) + 1) * z.1 - ((k : ℤ) + 2) * z.2) := by
  unfold ChildFrame.price
  rw [twos_eps_explicit, twos_parentSlope_explicit, twos_parentShift_explicit]
  have hs : z - (1, -(2 * (k : ℤ) + 3)) = (z.1 - 1, z.2 + (2 * (k : ℤ) + 3)) := by
    ext
    · simp
    · simp
      ring
  rw [hs]
  ring

/-- The closed-polygon arithmetic of `twos_E_arith` (with `v = z₂ − z₁`), as one predicate. -/
def TwosKey (d z1 z2 : ℤ) : Prop :=
  (-1 ≤ z1 ∧ z1 ≤ d + 1 ∧ -2 ≤ z2 - z1 ∧ z2 - z1 ≤ 2 * d ∧ 0 ≤ z1 + (z2 - z1) ∧
      z1 + (z2 - z1) ≤ 3 * d - 2 ∧ ¬(z1 = -1 ∧ z1 + (z2 - z1) ≤ d) ∧
      ¬(z1 = d + 1 ∧ 2 * d - 2 ≤ z1 + (z2 - z1))) ∨
    (z1 = -1 ∧ z2 - z1 = 2 * d + 1) ∨ (z1 = d + 1 ∧ z2 - z1 = -3) ∨
    (z1 = -1 ∧ z1 + (z2 - z1) = d) ∨ (z1 = d + 1 ∧ z1 + (z2 - z1) = 2 * d - 2)

/-- The closed polygon of `2^(k+1)` satisfies `TwosKey` (the output of `twos_E_arith`). -/
theorem twos_E_key (k : ℕ) (z : Site)
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    TwosKey (2 * (k : ℤ) + 4) z.1 z.2 := by
  obtain ⟨hn, hd⟩ := twos_child_num_den k
  have hT : (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator =
      2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) := by
    simp only [Fraction.periodDenominator, hn, hd]
    ring
  obtain ⟨z1, z2⟩ := z
  rw [ChildFrame.mem_closedPolygon_iff] at hz
  simp only [ChildFrame.tGrade, ChildFrame.sGrade, hn, hd, hT, EvenSite] at hz
  have hu0 : 0 ≤ (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) := by
    rcases hz with ⟨_, _, _, h3, _⟩ | ⟨_, _, _, h3, _⟩ <;> linarith
  have huP : (2 * (k : ℤ) + 4 + 1) * z1 + (z2 - z1) ≤
      (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1 + (2 * (k : ℤ) + 4) - 1 := by
    rcases hz with ⟨_, _, _, _, h4⟩ | ⟨_, _, _, _, h4⟩ <;> linarith
  have hev : (z2 - z1) % 2 = 0 → 2 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ 2 * (2 * (k : ℤ) + 4) - 2 := by
    intro hv
    rcases hz with ⟨_, h1, h2, _, _⟩ | ⟨ho, _⟩
    · exact ⟨by linarith, by linarith⟩
    · exfalso
      omega
  have hod : (z2 - z1) % 2 = 1 → (2 * (k : ℤ) + 4) - 1 - 2 * ((2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 2 * (2 * (k : ℤ) + 4) - 1) ≤
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ∧
      -2 * z1 - (2 * (k : ℤ) + 4 + 1) * (z2 - z1) ≤ (2 * (k : ℤ) + 4) + 1 := by
    intro hv
    rcases hz with ⟨he, _, _, _, _⟩ | ⟨_, h1, h2, _, _⟩
    · exfalso
      omega
    · exact ⟨by linarith, by linarith⟩
  exact twos_E_arith (2 * (k : ℤ) + 4) z1 (z2 - z1) (by omega) hu0 huP hev hod

end FLatticePaper.Induction
