import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.ReciprocalIncrements

/-! The price and slip drifts of the standard field of the pure word `3^k` (`reciprocalField k`), from its periods.

The frame of `3^k` is uniform in `k`: the odd parent is `0/1`, the even parent is `1/(2k+1)`, the child is `1/d` with
`d = 2k+3`, `ε = −1`, `σ = shortShift = (−2, 0)`, `parentShift = (1, −1)` and `parentSlope z = −z₂`. The periods of
`reciprocalField k` are `F(z + K) = F z` and `F(z + T) = F z − grade z + cV` (`reciprocalField_spec`).

The drifts are then immediate: the price `P(z) = F z − F(z − (1,−1)) − z₂` has `P(z + K) − P z = −1` and `P(z + T) − P z = 0`;
the slip `D_η(z) = F z − F(z + η σ)` has `D_η(z + K) − D_η z = 0` and `D_η(z + T) − D_η z = 2η`. -/

namespace FLatticePaper.Induction

open Farey Construction

/-- The even parent of `3^k` is `1/(2k+1)`, the odd parent `0/1`: the frame facts. -/
theorem frameAt_threes_eps (k : ℕ) : (frameAt (List.replicate k Digit.three)).eps = -1 := by
  simp [frameAt, ChildFrame.eps, Fraction.det, parentsAt_replicate_three]

theorem frameAt_threes_shortShift (k : ℕ) : (frameAt (List.replicate k Digit.three)).shortShift = (-2, 0) := by
  simp [frameAt, ChildFrame.shortShift, ChildFrame.eps, Fraction.det, parentsAt_replicate_three]

/-- The parent shift `(1, −1)` of `3^k`. -/
theorem frameAt_threes_parentShift (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).parentShift = (1, -1) := by
  simp [frameAt, ChildFrame.parentShift, ChildFrame.eps, Fraction.det, parentsAt_replicate_three]

/-- The parent slope of `3^k` is `−z₂`. -/
theorem frameAt_threes_parentSlope (k : ℕ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).parentSlope z = -z.2 := by
  unfold frameAt ChildFrame.parentSlope
  simp only [parentsAt_replicate_three]
  simp

/-- The child of `3^k` is `1/(2k+3)`. -/
theorem frameAt_threes_child (k : ℕ) :
    (frameAt (List.replicate k Digit.three)).child = Fraction.mk 1 (2 * (k : ℤ) + 3) := by
  unfold frameAt ChildFrame.child
  simp only [parentsAt_replicate_three]
  apply Fraction.ext <;> simp [Parents.current, Parents.combine]
  all_goals omega

/-- The period `F(w + K) = F w` of `reciprocalField k` (kernel of `1/d`). -/
theorem reciprocalField_period_kernel (k : ℕ) (w : Site) :
    reciprocalField k (w + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.kernel) = reciprocalField k w := by
  have h := ((reciprocalField_spec k).2).1 w
  rw [h]
  simp

/-- The period `F(w + T) = F w − grade w + cV` of `reciprocalField k` (transverse of `1/d`). -/
theorem reciprocalField_period_transverse (k : ℕ) (w : Site) :
    reciprocalField k (w + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.transverse) =
      reciprocalField k w - (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade w +
        stairEvenConstantV (2 * (k : ℤ) + 3) :=
  ((reciprocalField_spec k).2).2 w

/-- The kernel and the transverse period of `1/d` for odd `d`, in coordinates. -/
theorem kernel_threes (k : ℕ) :
    (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.kernel = (2 * (k : ℤ) + 3, 1) := by
  have h := reciprocalEvenDeck_eq (den := 2 * (k : ℤ) + 3) (by omega)
  unfold reciprocalEvenDeck at h
  rw [h]

theorem transverse_threes (k : ℕ) :
    (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.transverse = (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
  have h := reciprocalEvenDeck_eq (den := 2 * (k : ℤ) + 3) (by omega)
  unfold reciprocalEvenDeck at h
  rw [h]

/-- The primitive price of `reciprocalField k` at the pure word, in coordinates. -/
theorem price_threes (k : ℕ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z =
      reciprocalField k z - reciprocalField k (z - (1, -1)) - z.2 := by
  unfold ChildFrame.price
  rw [frameAt_threes_parentShift, frameAt_threes_eps, frameAt_threes_parentSlope]
  ring

/-- **F1 drift of the primitive price (pure words):** `P(z + K) − P z = −1` and `P(z + T) − P z = 0`. -/
theorem priceDrift_threes (k : ℕ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z = -1 ∧
    (frameAt (List.replicate k Digit.three)).price (reciprocalField k)
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate k Digit.three)).price (reciprocalField k) z = 0 := by
  rw [frameAt_threes_child]
  simp only [price_threes, kernel_threes, transverse_threes]
  constructor
  · have h1 : reciprocalField k (z + (2 * (k : ℤ) + 3, 1)) = reciprocalField k z := by
      have := reciprocalField_period_kernel k z
      rwa [kernel_threes] at this
    have h2 : reciprocalField k (z + (2 * (k : ℤ) + 3, 1) - (1, -1)) = reciprocalField k (z - (1, -1)) := by
      have := reciprocalField_period_kernel k (z - (1, -1))
      rw [kernel_threes] at this
      rw [show z + (2 * (k : ℤ) + 3, 1) - (1, -1) = z - (1, -1) + (2 * (k : ℤ) + 3, 1) by abel]
      exact this
    rw [h1, h2]
    simp
  · have h1 : reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
        reciprocalField k z - (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade z +
          stairEvenConstantV (2 * (k : ℤ) + 3) := by
      have := reciprocalField_period_transverse k z
      rwa [transverse_threes] at this
    have h2 : reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) - (1, -1)) =
        reciprocalField k (z - (1, -1)) - (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade (z - (1, -1)) +
          stairEvenConstantV (2 * (k : ℤ) + 3) := by
      have := reciprocalField_period_transverse k (z - (1, -1))
      rw [transverse_threes] at this
      rw [show z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) - (1, -1) =
        z - (1, -1) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) by abel]
      exact this
    rw [h1, h2]
    simp only [Fraction.transverseGrade]
    simp
    ring

/-- The shift `η • shortShift = (−2η, 0)` of the pure word. -/
theorem smul_shortShift_threes (k : ℕ) (η : ℤ) :
    η • (frameAt (List.replicate k Digit.three)).shortShift = (-2 * η, 0) := by
  rw [frameAt_threes_shortShift]
  ext
  · simp; ring
  · simp

/-- **F1 drift of the short slip (pure words):** `D_η(z + K) − D_η z = 0` and `D_η(z + T) − D_η z = 2η`, for `η = ±1`. -/
theorem slipDrift_threes (k : ℕ) (η : ℤ) (z : Site) :
    (frameAt (List.replicate k Digit.three)).slip (reciprocalField k) η
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate k Digit.three)).slip (reciprocalField k) η z = 0 ∧
    (frameAt (List.replicate k Digit.three)).slip (reciprocalField k) η
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate k Digit.three)).slip (reciprocalField k) η z = 2 * η := by
  rw [frameAt_threes_child]
  unfold ChildFrame.slip
  simp only [smul_shortShift_threes]
  rw [kernel_threes, transverse_threes]
  constructor
  · have h1 : reciprocalField k (z + (2 * (k : ℤ) + 3, 1)) = reciprocalField k z := by
      have := reciprocalField_period_kernel k z
      rwa [kernel_threes] at this
    have h2 : reciprocalField k (z + (2 * (k : ℤ) + 3, 1) + (-2 * η, 0)) =
        reciprocalField k (z + (-2 * η, 0)) := by
      have := reciprocalField_period_kernel k (z + (-2 * η, 0))
      rw [kernel_threes] at this
      rw [show z + (2 * (k : ℤ) + 3, 1) + (-2 * η, 0) = z + (-2 * η, 0) + (2 * (k : ℤ) + 3, 1) by abel]
      exact this
    rw [h1, h2]
    ring
  · have h1 : reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3))) =
        reciprocalField k z - (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade z +
          stairEvenConstantV (2 * (k : ℤ) + 3) := by
      have := reciprocalField_period_transverse k z
      rwa [transverse_threes] at this
    have h2 : reciprocalField k (z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (-2 * η, 0)) =
        reciprocalField k (z + (-2 * η, 0)) - (Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade (z + (-2 * η, 0)) +
          stairEvenConstantV (2 * (k : ℤ) + 3) := by
      have := reciprocalField_period_transverse k (z + (-2 * η, 0))
      rw [transverse_threes] at this
      rw [show z + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) + (-2 * η, 0) =
        z + (-2 * η, 0) + (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) by abel]
      exact this
    rw [h1, h2]
    simp only [Fraction.transverseGrade]
    simp
    ring

/-- The `priceDrift` field of `StrongResidual` at the pure word `3^k` (the standard field is `reciprocalField k`). -/
theorem strongResidual_priceDrift_threes (k : ℕ) : ∀ z : Site,
    (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three))
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three)) z = -1 ∧
    (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three))
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate k Digit.three)).price (standardField (List.replicate k Digit.three)) z = 0 := by
  intro z
  rw [standardField_threes]
  exact priceDrift_threes k z

/-- The `slipDrift` field of `StrongResidual` at the pure word `3^k` (for every `η`, in particular `η = ±1`). -/
theorem strongResidual_slipDrift_threes (k : ℕ) : ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ z : Site,
    (frameAt (List.replicate k Digit.three)).slip (standardField (List.replicate k Digit.three)) η
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.kernel) -
      (frameAt (List.replicate k Digit.three)).slip (standardField (List.replicate k Digit.three)) η z = 0 ∧
    (frameAt (List.replicate k Digit.three)).slip (standardField (List.replicate k Digit.three)) η
        (z + (frameAt (List.replicate k Digit.three)).child.modifiedDeck.transverse) -
      (frameAt (List.replicate k Digit.three)).slip (standardField (List.replicate k Digit.three)) η z = 2 * η := by
  intro η _ z
  rw [standardField_threes]
  exact slipDrift_threes k η z

end FLatticePaper.Induction
