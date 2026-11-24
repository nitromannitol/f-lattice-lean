import FLatticePaper.Plane.Induction.TwosChainMono

/-! Task 73: the twos rank `R = (2d+3) Φ₊₁ + ρ` (sign `+1`), with `d = 2k+5`, `M = 2d+3 = 4k+13`.

* `classKey_kernel`, `classKey_transverse`: the class key is invariant under the kernel `(2k+5, 2k+3)` and under the transverse
  `(−2, 4k+8)` (which shifts the key by `−T`), so `rhoTwos` is deck-periodic by definition.
* `chainP_kernel`, `chainP_transverse`: the chain potential of sign `+1` drops by `1` along the kernel and rises by `2` along the
  transverse (the frame's slip and price drifts).
* `twosRank_kernel`, `twosRank_transverse`: the characters of `R`: `R(z + U) = R z − M`, `R(z + V) = R z + 2M`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Induction Farey
open scoped Classical

/-- The class key is invariant under the kernel `(2k+5, 2k+3)` of the twos child. -/
theorem classKey_kernel (k : ℕ) (c : Site) :
    classKey (2 * (k : ℤ) + 4) (c.1 + (2 * (k : ℤ) + 5), c.2 + (2 * (k : ℤ) + 3)) = classKey (2 * (k : ℤ) + 4) c := by
  unfold classKey
  have e : (2 * (k : ℤ) + 4 - 1) * (c.1 + (2 * (k : ℤ) + 5)) - (2 * (k : ℤ) + 4 + 1) * (c.2 + (2 * (k : ℤ) + 3)) =
      (2 * (k : ℤ) + 4 - 1) * c.1 - (2 * (k : ℤ) + 4 + 1) * c.2 := by
    ring
  rw [e]

/-- The class key shifts by `−T` under the transverse `(−2, 4k+8)`, so it is unchanged modulo `T`. -/
theorem classKey_transverse (k : ℕ) (c : Site) :
    classKey (2 * (k : ℤ) + 4) (c.1 + -2, c.2 + (4 * (k : ℤ) + 8)) = classKey (2 * (k : ℤ) + 4) c := by
  unfold classKey
  have e : (2 * (k : ℤ) + 4 - 1) * (c.1 + -2) - (2 * (k : ℤ) + 4 + 1) * (c.2 + (4 * (k : ℤ) + 8)) =
      (2 * (k : ℤ) + 4 - 1) * c.1 - (2 * (k : ℤ) + 4 + 1) * c.2 +
        (-1) * (2 * (2 * (k : ℤ) + 4) * (2 * (k : ℤ) + 4) + 4 * (2 * (k : ℤ) + 4) - 2) := by
    ring
  rw [e, Int.add_emod, Int.mul_emod_left, add_zero, Int.emod_emod]

/-- The deck-periodic part `ρ` is invariant under the kernel. -/
theorem rhoTwos_kernel (k : ℕ) (η : ℤ) (c : Site) :
    rhoTwos (2 * (k : ℤ) + 4) η (c.1 + (2 * (k : ℤ) + 5), c.2 + (2 * (k : ℤ) + 3)) = rhoTwos (2 * (k : ℤ) + 4) η c := by
  unfold rhoTwos
  rw [classKey_kernel]

/-- The deck-periodic part `ρ` is invariant under the transverse. -/
theorem rhoTwos_transverse (k : ℕ) (η : ℤ) (c : Site) :
    rhoTwos (2 * (k : ℤ) + 4) η (c.1 + -2, c.2 + (4 * (k : ℤ) + 8)) = rhoTwos (2 * (k : ℤ) + 4) η c := by
  unfold rhoTwos
  rw [classKey_transverse]

/-- The chain potential of sign `+1` drops by `1` along the kernel. -/
theorem chainP_kernel (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 z - 1 := by
  unfold ChildFrame.chainPotential
  have h1 := twos_slip_drift_kernel k 1 z
  have h2 := twos_price_drift_kernel k (z + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift)
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel := by
    abel
  rw [e]
  linarith

/-- The chain potential of sign `+1` rises by `2` along the transverse. -/
theorem chainP_transverse (k : ℕ) (z : Site) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1
        (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 z + 2 := by
  unfold ChildFrame.chainPotential
  have h1 := twos_slip_drift_transverse k 1 (Or.inl rfl) z
  have h2 := twos_price_drift_transverse k (z + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift)
  have e : z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      (z + (1 : ℤ) • (frameAt (List.replicate (k + 1) Digit.two)).shortShift) +
        (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse := by
    abel
  rw [e]
  linarith

/-- **The twos rank** `R = (2d+3) Φ₊₁ + ρ` with `d = 2k+5` (so `M = 2d+3 = 4k+13`). -/
noncomputable def twosRank (k : ℕ) (z : Site) : ℤ :=
  (2 * (2 * (k : ℤ) + 5) + 3) *
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 z +
    rhoTwos (2 * (k : ℤ) + 4) 1 z

/-- The character of the twos rank on the kernel: `R(z + U) = R z − (2d+3)`. -/
theorem twosRank_kernel (k : ℕ) (z : Site) :
    twosRank k (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      twosRank k z - (2 * (2 * (k : ℤ) + 5) + 3) := by
  unfold twosRank
  rw [chainP_kernel]
  have hr : rhoTwos (2 * (k : ℤ) + 4) 1 (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.kernel) =
      rhoTwos (2 * (k : ℤ) + 4) 1 z := by
    rw [twos_kernel_explicit]
    obtain ⟨c1, c2⟩ := z
    exact rhoTwos_kernel k 1 (c1, c2)
  rw [hr]
  ring

/-- The character of the twos rank on the transverse: `R(z + V) = R z + 2(2d+3)`. -/
theorem twosRank_transverse (k : ℕ) (z : Site) :
    twosRank k (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      twosRank k z + 2 * (2 * (2 * (k : ℤ) + 5) + 3) := by
  unfold twosRank
  rw [chainP_transverse]
  have hr : rhoTwos (2 * (k : ℤ) + 4) 1 (z + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.transverse) =
      rhoTwos (2 * (k : ℤ) + 4) 1 z := by
    rw [twos_transverse_explicit]
    obtain ⟨c1, c2⟩ := z
    exact rhoTwos_transverse k 1 (c1, c2)
  rw [hr]
  ring

end FLatticePaper.TwosEPolicy
