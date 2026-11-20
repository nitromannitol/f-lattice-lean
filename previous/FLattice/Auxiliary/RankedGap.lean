import FLattice.Auxiliary.FiniteComparison

/-!
# Raising an integer comparison gap by one layer

Generic conditional infrastructure for two incoming predecessors. The
region may be infinite: only the set below the next layer must be finite.
No lattice, profile, collar, or growth theorem is assumed implicitly.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- A zero/one-hole rank raises an integer gap from `b` to `b + 1`.
The lower bound includes the entire incoming collar. Sources already
have the next layer. Reapplying this theorem uses the same rank. -/
theorem gap_next_layer_of_finite_bad_set
    (left right : V → V) (h u : V → ℤ) (rank : V → α)
    (region source : Set V) (b : ℤ)
    (hFinite : {z | z ∈ region ∧ h z - u z ≤ b}.Finite)
    (hLower : ∀ z ∈ region,
      b ≤ h z - u z ∧
      b ≤ h (left z) - u (left z) ∧
      b ≤ h (right z) - u (right z))
    (hSource : ∀ z ∈ source, b + 1 ≤ h z - u z)
    (hSuperharmonic : ∀ z ∈ region,
      h (left z) + h (right z) ≤ 2 * h z)
    (hHoles : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 0 ∨
      2 * u z - u (left z) - u (right z) = 1)
    (hZeroRank : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 0 →
      (left z ∈ source ∨ left z ∈ region ∧ rank (left z) < rank z) ∨
      (right z ∈ source ∨ right z ∈ region ∧ rank (right z) < rank z))
    (hOneRank : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 1 →
      (left z ∈ source ∨ left z ∈ region ∧ rank (left z) < rank z) ∧
      (right z ∈ source ∨ right z ∈ region ∧ rank (right z) < rank z)) :
    ∀ z ∈ region, b + 1 ≤ h z - u z := by
  have hNoBad : ¬{z | z ∈ region ∧ h z - u z ≤ b}.Nonempty := by
    apply not_nonempty_of_finite_rank_descent
      {z | z ∈ region ∧ h z - u z ≤ b} rank hFinite
    intro z hz
    obtain ⟨hzRegion, hzBad⟩ := hz
    obtain ⟨hCenter, hLeft, hRight⟩ := hLower z hzRegion
    have hCenterEq : h z - u z = b := by omega
    have hStar := hSuperharmonic z hzRegion
    have hNext : ∀ w, h w - u w = b →
        (w ∈ source ∨ w ∈ region ∧ rank w < rank z) →
        ∃ w ∈ {z | z ∈ region ∧ h z - u z ≤ b}, rank w < rank z := by
      intro w hw hChoice
      rcases hChoice with hwSource | ⟨hwRegion, hwRank⟩
      · have hImproved := hSource w hwSource
        omega
      · exact ⟨w, ⟨hwRegion, le_of_eq hw⟩, hwRank⟩
    rcases hHoles z hzRegion with hZero | hOne
    · have hLeftEq : h (left z) - u (left z) = b := by omega
      have hRightEq : h (right z) - u (right z) = b := by omega
      rcases hZeroRank z hzRegion hZero with hChoice | hChoice
      · exact hNext (left z) hLeftEq hChoice
      · exact hNext (right z) hRightEq hChoice
    · have hEither : h (left z) - u (left z) = b ∨
          h (right z) - u (right z) = b := by omega
      obtain ⟨hLeftChoice, hRightChoice⟩ := hOneRank z hzRegion hOne
      rcases hEither with hLeftEq | hRightEq
      · exact hNext (left z) hLeftEq hLeftChoice
      · exact hNext (right z) hRightEq hRightChoice
  intro z hz
  by_contra hFailure
  have hBad : h z - u z ≤ b := by omega
  exact hNoBad ⟨z, hz, hBad⟩

end FLattice.Auxiliary
