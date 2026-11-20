import FLattice.Auxiliary.FiniteComparison

/-!
# Finite contact escape with an incoming collar

The comparison bound is needed at the two predecessors of every vertex in
the active region. Neither a global lower bound nor periodicity is assumed.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- A finite contact set is empty when its incoming collar is controlled and
the binary holes have the appropriate rank-decreasing predecessors inside
the active region. -/
theorem not_exists_contact_of_finite_rank
    (left right : V → V) (h u : V → ℤ) (rank : V → α)
    (region : Set V) (level : ℤ)
    (hFinite : {z | z ∈ region ∧ h z - u z = level}.Finite)
    (hIncomingLower : ∀ z ∈ region,
      level ≤ h (left z) - u (left z) ∧ level ≤ h (right z) - u (right z))
    (hSuperharmonic : ∀ z ∈ region,
      h (left z) + h (right z) ≤ 2 * h z)
    (hHoles : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 0 ∨
      2 * u z - u (left z) - u (right z) = 1)
    (hZeroRank : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 0 →
      (left z ∈ region ∧ rank (left z) < rank z) ∨
      (right z ∈ region ∧ rank (right z) < rank z))
    (hOneRank : ∀ z ∈ region,
      2 * u z - u (left z) - u (right z) = 1 →
      (left z ∈ region ∧ rank (left z) < rank z) ∧
      (right z ∈ region ∧ rank (right z) < rank z)) :
    ¬∃ z ∈ region, h z - u z = level := by
  apply not_nonempty_of_finite_rank_descent
    {z | z ∈ region ∧ h z - u z = level} rank hFinite
  intro z hz
  obtain ⟨hzRegion, hzContact⟩ := hz
  obtain ⟨hLeft, hRight⟩ := hIncomingLower z hzRegion
  have hStar := hSuperharmonic z hzRegion
  rcases hHoles z hzRegion with hZero | hOne
  · have hLeftContact : h (left z) - u (left z) = level := by omega
    have hRightContact : h (right z) - u (right z) = level := by omega
    rcases hZeroRank z hzRegion hZero with ⟨hMember, hLess⟩ | ⟨hMember, hLess⟩
    · exact ⟨left z, ⟨hMember, hLeftContact⟩, hLess⟩
    · exact ⟨right z, ⟨hMember, hRightContact⟩, hLess⟩
  · have hContact : h (left z) - u (left z) = level ∨
        h (right z) - u (right z) = level := by omega
    obtain ⟨⟨hLeftMember, hLeftLess⟩, ⟨hRightMember, hRightLess⟩⟩ :=
      hOneRank z hzRegion hOne
    rcases hContact with hLeftContact | hRightContact
    · exact ⟨left z, ⟨hLeftMember, hLeftContact⟩, hLeftLess⟩
    · exact ⟨right z, ⟨hRightMember, hRightContact⟩, hRightLess⟩

end FLattice.Auxiliary
