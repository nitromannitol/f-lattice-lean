import FLattice.Auxiliary.IncomingGap
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Integer comparison with a bounded clock

An integer gap bounded below attains its minimum even when its minimum
set is infinite. A bounded-below integer clock chooses a second minimum.
Enough incoming slots with smaller clocks rule out a negative minimum.
The incoming slots retain multiplicity, and the Laplacian cap is arbitrary.
This is conditional graph-independent infrastructure, not a lattice theorem.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

open scoped BigOperators

/-- An integer-valued function bounded below on a nonempty set attains a
minimum there; the set need not be finite. -/
theorem exists_min_image_of_int_bounded_below {V : Type*}
    (s : Set V) (f : V → ℤ) (hNonempty : s.Nonempty)
    (hBounded : ∃ B : ℤ, ∀ z ∈ s, B ≤ f z) :
    ∃ z ∈ s, ∀ w ∈ s, f z ≤ f w := by
  obtain ⟨B, hB⟩ := hBounded
  have hImageNonempty : (f '' s).Nonempty := hNonempty.image f
  have hImageBounded : BddBelow (f '' s) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hB z hz
  obtain ⟨z, hz, hValue⟩ := Int.csInf_mem hImageNonempty hImageBounded
  refine ⟨z, hz, ?_⟩
  intro w hw
  rw [hValue]
  exact csInf_le hImageBounded ⟨w, hw, rfl⟩

/-- A prescribed lower profile is a global lower bound when its gap and
clock are bounded below and sufficiently many incoming slots lower the clock.
No finite contact set, graph symmetry, or periodicity of the unknown is assumed. -/
theorem le_of_bounded_gap_and_rank {V ι : Type*} [Fintype ι]
    (incoming : V → ι → V) (h u : V → ℤ) (cap rank : V → ℤ)
    (prescribed : Set V)
    (hGapBounded : ∃ B : ℤ, ∀ z, B ≤ h z - u z)
    (hRankBounded : ∃ B : ℤ, ∀ z, B ≤ rank z)
    (hCapped : ∀ z,
      (∑ i, h (incoming z i)) - (Fintype.card ι : ℤ) * h z ≤ cap z)
    (hPrescribed : ∀ z ∈ prescribed, u z ≤ h z)
    (hSelected : ∀ z, z ∉ prescribed → ∃ S : Finset ι,
      cap z - ((∑ i, u (incoming z i)) - (Fintype.card ι : ℤ) * u z) < (S.card : ℤ) ∧
      ∀ i ∈ S, rank (incoming z i) < rank z) :
    ∀ z, u z ≤ h z := by
  intro z₀
  by_contra hFailure
  obtain ⟨B, hB⟩ := hGapBounded
  obtain ⟨R, hR⟩ := hRankBounded
  let gap : V → ℤ := fun z => h z - u z
  obtain ⟨z, _, hMin⟩ := exists_min_image_of_int_bounded_below
    Set.univ gap ⟨z₀, Set.mem_univ z₀⟩ ⟨B, fun w _ => hB w⟩
  have hMinimum : ∀ w, gap z ≤ gap w := fun w => hMin w (Set.mem_univ w)
  have hNegative : gap z < 0 := by
    have hAtFailure := hMinimum z₀
    dsimp [gap] at hAtFailure ⊢
    omega
  let contacts : Set V := {w | gap w = gap z}
  obtain ⟨w, hw, hClockMin⟩ := exists_min_image_of_int_bounded_below
    contacts rank ⟨z, rfl⟩ ⟨R, fun t _ => hR t⟩
  have hContact : gap w = gap z := hw
  have hNotPrescribed : w ∉ prescribed := by
    intro hPin
    have hPinBound := hPrescribed w hPin
    dsimp [gap] at hContact hNegative
    omega
  obtain ⟨S, hCount, hClock⟩ := hSelected w hNotPrescribed
  have hIncomingLower : ∀ i, gap z ≤ gap (incoming w i) :=
    fun i => hMinimum (incoming w i)
  have hSelectedLower : ∀ i ∈ S, gap z + 1 ≤ gap (incoming w i) := by
    intro i hi
    have hLower := hIncomingLower i
    have hStrict := hClock i hi
    by_contra hNotLarger
    have hSame : incoming w i ∈ contacts := by
      change gap (incoming w i) = gap z
      omega
    have hContradiction := hClockMin (incoming w i) hSame
    omega
  have hLowerSum := card_mul_add_card_le_sum
    (fun i => gap (incoming w i)) (gap z) S hIncomingLower hSelectedLower
  have hUpperSum := sum_incoming_gap_le (incoming w) h u w
    (Fintype.card ι : ℤ) (cap w)
    (cap w - ((∑ i, u (incoming w i)) - (Fintype.card ι : ℤ) * u w))
    (hCapped w) rfl
  change (∑ i, gap (incoming w i)) ≤ (Fintype.card ι : ℤ) * gap w + _ at hUpperSum
  rw [hContact] at hUpperSum
  omega

end FLattice.Auxiliary
