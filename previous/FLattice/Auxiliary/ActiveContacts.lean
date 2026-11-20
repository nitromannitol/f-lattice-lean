import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Set.Finite.Lattice
import Lean.Elab.Tactic.Omega

/-!
# Active contacts of a finite unit lowering

Generic conditional infrastructure for integer extrema. No lattice,
quadratic-growth, transport, or recurrence theorem is assumed or defined.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

variable {X Y I : Type*}

/-- A backward objective below the parent height comes from a lowered
forward contact and an index maximizing the forward objective. -/
theorem active_contact_of_attained_objective
    (φ : I → X ≃ Y) (cost : I → ℤ)
    (f : Y → ℤ) (obstacle height : X → ℤ) (backward : Y → ℤ)
    (lowered : Set X) [DecidablePred (· ∈ lowered)]
    (hMajorant : ∀ x, obstacle x ≤ height x)
    (hObjective : ∀ x i, f (φ i x) - cost i ≤ obstacle x)
    (hAttained : ∀ y, ∃ i,
      backward y =
        (if (φ i).symm y ∈ lowered then height ((φ i).symm y) - 1
         else height ((φ i).symm y)) + cost i)
    (y : Y) (hActive : backward y < f y) :
    ∃ x ∈ lowered, ∃ i,
      φ i x = y ∧ height x = obstacle x ∧
        f (φ i x) - cost i = obstacle x := by
  obtain ⟨i, hi⟩ := hAttained y
  let x := (φ i).symm y
  have hImage : φ i x = y := (φ i).apply_symm_apply y
  have hMajor := hMajorant x
  have hTerm := hObjective x i
  rw [hImage] at hTerm
  change backward y = (if x ∈ lowered then height x - 1 else height x) + cost i at hi
  have hMember : x ∈ lowered := by
    by_contra hOutside
    rw [if_neg hOutside] at hi
    omega
  rw [if_pos hMember] at hi
  refine ⟨x, hMember, i, hImage, ?_, ?_⟩
  · omega
  · rw [hImage]
    omega

/-- Finite forward maximizing sets make the negative backward comparison
set finite, without any periodicity or backward response formula. -/
theorem finite_active_contacts
    (φ : I → X ≃ Y) (cost : I → ℤ)
    (f : Y → ℤ) (obstacle height : X → ℤ) (backward : Y → ℤ)
    (lowered : Set X) [DecidablePred (· ∈ lowered)]
    (hFinite : lowered.Finite)
    (hMaximizers : ∀ x,
      {i | f (φ i x) - cost i = obstacle x}.Finite)
    (hMajorant : ∀ x, obstacle x ≤ height x)
    (hObjective : ∀ x i, f (φ i x) - cost i ≤ obstacle x)
    (hAttained : ∀ y, ∃ i,
      backward y =
        (if (φ i).symm y ∈ lowered then height ((φ i).symm y) - 1
         else height ((φ i).symm y)) + cost i) :
    {y | backward y < f y}.Finite := by
  have hUnion :
      (⋃ x ∈ lowered, (fun i => φ i x) ''
        {i | f (φ i x) - cost i = obstacle x}).Finite :=
    hFinite.biUnion fun x _ => (hMaximizers x).image (fun i => φ i x)
  apply hUnion.subset
  intro y hy
  obtain ⟨x, hx, i, hImage, _, hMax⟩ :=
    active_contact_of_attained_objective φ cost f obstacle height backward
      lowered hMajorant hObjective hAttained y hy
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
    ⟨hx, ⟨i, hMax, hImage⟩⟩⟩

/-- Superharmonicity of the second function is needed only where it is
strictly below the first function. -/
theorem minimum_superharmonic_on_active
    (left right : Y → Y) (f backward : Y → ℤ)
    (hParent : ∀ y, f (left y) + f (right y) ≤ 2 * f y)
    (hActive : ∀ y, backward y < f y →
      backward (left y) + backward (right y) ≤ 2 * backward y) :
    ∀ y, min (f (left y)) (backward (left y)) +
      min (f (right y)) (backward (right y)) ≤
        2 * min (f y) (backward y) := by
  intro y
  by_cases hOrder : f y ≤ backward y
  · rw [min_eq_left hOrder]
    have hLeft := min_le_left (f (left y)) (backward (left y))
    have hRight := min_le_left (f (right y)) (backward (right y))
    have hStar := hParent y
    omega
  · have hStrict : backward y < f y := by omega
    rw [min_eq_right (le_of_lt hStrict)]
    have hLeft := min_le_right (f (left y)) (backward (left y))
    have hRight := min_le_right (f (right y)) (backward (right y))
    have hStar := hActive y hStrict
    omega

/-- A backward comparison bounded below by one unit clips to exactly a
unit lowering on its strict negative comparison set. -/
theorem minimum_eq_unit_lowering
    (f backward : Y → ℤ) (hLower : ∀ y, f y - 1 ≤ backward y) :
    ∀ y, min (f y) (backward y) =
      if backward y < f y then f y - 1 else f y := by
  intro y
  have hBound := hLower y
  by_cases hActive : backward y < f y
  · rw [if_pos hActive, min_eq_right (le_of_lt hActive)]
    omega
  · have hOrder : f y ≤ backward y := by omega
    rw [if_neg hActive, min_eq_left hOrder]

end FLattice.Auxiliary
