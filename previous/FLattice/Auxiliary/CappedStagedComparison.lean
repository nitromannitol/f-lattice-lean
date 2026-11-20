import FLattice.Auxiliary.StagedComparison

/-!
# Staged comparison for capped integer functions

This internal comparison theorem derives the gap inequality from the
literal incoming sums of the compared functions. Its hypotheses expose
the prescribed values, residual deficit, selected incoming indices, and
the two finite sublevel sets. It assumes no comparison conclusion.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- A capped incoming inequality and ordered predecessor regions give
one unit above a reference function off the prescribed set and two on
the first region when its whole incoming collar avoids that set.
The integer residual is converted to a natural number only after its
nonnegativity has been established at the vertices where it is used. -/
theorem one_and_two_le_of_capped_staged_incoming
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (h u cap : V → ℤ) (stage : V → ℕ) (rank : V → α)
    (prescribed : Set V)
    (hCap : ∀ x, (∑ i : Fin (degree x), h (incoming x i)) -
      (degree x : ℤ) * h x ≤ cap x)
    (hPrescribed : ∀ x ∈ prescribed, u x ≤ h x)
    (hDeficitNonneg : ∀ x, x ∉ prescribed →
      0 ≤ cap x - ((∑ i : Fin (degree x), u (incoming x i)) -
        (degree x : ℤ) * u x))
    (hSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)),
        cap x - ((∑ i : Fin (degree x), u (incoming x i)) -
          (degree x : ℤ) * u x) < (S.card : ℤ) ∧
        ∀ i ∈ S, incoming x i ∉ prescribed ∧
          (stage (incoming x i) < stage x ∨
            stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x))
    (hFiniteNonpositive : {x | x ∉ prescribed ∧ h x - u x ≤ 0}.Finite)
    (hNoPrescribedIncoming : ∀ x, x ∉ prescribed → stage x = 0 →
      ∀ i : Fin (degree x), incoming x i ∉ prescribed)
    (hFiniteFirst : {x | x ∉ prescribed ∧ stage x = 0 ∧ h x - u x ≤ 1}.Finite) :
    (∀ x, x ∉ prescribed → u x + 1 ≤ h x) ∧
      (∀ x, x ∉ prescribed → stage x = 0 → u x + 2 ≤ h x) := by
  let gap : V → ℤ := fun x => h x - u x
  let deficit : V → ℕ := fun x =>
    (cap x - ((∑ i : Fin (degree x), u (incoming x i)) -
      (degree x : ℤ) * u x)).toNat
  have hDeficit : ∀ x, x ∉ prescribed → (deficit x : ℤ) =
      cap x - ((∑ i : Fin (degree x), u (incoming x i)) -
        (degree x : ℤ) * u x) := by
    intro x hx
    exact Int.toNat_of_nonneg (hDeficitNonneg x hx)
  have hGapPrescribed : ∀ x ∈ prescribed, 0 ≤ gap x := by
    intro x hx
    exact sub_nonneg.mpr (hPrescribed x hx)
  have hGapSum : ∀ x, x ∉ prescribed →
      (∑ i : Fin (degree x), gap (incoming x i)) ≤
        (degree x : ℤ) * gap x + (deficit x : ℤ) := by
    intro x hx
    exact sum_incoming_gap_le (incoming x) h u x (degree x) (cap x)
      (deficit x) (hCap x) (hDeficit x hx)
  have hGapSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
        ∀ i ∈ S, incoming x i ∉ prescribed ∧
          (stage (incoming x i) < stage x ∨
            stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x) := by
    intro x hx
    obtain ⟨S, hCard, hMove⟩ := hSelected x hx
    refine ⟨S, ?_, hMove⟩
    have hCast := hDeficit x hx
    omega
  obtain ⟨hOne, hTwo⟩ := staged_gap_one_and_two degree incoming gap deficit stage rank
    prescribed hGapPrescribed hGapSum hGapSelected hFiniteNonpositive
    hNoPrescribedIncoming hFiniteFirst
  constructor
  · intro x hx
    have hBound := hOne x hx
    change 1 ≤ h x - u x at hBound
    omega
  · intro x hx hxStage
    have hBound := hTwo x hx hxStage
    change 2 ≤ h x - u x at hBound
    omega

end FLattice.Auxiliary
