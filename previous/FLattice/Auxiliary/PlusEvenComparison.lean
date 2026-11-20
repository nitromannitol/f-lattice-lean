import FLattice.Auxiliary.PlusEvenStages
import FLattice.Auxiliary.PlusEvenPhysicalRegions
import FLattice.Auxiliary.PlusEvenIncomingSums
import FLattice.Auxiliary.PlusEvenSpecialValues

/-!
# Concrete even-plus comparison from finite gap sublevels

The four-region selections are lifted to the full physical lattice, with
literal ranks there. The unknown integer function is not assumed periodic.
The only remaining growth input is finiteness of its gap sublevels.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.PlusEvenProfile

open DirectionalRank

/-- The source region of a physical point, with the prescribed class last. -/
noncomputable def physicalStage (m : Parameter) (z : ℤ × ℤ) : ℕ :=
  cellStage (cellOf m z.1 z.2)

/-- Left ranks on the first and third regions, right ranks on the other regions. -/
noncomputable def physicalRank (m : Parameter) (z : ℤ × ℤ) : ℤ := by
  classical
  exact if physicalStage m z = 0 ∨ physicalStage m z = 2 then
    leftRank z.1 z.2 else rightRank z.1 z.2

/-- The selected physical edges satisfy the staged comparison hypotheses. -/
theorem physical_selected (m : Parameter) (z : ℤ × ℤ)
    (hz : ¬cellPrescribed (cellOf m z.1 z.2)) :
    ∃ S : Finset (Fin 2), incomingDeficit m z.1 z.2 < (S.card : ℤ) ∧
      ∀ i ∈ S,
        ¬cellPrescribed (cellOf m (incomingPoint z.1 z.2 i).1 (incomingPoint z.1 z.2 i).2) ∧
        (physicalStage m (incomingPoint z.1 z.2 i) < physicalStage m z ∨
          physicalStage m (incomingPoint z.1 z.2 i) = physicalStage m z ∧
          physicalRank m (incomingPoint z.1 z.2 i) < physicalRank m z) := by
  classical
  obtain ⟨S, hCard, hMove⟩ := cell_selected (cellOf m z.1 z.2) hz
  refine ⟨S, ?_, ?_⟩
  · rw [incomingDeficit_eq_cell]
    exact hCard
  · intro i hi
    obtain ⟨hP, hStage⟩ := hMove i hi
    refine ⟨?_, ?_⟩
    · rw [cellOf_incomingPoint]
      exact hP
    · rcases hStage with hEarlier | ⟨hSame, hDirection⟩
      · left
        simpa only [physicalStage, cellOf_incomingPoint] using hEarlier
      · right
        have hSame' : physicalStage m (incomingPoint z.1 z.2 i) = physicalStage m z := by
          simpa only [physicalStage, cellOf_incomingPoint] using hSame
        change (cellOf m z.1 z.2).e ≠ (cellOf m z.1 z.2).v ∨
          i = (if physicalStage m z = 0 ∨ physicalStage m z = 2 then 0 else 1) at hDirection
        refine ⟨hSame', ?_⟩
        unfold physicalRank
        rw [hSame']
        by_cases hLeft : physicalStage m z = 0 ∨ physicalStage m z = 2
        · simp only [if_pos hLeft]
          have hDir : (cellOf m z.1 z.2).e ≠ (cellOf m z.1 z.2).v ∨ i = 0 := by
            simpa only [if_pos hLeft] using hDirection
          have h := leftRank_incoming m z.1 z.2 i hDir
          omega
        · simp only [if_neg hLeft]
          have hDir : (cellOf m z.1 z.2).e ≠ (cellOf m z.1 z.2).v ∨ i = 1 := by
            simpa only [if_neg hLeft] using hDirection
          have h := rightRank_incoming m z.1 z.2 i hDir
          omega

/-- The concrete four-region comparison, with its growth input stated as finite sublevels. -/
theorem profile_comparison_of_finite_sublevels (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -1 - 2 * m.val * a - 2 * b))
    (hFinite : ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m z.1 z.2 ≤ b}.Finite) :
    (∀ z : ℤ × ℤ, ¬cellPrescribed (cellOf m z.1 z.2) →
      profile m z.1 z.2 + 1 ≤ h z) ∧
    (∀ z : ℤ × ℤ, regionI (cellOf m z.1 z.2) → profile m z.1 z.2 + 2 ≤ h z) := by
  classical
  let prescribed : Set (ℤ × ℤ) := {z | cellPrescribed (cellOf m z.1 z.2)}
  have hCap : ∀ z : ℤ × ℤ,
      (∑ i : Fin 2, h (incomingPoint z.1 z.2 i)) - 2 * h z ≤ 0 := by
    intro z
    rw [incomingPoint_sum]
    have hSH := hSuperharmonic z.1 z.2
    simpa only [Prod.mk.eta, sub_nonpos] using hSH
  have hPins : ∀ z ∈ prescribed, profile m z.1 z.2 ≤ h z := by
    rintro ⟨x, y⟩ hz
    obtain ⟨a, b, hx, hy⟩ := (cellPrescribed_cellOf_iff m x y).mp hz
    dsimp at hx hy ⊢
    rw [hx, hy, profile_prescribed_coset]
    exact hPrescribed a b
  have hNonneg : ∀ z : ℤ × ℤ, z ∉ prescribed →
      0 ≤ 0 - ((∑ i : Fin 2,
        profile m (incomingPoint z.1 z.2 i).1 (incomingPoint z.1 z.2 i).2) -
        2 * profile m z.1 z.2) := by
    intro z _
    rw [← incomingDeficit_eq_residual]
    exact incomingDeficit_nonneg m z.1 z.2
  have hSelection : ∀ z : ℤ × ℤ, z ∉ prescribed →
      ∃ S : Finset (Fin 2),
        0 - ((∑ i : Fin 2,
          profile m (incomingPoint z.1 z.2 i).1 (incomingPoint z.1 z.2 i).2) -
          2 * profile m z.1 z.2) < (S.card : ℤ) ∧
        ∀ i ∈ S, incomingPoint z.1 z.2 i ∉ prescribed ∧
          (physicalStage m (incomingPoint z.1 z.2 i) < physicalStage m z ∨
            physicalStage m (incomingPoint z.1 z.2 i) = physicalStage m z ∧
              physicalRank m (incomingPoint z.1 z.2 i) < physicalRank m z) := by
    intro z hz
    rw [← incomingDeficit_eq_residual]
    exact physical_selected m z hz
  have hFiniteZero : {z : ℤ × ℤ | z ∉ prescribed ∧
      h z - profile m z.1 z.2 ≤ 0}.Finite :=
    (hFinite 0).subset (fun _ hz => hz.2)
  have hCollar : ∀ z : ℤ × ℤ, z ∉ prescribed → physicalStage m z = 0 →
      ∀ i : Fin 2, incomingPoint z.1 z.2 i ∉ prescribed := by
    intro z _ hStage i
    exact regionI_physical_incoming_not_prescribed m z.1 z.2
      ((cellStage_eq_zero_iff (cellOf m z.1 z.2)).mp hStage) i
  have hFiniteOne : {z : ℤ × ℤ | z ∉ prescribed ∧ physicalStage m z = 0 ∧
      h z - profile m z.1 z.2 ≤ 1}.Finite :=
    (hFinite 1).subset (fun _ hz => hz.2.2)
  obtain ⟨hOne, hTwo⟩ := one_and_two_le_of_capped_staged_incoming
    (fun _ : ℤ × ℤ => 2) (fun z i => incomingPoint z.1 z.2 i) h
    (fun z => profile m z.1 z.2) (fun _ => 0) (physicalStage m) (physicalRank m)
    prescribed hCap hPins hNonneg hSelection hFiniteZero hCollar hFiniteOne
  refine ⟨hOne, ?_⟩
  intro z hz
  have hNotPrescribed : z ∉ prescribed := by
    intro hP
    exact (cell_region_disjoint (cellOf m z.1 z.2)).1 hP |>.1 hz
  exact hTwo z hNotPrescribed ((cellStage_eq_zero_iff (cellOf m z.1 z.2)).mpr hz)

/-- The source pin bounds force the origin above zero for every proper integer gap. -/
theorem one_le_origin_of_finite_sublevels (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (-2 * m.val - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -1 - 2 * m.val * a - 2 * b))
    (hFinite : ∀ b : ℤ, {z : ℤ × ℤ | h z - profile m z.1 z.2 ≤ b}.Finite) :
    1 ≤ h (0, 0) := by
  have hComparison :=
    (profile_comparison_of_finite_sublevels m h hSuperharmonic hPrescribed hFinite).2
      (0, 0) (regionI_cellOf_origin m)
  simpa only [profile_origin, Int.reduceNeg, Int.reduceAdd] using hComparison

end FLattice.Auxiliary.PlusEvenProfile
