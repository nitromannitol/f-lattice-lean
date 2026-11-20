import FLattice.Auxiliary.IncomingGap
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Staged integer comparison for finite incoming lists

Conditional infrastructure for an arbitrary vertex type. Incoming indices,
not distinct predecessor vertices, are counted, so repeated entries retain
their multiplicity. Finiteness is required only for the specified bad sets;
neither the rank nor the number of stages needs a global bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- Selected incoming indices exclude every nonpositive nonprescribed gap.
Only the bad set is finite; the vertex type and all stage regions may be
infinite. The selected predecessors explicitly avoid the prescribed set. -/
theorem one_le_gap_of_staged_incoming
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (gap : V → ℤ) (deficit stage : V → ℕ) (rank : V → α)
    (prescribed : Set V)
    (hPrescribed : ∀ x ∈ prescribed, 0 ≤ gap x)
    (hSum : ∀ x, x ∉ prescribed →
      (∑ i : Fin (degree x), gap (incoming x i)) ≤
        (degree x : ℤ) * gap x + (deficit x : ℤ))
    (hSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
        ∀ i ∈ S, incoming x i ∉ prescribed ∧
          (stage (incoming x i) < stage x ∨
            stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x))
    (hFinite : {x | x ∉ prescribed ∧ gap x ≤ 0}.Finite) :
    ∀ x, x ∉ prescribed → 1 ≤ gap x := by
  classical
  intro x hx
  by_contra hFailure
  have hxBad : x ∈ {y | y ∉ prescribed ∧ gap y ≤ 0} := ⟨hx, by omega⟩
  obtain ⟨z₀, hz₀, hMinGap⟩ := Set.exists_min_image
    {y | y ∉ prescribed ∧ gap y ≤ 0} gap hFinite ⟨x, hxBad⟩
  have hMinimumNonpositive : gap z₀ ≤ 0 := hz₀.2
  have hGlobalLower : ∀ y, gap z₀ ≤ gap y := by
    intro y
    by_cases hy : y ∈ prescribed
    · have hBound := hPrescribed y hy
      exact le_trans hz₀.2 hBound
    · by_cases hyGap : gap y ≤ 0
      · exact hMinGap y ⟨hy, hyGap⟩
      · omega
  let level : Set V := {y | y ∉ prescribed ∧ gap y = gap z₀}
  have hLevelFinite : level.Finite := hFinite.subset (by
    intro y hy
    exact ⟨hy.1, le_trans (le_of_eq hy.2) hz₀.2⟩)
  have hLevelNonempty : level.Nonempty := ⟨z₀, hz₀.1, rfl⟩
  obtain ⟨z₁, hz₁, hMinStage⟩ :=
    Set.exists_min_image level stage hLevelFinite hLevelNonempty
  let first : Set V := {y | y ∈ level ∧ stage y = stage z₁}
  have hFirstFinite : first.Finite := hLevelFinite.subset (fun _ hy => hy.1)
  obtain ⟨z, hz, hMinRank⟩ := Set.exists_min_image first rank hFirstFinite
    ⟨z₁, hz₁, rfl⟩
  obtain ⟨S, hCard, hMove⟩ := hSelected z hz.1.1
  have hIncomingLower : ∀ i : Fin (degree z), gap z ≤ gap (incoming z i) := by
    intro i
    rw [hz.1.2]
    exact hGlobalLower (incoming z i)
  have hIncomingStrict : ∀ i ∈ S, gap z + 1 ≤ gap (incoming z i) := by
    intro i hi
    obtain ⟨hiNotPrescribed, hiMove⟩ := hMove i hi
    have hLower := hIncomingLower i
    have hUnequal : gap (incoming z i) ≠ gap z := by
      intro hEqual
      have hiLevel : incoming z i ∈ level :=
        ⟨hiNotPrescribed, hEqual.trans hz.1.2⟩
      rcases hiMove with hiEarlier | ⟨hiSame, hiRank⟩
      · have hStageLower := hMinStage (incoming z i) hiLevel
        have hStageEqual := hz.2
        omega
      · have hiFirst : incoming z i ∈ first := ⟨hiLevel, hiSame.trans hz.2⟩
        exact (not_lt_of_ge (hMinRank (incoming z i) hiFirst)) hiRank
    omega
  have hCount : (degree z : ℤ) * gap z + (S.card : ℤ) ≤
      ∑ i : Fin (degree z), gap (incoming z i) := by
    simpa only [Fintype.card_fin] using
      card_mul_add_card_le_sum (fun i : Fin (degree z) => gap (incoming z i))
        (gap z) S hIncomingLower hIncomingStrict
  have hStar := hSum z hz.1.1
  omega

/-- Reusing the first stage raises its gap to two. The first-layer lower
bound is assumed explicitly, and every incoming predecessor of this stage,
including those not selected, is required to avoid the prescribed set. -/
theorem two_le_gap_on_first_stage
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (gap : V → ℤ) (deficit stage : V → ℕ) (rank : V → α)
    (prescribed : Set V)
    (hOne : ∀ x, x ∉ prescribed → 1 ≤ gap x)
    (hSum : ∀ x, x ∉ prescribed →
      (∑ i : Fin (degree x), gap (incoming x i)) ≤
        (degree x : ℤ) * gap x + (deficit x : ℤ))
    (hSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
        ∀ i ∈ S, incoming x i ∉ prescribed ∧
          (stage (incoming x i) < stage x ∨
            stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x))
    (hNoPrescribedIncoming : ∀ x, x ∉ prescribed → stage x = 0 →
      ∀ i : Fin (degree x), incoming x i ∉ prescribed)
    (hFinite : {x | x ∉ prescribed ∧ stage x = 0 ∧ gap x ≤ 1}.Finite) :
    ∀ x, x ∉ prescribed → stage x = 0 → 2 ≤ gap x := by
  classical
  intro x hx hxStage
  by_contra hFailure
  have hxBad : x ∈ {y | y ∉ prescribed ∧ stage y = 0 ∧ gap y ≤ 1} :=
    ⟨hx, hxStage, by omega⟩
  obtain ⟨z, hz, hMinRank⟩ := Set.exists_min_image
    {y | y ∉ prescribed ∧ stage y = 0 ∧ gap y ≤ 1} rank hFinite ⟨x, hxBad⟩
  have hCenter : gap z = 1 := by
    have hLower := hOne z hz.1
    have hUpper := hz.2.2
    omega
  have hIncomingLower : ∀ i : Fin (degree z), 1 ≤ gap (incoming z i) := by
    intro i
    exact hOne (incoming z i) (hNoPrescribedIncoming z hz.1 hz.2.1 i)
  obtain ⟨S, hCard, hMove⟩ := hSelected z hz.1
  have hIncomingStrict : ∀ i ∈ S, (1 : ℤ) + 1 ≤ gap (incoming z i) := by
    intro i hi
    obtain ⟨hiNotPrescribed, hiMove⟩ := hMove i hi
    have hiStage : stage (incoming z i) = 0 := by
      rcases hiMove with hiEarlier | ⟨hiSame, _⟩
      · have hzStage := hz.2.1
        omega
      · exact hiSame.trans hz.2.1
    have hiRank : rank (incoming z i) < rank z := by
      rcases hiMove with hiEarlier | ⟨_, hiRank⟩
      · have hzStage := hz.2.1
        omega
      · exact hiRank
    have hNotBad : ¬gap (incoming z i) ≤ 1 := by
      intro hiGap
      exact (not_lt_of_ge (hMinRank (incoming z i)
        ⟨hiNotPrescribed, hiStage, hiGap⟩)) hiRank
    omega
  have hCount : (degree z : ℤ) + (S.card : ℤ) ≤
      ∑ i : Fin (degree z), gap (incoming z i) := by
    simpa only [Fintype.card_fin, mul_one] using
      card_mul_add_card_le_sum (fun i : Fin (degree z) => gap (incoming z i))
        1 S hIncomingLower hIncomingStrict
  have hStar := hSum z hz.1
  rw [hCenter, mul_one] at hStar
  omega

/-- The staged comparison and its repeated first stage in one interface.
Both finite-sublevel assumptions and the full first-stage incoming collar
condition are explicit. No global rank or periodicity bound is present. -/
theorem staged_gap_one_and_two
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (gap : V → ℤ) (deficit stage : V → ℕ) (rank : V → α)
    (prescribed : Set V)
    (hPrescribed : ∀ x ∈ prescribed, 0 ≤ gap x)
    (hSum : ∀ x, x ∉ prescribed →
      (∑ i : Fin (degree x), gap (incoming x i)) ≤
        (degree x : ℤ) * gap x + (deficit x : ℤ))
    (hSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
        ∀ i ∈ S, incoming x i ∉ prescribed ∧
          (stage (incoming x i) < stage x ∨
            stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x))
    (hFiniteNonpositive : {x | x ∉ prescribed ∧ gap x ≤ 0}.Finite)
    (hNoPrescribedIncoming : ∀ x, x ∉ prescribed → stage x = 0 →
      ∀ i : Fin (degree x), incoming x i ∉ prescribed)
    (hFiniteFirst : {x | x ∉ prescribed ∧ stage x = 0 ∧ gap x ≤ 1}.Finite) :
    (∀ x, x ∉ prescribed → 1 ≤ gap x) ∧
      (∀ x, x ∉ prescribed → stage x = 0 → 2 ≤ gap x) := by
  have hOne := one_le_gap_of_staged_incoming degree incoming gap deficit stage rank
    prescribed hPrescribed hSum hSelected hFiniteNonpositive
  exact ⟨hOne, two_le_gap_on_first_stage degree incoming gap deficit stage rank
    prescribed hOne hSum hSelected hNoPrescribedIncoming hFiniteFirst⟩

end FLattice.Auxiliary
