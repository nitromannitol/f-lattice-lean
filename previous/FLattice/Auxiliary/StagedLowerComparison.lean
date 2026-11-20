import FLattice.Auxiliary.IncomingGap
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Lower comparison through ordered regions with prescribed exits

Selected incoming slots may reach a prescribed vertex or decrease a
region/rank order. Only the negative gap set must be finite. The graph
may have vertex-dependent degrees and repeated incoming vertices; slots
are counted with their multiplicities. Ranks need not be bounded below.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary

variable {V α : Type*} [LinearOrder α]

/-- Ordered incoming selections exclude negative gaps. Selected edges can
exit directly to the prescribed set; this proves the ordinary lower bound. -/
theorem zero_le_gap_of_staged_incoming
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (gap : V → ℤ) (deficit stage : V → ℕ) (rank : V → α)
    (prescribed : Set V)
    (hPrescribed : ∀ x ∈ prescribed, 0 ≤ gap x)
    (hSum : ∀ x, x ∉ prescribed →
      (∑ i : Fin (degree x), gap (incoming x i)) ≤
        (degree x : ℤ) * gap x + (deficit x : ℤ))
    (hSelected : ∀ x, x ∉ prescribed →
      ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
        ∀ i ∈ S, incoming x i ∈ prescribed ∨
          stage (incoming x i) < stage x ∨
          stage (incoming x i) = stage x ∧ rank (incoming x i) < rank x)
    (hFinite : {x | gap x < 0}.Finite) :
    ∀ x, 0 ≤ gap x := by
  classical
  intro x
  by_contra hFailure
  have hxBad : x ∈ {y | gap y < 0} := lt_of_not_ge hFailure
  obtain ⟨z₀, hz₀, hMinGap⟩ :=
    Set.exists_min_image {y | gap y < 0} gap hFinite ⟨x, hxBad⟩
  have hMinimumNegative : gap z₀ < 0 := hz₀
  have hGlobalLower : ∀ y, gap z₀ ≤ gap y := by
    intro y
    by_cases hy : gap y < 0
    · exact hMinGap y hy
    · omega
  let level : Set V := {y | gap y = gap z₀}
  have hLevelFinite : level.Finite := hFinite.subset (by
    intro y hy
    exact lt_of_eq_of_lt hy hMinimumNegative)
  have hLevelNonempty : level.Nonempty := ⟨z₀, rfl⟩
  obtain ⟨z₁, hz₁, hMinStage⟩ :=
    Set.exists_min_image level stage hLevelFinite hLevelNonempty
  let first : Set V := {y | y ∈ level ∧ stage y = stage z₁}
  have hFirstFinite : first.Finite := hLevelFinite.subset (fun _ hy => hy.1)
  obtain ⟨z, hz, hMinRank⟩ := Set.exists_min_image first rank hFirstFinite
    ⟨z₁, hz₁, rfl⟩
  have hzNegative : gap z < 0 := lt_of_eq_of_lt hz.1 hMinimumNegative
  have hzNotPrescribed : z ∉ prescribed := by
    intro hzPrescribed
    exact not_lt_of_ge (hPrescribed z hzPrescribed) hzNegative
  obtain ⟨S, hCard, hMove⟩ := hSelected z hzNotPrescribed
  have hIncomingLower : ∀ i : Fin (degree z), gap z ≤ gap (incoming z i) := by
    intro i
    rw [hz.1]
    exact hGlobalLower (incoming z i)
  have hIncomingStrict : ∀ i ∈ S, gap z + 1 ≤ gap (incoming z i) := by
    intro i hi
    have hLower := hIncomingLower i
    rcases hMove i hi with hiPrescribed | hiEarlier | ⟨hiSame, hiRank⟩
    · have hBound := hPrescribed (incoming z i) hiPrescribed
      omega
    · have hUnequal : gap (incoming z i) ≠ gap z := by
        intro hEqual
        have hiLevel : incoming z i ∈ level := hEqual.trans hz.1
        have hStageLower := hMinStage (incoming z i) hiLevel
        have hStageEqual := hz.2
        omega
      omega
    · have hUnequal : gap (incoming z i) ≠ gap z := by
        intro hEqual
        have hiLevel : incoming z i ∈ level := hEqual.trans hz.1
        have hiFirst : incoming z i ∈ first := ⟨hiLevel, hiSame.trans hz.2⟩
        exact (not_lt_of_ge (hMinRank (incoming z i) hiFirst)) hiRank
      omega
  have hCount : (degree z : ℤ) * gap z + (S.card : ℤ) ≤
      ∑ i : Fin (degree z), gap (incoming z i) := by
    simpa only [Fintype.card_fin] using
      card_mul_add_card_le_sum (fun i : Fin (degree z) => gap (incoming z i))
        (gap z) S hIncomingLower hIncomingStrict
  have hStar := hSum z hzNotPrescribed
  omega

end FLattice.Auxiliary
