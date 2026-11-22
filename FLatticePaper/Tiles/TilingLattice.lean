import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.TilingWalk
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.LinearCombination

/-! Task 32, part 3: the lattice `latticeOf v₁ v₂` as an additive subgroup of the Gaussian integers, and its index. When
`det(v₁, v₂) ≠ 0` the index of `Z v₁ + Z v₂` in `Z²` is `|det(v₁, v₂)|`, from Mathlib's determinant formula for the index
of a full-rank submodule. This is the count of the cosets of the lattice, used to read off the covering multiplicity. -/

namespace FLatticePaper.Tiles
open Module

/-- The lattice `Z v₁ + Z v₂` as an additive subgroup of `GInt`. -/
def latticeSub (v₁ v₂ : GInt) : AddSubgroup GInt := AddSubgroup.closure {v₁, v₂}

theorem mem_latticeSub_iff (v₁ v₂ x : GInt) : x ∈ latticeSub v₁ v₂ ↔ x ∈ latticeOf v₁ v₂ := by
  unfold latticeSub latticeOf
  rw [AddSubgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    rw [← h]
    ext <;> simp
  · rintro ⟨k, k', h⟩
    refine ⟨k, k', ?_⟩
    rw [h]
    ext <;> simp

/-- The determinant `det(v₁, v₂) = v₁.re v₂.im - v₁.im v₂.re` of two Gaussian integers. -/
theorem linearIndependent_of_detG (v₁ v₂ : GInt) (h : detG v₁ v₂ ≠ 0) :
    LinearIndependent ℤ ![v₁, v₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 : g 0 * v₁.1 + g 1 * v₂.1 = 0 := by
    have := congrArg Prod.fst (by simpa [Fin.sum_univ_two] using hg : g 0 • v₁ + g 1 • v₂ = 0)
    simpa using this
  have e2 : g 0 * v₁.2 + g 1 * v₂.2 = 0 := by
    have := congrArg Prod.snd (by simpa [Fin.sum_univ_two] using hg : g 0 • v₁ + g 1 • v₂ = 0)
    simpa using this
  have h0 : g 0 * detG v₁ v₂ = 0 := by
    unfold detG
    linear_combination v₂.2 * e1 - v₂.1 * e2
  have h1 : g 1 * detG v₁ v₂ = 0 := by
    unfold detG
    linear_combination v₁.1 * e2 - v₁.2 * e1
  fin_cases i
  · simpa [h] using h0
  · simpa [h] using h1

/-- The index of the lattice `Z v₁ + Z v₂` in the Gaussian integers is the absolute value of the determinant. -/
theorem index_latticeSub (v₁ v₂ : GInt) (h : detG v₁ v₂ ≠ 0) :
    (latticeSub v₁ v₂).index = (detG v₁ v₂).natAbs := by
  have hmem : ∀ i : Fin 2, ![v₁, v₂] i ∈ latticeSub v₁ v₂ := by
    intro i
    fin_cases i
    · exact AddSubgroup.subset_closure (by simp)
    · exact AddSubgroup.subset_closure (by simp)
  have hli : LinearIndependent ℤ (fun i : Fin 2 => (⟨![v₁, v₂] i, hmem i⟩ : latticeSub v₁ v₂)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : ∑ j : Fin 2, g j • (![v₁, v₂] j : GInt) = 0 := by
      have h3 := map_sum (latticeSub v₁ v₂).subtype
        (fun j : Fin 2 => g j • (⟨![v₁, v₂] j, hmem j⟩ : latticeSub v₁ v₂)) Finset.univ
      rw [← h3] at *
      have h4 : (latticeSub v₁ v₂).subtype (∑ j : Fin 2, g j • (⟨![v₁, v₂] j, hmem j⟩ : latticeSub v₁ v₂)) = 0 := by
        rw [hg]; simp
      rw [map_sum] at h4
      simpa using h4
    exact (Fintype.linearIndependent_iff.mp (linearIndependent_of_detG v₁ v₂ h)) g key i
  have hsp : (⊤ : Submodule ℤ (latticeSub v₁ v₂)) ≤
      Submodule.span ℤ (Set.range (fun i : Fin 2 => (⟨![v₁, v₂] i, hmem i⟩ : latticeSub v₁ v₂))) := by
    intro x _
    obtain ⟨m, n, hx⟩ := (AddSubgroup.mem_closure_pair).mp x.2
    have hx' : x = m • (⟨v₁, hmem 0⟩ : latticeSub v₁ v₂) + n • (⟨v₂, hmem 1⟩ : latticeSub v₁ v₂) := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_zsmul]
      rw [hx]
    rw [hx']
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩))
  let bN : Basis (Fin 2) ℤ (latticeSub v₁ v₂) :=
    Basis.mk hli hsp
  have hidx := AddSubgroup.index_eq_natAbs_det (Basis.finTwoProd ℤ) (latticeSub v₁ v₂) bN
  rw [hidx]
  congr 1
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply, bN, Basis.coe_mk, Basis.coe_finTwoProd_repr, detG]
  ring

end FLatticePaper.Tiles
