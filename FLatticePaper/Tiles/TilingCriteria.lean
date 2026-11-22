import FLatticePaper.Tiles.TilingBalance
import FLatticePaper.Tiles.TilingSteps
import FLatticePaper.Tiles.TilingLattice

/-! Task 32: `prop:tiling_criteria` (Beauquier-Nivat), proved in Lean.

Reading of the statement. A tile `T` (a simple tile, `IsSimpleTile`) generates a `(v₁, v₂)`-regular tiling when the translates
`T + v`, `v ∈ latticeOf v₁ v₂`, cover every cell exactly once: `IsRegularTiling T v₁ v₂` says that every cell `x` lies in
exactly one translate, i.e. there is exactly one `v` in the lattice with `x - v ∈ T`. The hypothesis is that the boundary word
of `T` is `w₁ * w₂ * ŵ₁ * ŵ₂`, with `ŵ` the group inverse (`F2Word.hat`: reverse and negate), and the lattice is
`(Σw₁, Σw₂)`.

Proof (the cancellation and area argument, in place of winding numbers). Let `N` be the lattice and `Q` a coset of `N`.
(1) The boundary edges of `T` split, by the word, into two translated walks and two reversed translated walks; the edge
balance `edgeCount N T Q D = edgeCount N T (Q + [D]) (-D)` follows (`edgeCount_balance`).
(2) The balance makes the number of cells of `T` in each coset constant (`cellCount_step_h`, `cellCount_step_v`,
`cellCount_add_qmk`).
(3) The shoelace identity gives `#T = det(Σw₁, Σw₂)` (`card_eq_detG`, via Green's identity `green_boundary`), so the
index of `N` is `#T` (`index_latticeSub`), and the number of cells per coset summed over the cosets is `#T`; hence the constant
is `1`. -/

namespace FLatticePaper.Tiles
open Classical

/-- A `(v₁, v₂)`-regular tiling by `T`: every cell lies in exactly one translate `T + v`, `v ∈ latticeOf v₁ v₂`. -/
def IsRegularTiling (T : CellTile) (v₁ v₂ : GInt) : Prop :=
  ∀ x : GInt, ∃! v, v ∈ latticeOf v₁ v₂ ∧ x - v ∈ T

/-- `prop:tiling_criteria`: a simple tile whose boundary word is `w₁ * w₂ * ŵ₁ * ŵ₂` generates a
`(Σw₁, Σw₂)`-regular tiling. -/
theorem tiling_criteria (T : CellTile) (w₁ w₂ : F2Word) (_hT : IsSimpleTile T)
    (hw : IsBoundaryWord T (w₁ ++ w₂ ++ F2Word.hat w₁ ++ F2Word.hat w₂)) :
    IsRegularTiling T (F2Word.sum w₁) (F2Word.sum w₂) := by
  obtain ⟨c, hc⟩ := hw
  have hg₁N : F2Word.sum w₁ ∈ latticeSub (F2Word.sum w₁) (F2Word.sum w₂) :=
    AddSubgroup.subset_closure (by simp)
  have hg₂N : F2Word.sum w₂ ∈ latticeSub (F2Word.sum w₁) (F2Word.sum w₂) :=
    AddSubgroup.subset_closure (by simp)
  set N := latticeSub (F2Word.sum w₁) (F2Word.sum w₂) with hN
  have hcard : (T.card : ℤ) = detG (F2Word.sum w₁) (F2Word.sum w₂) := card_eq_detG T c w₁ w₂ hc
  have hpos : 0 < T.card := by
    obtain ⟨t, ht, _⟩ := Finset.mem_biUnion.1 hc.1.1
    exact Finset.card_pos.mpr ⟨t, ht⟩
  have hposZ : (0 : ℤ) < T.card := by exact_mod_cast hpos
  have hdet : detG (F2Word.sum w₁) (F2Word.sum w₂) ≠ 0 := by
    rw [← hcard]
    exact ne_of_gt hposZ
  have habs : (detG (F2Word.sum w₁) (F2Word.sum w₂)).natAbs = T.card := by
    rw [← hcard]
    simp
  have hidx : N.index = T.card := by
    rw [hN, index_latticeSub _ _ hdet, habs]
  have hcardQ : Nat.card (GInt ⧸ N) = T.card := hidx
  haveI : Finite (GInt ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hcardQ]; omega)
  haveI : Fintype (GInt ⧸ N) := Fintype.ofFinite _
  have hbal : ∀ (Q : GInt ⧸ N) (D : GInt), edgeCount N T Q D = edgeCount N T (Q + qmk N D) (-D) :=
    fun Q D => edgeCount_balance N T c w₁ w₂ hc hg₁N hg₂N Q D
  have hconst : ∀ Q : GInt ⧸ N, cellCount N T Q = cellCount N T 0 := by
    intro Q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective N Q
    have h := cellCount_add_qmk N T hbal 0 x
    rw [zero_add] at h
    exact h
  have hsum := sum_cellCount N T
  rw [Finset.sum_congr rfl (fun Q _ => hconst Q), Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hfc : Fintype.card (GInt ⧸ N) = T.card := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardQ
  rw [hfc] at hsum
  have hone : cellCount N T 0 = 1 := by
    have h2 : T.card * cellCount N T 0 = T.card * 1 := by rw [hsum, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hcell1 : ∀ Q : GInt ⧸ N, cellCount N T Q = 1 := fun Q => (hconst Q).trans hone
  intro x
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (hcell1 (qmk N x))
  have ht_mem : t ∈ T.filter (fun s => qmk N s = qmk N x) := by
    rw [ht]
    exact Finset.mem_singleton_self t
  rw [Finset.mem_filter] at ht_mem
  have huniq : ∀ s ∈ T, qmk N s = qmk N x → s = t := by
    intro s hs hsq
    have hm : s ∈ T.filter (fun s => qmk N s = qmk N x) := Finset.mem_filter.2 ⟨hs, hsq⟩
    rw [ht, Finset.mem_singleton] at hm
    exact hm
  refine ⟨x - t, ⟨?_, ?_⟩, ?_⟩
  · have hmem : x - t ∈ N := by
      have h0 : qmk N (x - t) = 0 := by
        rw [map_sub, ht_mem.2, sub_self]
      exact (QuotientAddGroup.eq_zero_iff (x - t)).mp h0
    exact (mem_latticeSub_iff _ _ _).mp hmem
  · rw [sub_sub_cancel]
    exact ht_mem.1
  · rintro v ⟨hv, hxv⟩
    have hvN : v ∈ N := (mem_latticeSub_iff _ _ _).mpr hv
    have hq : qmk N (x - v) = qmk N x := by
      rw [map_sub, qmk_eq_zero_of_mem hvN, sub_zero]
    have hxt := huniq (x - v) hxv hq
    rw [← hxt, sub_sub_cancel]

end FLatticePaper.Tiles
