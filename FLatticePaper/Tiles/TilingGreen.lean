import FLatticePaper.Tiles.TilingWalk
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin

/-! Task 32, part 2: Green's identity for cell tiles. For a finite set `T` of cells, the shoelace sum of its directed
boundary edges is twice its number of cells: `Σ_{e ∈ ∂T} ω(e) = 2 |T|`, with `ω(a → b) = (a₁ + b₁)(b₂ - a₂)`.

Proof: each cell `c` has four counterclockwise edges `cellEdge c j` (`j : Fin 4`), each with the cell `cellOther c j`
on its other side, and their `ω` sum to `2`. The pairs `(c, j)` whose other cell lies in `T` cancel in pairs, through the
involution `(c, j) ↦ (cellOther c j, j + 2)`, which reverses the edge. The remaining pairs are the boundary edges, each once. -/

namespace FLatticePaper.Tiles
open Finset

/-- The four counterclockwise edges of the cell `c`: bottom, right, top, left. -/
def cellEdge (c : GInt) : Fin 4 → GInt × GInt
  | 0 => (c, c + gOne)
  | 1 => (c + gOne, c + gOne + gI)
  | 2 => (c + gOne + gI, c + gI)
  | 3 => (c + gI, c)

/-- The cell on the other side of the `j`-th edge of `c`. -/
def cellOther (c : GInt) : Fin 4 → GInt
  | 0 => c - gI
  | 1 => c + gOne
  | 2 => c + gI
  | 3 => c - gOne

theorem mem_boundaryEdges_iff (T : CellTile) (e : GInt × GInt) :
    e ∈ T.boundaryEdges ↔ ∃ c ∈ T, ∃ j : Fin 4, cellEdge c j = e ∧ cellOther c j ∉ T := by
  unfold CellTile.boundaryEdges
  simp only [Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset, List.mem_filter, cellEdgesWithOther,
    List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, x, hx, rfl⟩
    rcases hx with ⟨rfl | rfl | rfl | rfl, hn⟩
    · exact ⟨c, hc, 0, by simp [cellEdge], by simpa [cellOther] using hn⟩
    · exact ⟨c, hc, 1, by simp [cellEdge], by simpa [cellOther] using hn⟩
    · exact ⟨c, hc, 2, by simp [cellEdge], by simpa [cellOther] using hn⟩
    · exact ⟨c, hc, 3, by simp [cellEdge], by simpa [cellOther] using hn⟩
  · rintro ⟨c, hc, j, rfl, hn⟩
    refine ⟨c, hc, ?_⟩
    fin_cases j
    · exact ⟨(c, c + gOne, c - gI), ⟨Or.inl rfl, by simpa [cellOther] using hn⟩, rfl⟩
    · exact ⟨(c + gOne, c + gOne + gI, c + gOne), ⟨Or.inr (Or.inl rfl), by simpa [cellOther] using hn⟩, rfl⟩
    · exact ⟨(c + gOne + gI, c + gI, c + gI), ⟨Or.inr (Or.inr (Or.inl rfl)), by simpa [cellOther] using hn⟩, rfl⟩
    · exact ⟨(c + gI, c, c - gOne), ⟨Or.inr (Or.inr (Or.inr rfl)), by simpa [cellOther] using hn⟩, rfl⟩

theorem cellEdge_injective : Function.Injective (fun p : GInt × Fin 4 => cellEdge p.1 p.2) := by
  rintro ⟨c, j⟩ ⟨c', j'⟩ h
  fin_cases j <;> fin_cases j' <;> simp [cellEdge, Prod.ext_iff, gOne, gI] at h ⊢ <;> omega

theorem omegaE_cellEdge_sum (c : GInt) : ∑ j : Fin 4, omegaE (cellEdge c j) = 2 := by
  simp [Fin.sum_univ_four, cellEdge, omegaE, gOne, gI]
  ring

theorem cellOther_ne (c : GInt) (j : Fin 4) : cellOther c j ≠ c := by
  fin_cases j <;> simp [cellOther, gOne, gI]

theorem cellOther_involution (c : GInt) (j : Fin 4) : cellOther (cellOther c j) (j + 2) = c := by
  fin_cases j <;> simp [cellOther, gOne, gI]

theorem cellEdge_involution (c : GInt) (j : Fin 4) :
    cellEdge (cellOther c j) (j + 2) = edgeRev (cellEdge c j) := by
  fin_cases j <;> simp [cellEdge, cellOther, edgeRev, gOne, gI] <;> abel

/-- Green's identity: the shoelace sum of the boundary of a finite set of cells is twice its cardinality. -/
theorem green_boundary (T : CellTile) : ∑ e ∈ T.boundaryEdges, omegaE e = 2 * (T.card : ℤ) := by
  classical
  set P : Finset (GInt × Fin 4) := T ×ˢ (Finset.univ : Finset (Fin 4)) with hP
  have hall : ∑ p ∈ P, omegaE (cellEdge p.1 p.2) = 2 * (T.card : ℤ) := by
    rw [hP, Finset.sum_product]
    simp only [omegaE_cellEdge_sum]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hin : ∑ p ∈ P.filter (fun p => cellOther p.1 p.2 ∈ T), omegaE (cellEdge p.1 p.2) = 0 := by
    apply Finset.sum_involution (fun p _ => (cellOther p.1 p.2, p.2 + 2))
    · intro p _
      rw [cellEdge_involution, omegaE_rev]
      ring
    · intro p _ _ h
      apply cellOther_ne p.1 p.2
      exact congrArg Prod.fst h
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        cellOther_involution] at hp ⊢
      exact ⟨hp.2, hp.1⟩
    · intro p _
      obtain ⟨c, j⟩ := p
      have hj : j + 2 + 2 = j := by fin_cases j <;> rfl
      simp only [cellOther_involution, hj]
  have hb : T.boundaryEdges =
      (P.filter (fun p => cellOther p.1 p.2 ∉ T)).image (fun p => cellEdge p.1 p.2) := by
    ext e
    rw [mem_boundaryEdges_iff, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, j, rfl, hn⟩
      exact ⟨(c, j), by simp [hP, hc, hn], rfl⟩
    · rintro ⟨⟨c, j⟩, hmem, rfl⟩
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hmem
      exact ⟨c, hmem.1, j, rfl, hmem.2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p => cellOther p.1 p.2 ∈ T)
    (fun p => omegaE (cellEdge p.1 p.2))
  rw [hin, zero_add] at hsplit
  rw [hb, Finset.sum_image (fun p _ q _ h => cellEdge_injective h), hsplit, hall]

end FLatticePaper.Tiles
