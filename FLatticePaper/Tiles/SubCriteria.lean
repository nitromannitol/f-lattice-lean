import FLatticePaper.Tiles.CheckerFree
import FLatticePaper.Tiles.CellFourTests
import FLatticePaper.Tiles.StandardClauseA

/-! Task Q25 (sub), the boundary criteria of a cell tile.

An east edge `p → p + 1` of the bottom walk is a boundary edge of a cell tile `T` exactly when the cell with lower-left
corner `p` is in `T` and the cell below it, with lower-left corner `p − i`, is not. A north edge `p → p + i` is a boundary
edge exactly when the cell with lower-left corner `p − 1` is in `T` and the cell with lower-left corner `p` is not
(`east_mem_boundaryEdges_iff`, `north_mem_boundaryEdges_iff`). For the cell tile of a fraction, the membership of a cell
is the four-test bound of Q25 (1) (`cellCorners_subset_iff_bounds`). -/

namespace FLatticePaper.Tiles.SubCriteria

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.CellFourTests FLatticePaper.Tiles.SiteInduction

/-- The east edge `p → p + 1` is a boundary edge of `T` iff `p` is a cell of `T` and `p − i` is not. -/
theorem east_mem_boundaryEdges_iff (T : CellTile) (p : GInt) :
    (p, p + gOne) ∈ T.boundaryEdges ↔ p ∈ T ∧ p - gI ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, he⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · simp only [Prod.mk.injEq] at he
      obtain ⟨h1, -⟩ := he
      subst h1
      exact ⟨hc, hnot⟩
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gOne, gI] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gOne, gI] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gOne, gI] at h1 h2
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨p, h1, (p, p + gOne, p - gI), ?_, h2, rfl⟩
    unfold cellEdgesWithOther
    exact List.mem_cons_self

/-- The north edge `p → p + i` is a boundary edge of `T` iff `p − 1` is a cell of `T` and `p` is not. -/
theorem north_mem_boundaryEdges_iff (T : CellTile) (p : GInt) :
    (p, p + gI) ∈ T.boundaryEdges ↔ p - gOne ∈ T ∧ p ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, he⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gOne, gI] at h1 h2
      omega
    · simp only [Prod.mk.injEq] at he
      obtain ⟨h1, -⟩ := he
      have hc' : c = p - gOne := eq_sub_of_add_eq h1
      subst hc'
      refine ⟨hc, ?_⟩
      simpa using hnot
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gOne, gI] at h1 h2
      omega
    · exfalso
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, gI] at h1 h2
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨p - gOne, h1, (p - gOne + gOne, p - gOne + gOne + gI, p - gOne + gOne), ?_, ?_,
      Prod.ext (by simp) (by simp)⟩
    · unfold cellEdgesWithOther
      exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · simpa using h2

/-- A cell of a finite set `P` is a cell of its tile `cellTileOf P` iff its four corners lie in `P`. -/
theorem mem_cellTileOf_iff (P : Finset GInt) (c : GInt) : c ∈ cellTileOf P ↔ cellCorners c ⊆ P := by
  unfold cellTileOf
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h (by simp [cellCorners]), h⟩

/-- For a finite set `P` whose membership is the fraction `f`, a cell is in `P` (all corners) iff the four-test bounds
of Q25 (1) hold at its lower-left corner. -/
theorem cellCorners_subset_iff_bounds (f : Fraction) (hodd : (f.num + f.den) % 2 = 1) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (P : Finset GInt) (hP : ∀ x : GInt, x ∈ P ↔ InH f x) (z : GInt) :
    cellCorners z ⊆ P ↔
      ((2 * f.den - tOf f - cellK f (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo f z ∧
          tCo f z ≤ cellK f (decide ((z.1 + z.2) % 2 = 0))) ∧
        (lOf f (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo f z ∧
          sCo f z ≤ 2 * tOf f - 2 * (f.den - f.num) - lOf f (decide ((z.1 + z.2) % 2 = 0)))) := by
  rw [← cell_four_tests_iff f hodd hpos hlt z]
  have e1 : z + gOne = (z.1 + 1, z.2) := Prod.ext (by simp [gOne]) (by simp [gOne])
  have e2 : z + gI = (z.1, z.2 + 1) := Prod.ext (by simp [gI]) (by simp [gI])
  have e3 : z + (gOne + gI) = (z.1 + 1, z.2 + 1) := Prod.ext (by simp [gOne, gI]) (by simp [gOne, gI])
  simp only [cellCorners, Finset.insert_subset_iff, Finset.singleton_subset_iff, hP, e1, e2, e3]

end FLatticePaper.Tiles.SubCriteria
