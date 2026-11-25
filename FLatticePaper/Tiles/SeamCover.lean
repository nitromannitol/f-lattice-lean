import FLatticePaper.Tiles.WalkLines
import FLatticePaper.Tiles.WordCounts
import FLatticePaper.Tiles.CellIntervals
import FLatticePaper.Tiles.CellBox
import FLatticePaper.Tiles.CellTestGen
import FLatticePaper.Tiles.WalkCover
import FLatticePaper.Tiles.SubCriteria

/-! Task Q25 (completeness of the seam), the generic cover and nodup of the four-walk boundary word (`fixes/Q25.md`, "The cell boundary").

For a fraction `f = (N, D)` with `0 < N < D`, the cell tile `T = cellTileOf P` of its H set `P` has interval rows and columns
(`col_interval`, `row_interval`), lies in the box `[1 − C, μD − 1] × [0, μN + L − 2]` (`box_core`), where `C = D − N`, `L = D + N` and
`μ = muOf f`. If the two words `w1` (the bottom walk) and `w2` (the right walk) have the letter counts `μD`, `C − 1`, `μN − 1 + L`, then the
four-walk word `edgesFrom 0 (boundaryWordOf w1 w2)` covers the boundary of `T` and has no repeated edge (`cover_of_walk`). -/

namespace FLatticePaper.Tiles.SeamCover

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.CellFourTests FLatticePaper.Tiles.CellIntervals
  FLatticePaper.Tiles.CellBox FLatticePaper.Tiles.WalkCover FLatticePaper.Tiles.SubBlockOdd
  FLatticePaper.Tiles.CellTestGen FLatticePaper.Tiles.FourWalks

theorem cellK_pk (f : Fraction) (x y : ℤ) :
    cellK f (decide ((x + y) % 2 = 0)) = pk (f.den - f.num) (max (f.den - 2 * f.num) f.num) (x + y) := by
  unfold cellK pk
  by_cases h : (x + y) % 2 = 0
  · simp [h]
  · simp [h]

theorem lOf_pk (f : Fraction) (x y : ℤ) :
    lOf f (decide ((x + y) % 2 = 0)) = pk 0 (min (f.den - f.num) (3 * f.num - f.den)) (x + y) := by
  unfold lOf pk
  by_cases h : (x + y) % 2 = 0
  · simp [h]
  · simp [h]

/-- The membership of a site in the cell tile, in the parity constants. -/
theorem mem_cellTile_pk (f : Fraction) (hpos : 0 < f.num) (hlt : f.num < f.den) (P : Finset GInt)
    (hP : ∀ z : GInt, z ∈ P ↔ InH f z) (x y : ℤ) :
    (x, y) ∈ cellTileOf P ↔
      (2 * f.den - tOf f - pk (f.den - f.num) (max (f.den - 2 * f.num) f.num) (x + y) ≤ f.num * x - f.den * y ∧
        f.num * x - f.den * y ≤ pk (f.den - f.num) (max (f.den - 2 * f.num) f.num) (x + y)) ∧
      (pk 0 (min (f.den - f.num) (3 * f.num - f.den)) (x + y) ≤ (f.den + f.num) * x + (f.den - f.num) * y ∧
        (f.den + f.num) * x + (f.den - f.num) * y ≤
          muOf f * tOf f - 2 * (f.den - f.num) - pk 0 (min (f.den - f.num) (3 * f.num - f.den)) (x + y)) := by
  rw [SubCriteria.mem_cellTileOf_iff, cell_test_gen f hpos hlt P hP x y, cellK_pk, lOf_pk]

/-- The box of the cell tile. -/
theorem box_of_mem (f : Fraction) (hpos : 0 < f.num) (hlt : f.num < f.den) (P : Finset GInt)
    (hP : ∀ z : GInt, z ∈ P ↔ InH f z) (p : GInt) (hp : p ∈ cellTileOf P) :
    1 - (f.den - f.num) ≤ p.1 ∧ p.1 ≤ muOf f * f.den - 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ muOf f * f.num + (f.den + f.num) - 2 := by
  obtain ⟨x, y⟩ := p
  have hm := (mem_cellTile_pk f hpos hlt P hP x y).1 hp
  have hm' := (mem_cellTile_pk f hpos hlt P hP x y).1 hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hm
  have hmu : muOf f = 1 ∨ muOf f = 2 := by
    unfold muOf
    split_ifs <;> simp
  by_cases hpar : (x + y) % 2 = 0
  · have hk : pk (f.den - f.num) (max (f.den - 2 * f.num) f.num) (x + y) = f.den - f.num := by
      unfold pk; simp [hpar]
    have hl : pk 0 (min (f.den - f.num) (3 * f.num - f.den)) (x + y) = 0 := by
      unfold pk; simp [hpar]
    rw [hk] at h1 h2
    rw [hl] at h3 h4
    have := box_core f.num f.den (muOf f) x y (f.den - f.num) 0 (by omega) (by omega) (by rcases hmu with h | h <;> omega)
      (by rcases hmu with h | h <;> omega) h1 h2 h3 h4 (box_facts_even f.num f.den (by omega) (by omega)).1
      (box_facts_even f.num f.den (by omega) (by omega)).2.1 (box_facts_even f.num f.den (by omega) (by omega)).2.2
    exact this
  · have hk : pk (f.den - f.num) (max (f.den - 2 * f.num) f.num) (x + y) = max (f.den - 2 * f.num) f.num := by
      unfold pk; simp [hpar]
    have hl : pk 0 (min (f.den - f.num) (3 * f.num - f.den)) (x + y) = min (f.den - f.num) (3 * f.num - f.den) := by
      unfold pk; simp [hpar]
    rw [hk] at h1 h2
    rw [hl] at h3 h4
    have f3 := box_facts_odd f.num f.den (by omega) (by omega)
    exact box_core f.num f.den (muOf f) x y _ _ (by omega) (by omega) (by rcases hmu with h | h <;> omega)
      (by rcases hmu with h | h <;> omega) h1 h2 h3 h4 f3.1 f3.2.1 f3.2.2

/-- **The four-walk boundary word covers the boundary of the H-set cell tile, each edge once.** The hypotheses are the letter
conditions on the two walks, the boundary condition of the bottom walk and of its half-turn, and the three letter counts. -/
theorem cover_of_walk (f : Fraction) (hpos : 0 < f.num) (hlt : f.num < f.den) (P : Finset GInt)
    (hP : ∀ z : GInt, z ∈ P ↔ InH f z) (w1 w2 : F2Word)
    (hw1 : ∀ z ∈ w1, z = .one ∨ z = .i) (hw2 : ∀ z ∈ w2, z = .i ∨ z = .negOne)
    (hsub : ∀ e ∈ edgesFrom 0 w1 ++ edgesFrom (F2Word.sum w1) w2, e ∈ (cellTileOf P).boundaryEdges)
    (hsymm : ∀ e ∈ (cellTileOf P).boundaryEdges,
      halfE (F2Word.sum w1 + F2Word.sum w2) e ∈ (cellTileOf P).boundaryEdges)
    (h1 : (List.count Unit4.one w1 : ℤ) = muOf f * f.den)
    (h2 : (List.count Unit4.negOne w2 : ℤ) = f.den - f.num - 1)
    (h3 : (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 = muOf f * f.num - 1 + (f.den + f.num)) :
    (∀ e ∈ (cellTileOf P).boundaryEdges, e ∈ edgesFrom 0 (boundaryWordOf w1 w2)) ∧
      (edgesFrom 0 (boundaryWordOf w1 w2)).Nodup := by
  have hN := hpos
  have hND := hlt
  have hcol : ∀ x y1 y2 y3 : ℤ, y1 ≤ y2 → y2 ≤ y3 → ((x, y1) : GInt) ∈ cellTileOf P →
      ((x, y3) : GInt) ∈ cellTileOf P → ((x, y2) : GInt) ∈ cellTileOf P := by
    intro x y1 y2 y3 h12 h23 ha hc
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := (mem_cellTile_pk f hpos hlt P hP x y1).1 ha
    obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := (mem_cellTile_pk f hpos hlt P hP x y3).1 hc
    have hm := col_interval (f.den - f.num) (max (f.den - 2 * f.num) f.num) 0 (min (f.den - f.num) (3 * f.num - f.den))
      f.num f.den (tOf f) (muOf f * tOf f - 2 * (f.den - f.num)) x y1 y2 y3 (by omega) hpos hlt
      (max_le (by omega) (by omega))
      (by have := le_max_right (f.den - 2 * f.num) f.num; omega)
      (by have := min_le_left (f.den - f.num) (3 * f.num - f.den); omega)
      (by have : -(f.den - f.num) ≤ min (f.den - f.num) (3 * f.num - f.den) := le_min (by omega) (by omega); omega)
      h12 h23 ⟨a1, a2, a3, a4⟩ ⟨c1, c2, c3, c4⟩
    exact (mem_cellTile_pk f hpos hlt P hP x y2).2 ⟨⟨hm.1, hm.2.1⟩, ⟨hm.2.2.1, hm.2.2.2⟩⟩
  have hrow : ∀ y x1 x2 x3 : ℤ, x1 ≤ x2 → x2 ≤ x3 → ((x1, y) : GInt) ∈ cellTileOf P →
      ((x3, y) : GInt) ∈ cellTileOf P → ((x2, y) : GInt) ∈ cellTileOf P := by
    intro y x1 x2 x3 h12 h23 ha hc
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := (mem_cellTile_pk f hpos hlt P hP x1 y).1 ha
    obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := (mem_cellTile_pk f hpos hlt P hP x3 y).1 hc
    have hm := row_interval (f.den - f.num) (max (f.den - 2 * f.num) f.num) 0 (min (f.den - f.num) (3 * f.num - f.den))
      f.num f.den (tOf f) (muOf f * tOf f - 2 * (f.den - f.num)) x1 x2 x3 y (by omega) hpos hlt
      (max_le (by omega) (by omega))
      (by have := le_max_left (f.den - 2 * f.num) f.num; omega)
      (by have := min_le_left (f.den - f.num) (3 * f.num - f.den); omega)
      (by have : -(f.den + f.num) ≤ min (f.den - f.num) (3 * f.num - f.den) := le_min (by omega) (by omega); omega)
      h12 h23 ⟨a1, a2, a3, a4⟩ ⟨c1, c2, c3, c4⟩
    exact (mem_cellTile_pk f hpos hlt P hP x2 y).2 ⟨⟨hm.1, hm.2.1⟩, ⟨hm.2.2.1, hm.2.2.2⟩⟩
  have hbox : ∀ p : GInt, p ∈ cellTileOf P → -(List.count Unit4.negOne w2 : ℤ) ≤ p.1 ∧
      p.1 ≤ (List.count Unit4.one w1 : ℤ) - 1 ∧ (0 : ℤ) ≤ p.2 ∧
        p.2 ≤ (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 - 1 := by
    intro p hp
    obtain ⟨b1, b2, b3, b4⟩ := box_of_mem f hpos hlt P hP p hp
    rw [h1, h2, h3]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hV : edgesFrom (0, 0) (w1 ++ w2) = edgesFrom 0 w1 ++ edgesFrom (F2Word.sum w1) w2 := by
    rw [edgesFrom_append]
    simp only [Prod.mk_zero_zero, zero_add]
  have hsub' : ∀ g ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2), g ∈ (cellTileOf P).boundaryEdges := by
    intro g hg
    rw [RegionBoundary.walk_split] at hg
    rcases List.mem_append.1 hg with h | h
    · rw [hV] at h
      exact hsub g h
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
      rw [hV] at hg'
      have hg'' := hsub g' hg'
      have := hsymm g' hg''
      have hz : F2Word.sum (w1 ++ w2) = F2Word.sum w1 + F2Word.sum w2 := by simp [F2Word.sum]
      rw [← hz] at this
      exact this
  obtain ⟨hL1, hL2, hL3, hL4⟩ := FLatticePaper.Tiles.WalkLines.lines_of_walk w1 w2 hw1 hw2
  have hE1 : ∀ x, cntE (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x ≤ 1 := fun x => by
    rw [hL1 x]
    split_ifs <;> omega
  have hE2 : ∀ x, -(List.count Unit4.negOne w2 : ℤ) ≤ x → x ≤ (List.count Unit4.one w1 : ℤ) - 1 →
      1 ≤ cntE (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x := fun x ha hb => by
    rw [hL1 x]
    split_ifs <;> omega
  have hW1 : ∀ x, cntW (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x ≤ 1 := fun x => by
    rw [hL2 x]
    split_ifs <;> omega
  have hW2 : ∀ x, -(List.count Unit4.negOne w2 : ℤ) ≤ x → x ≤ (List.count Unit4.one w1 : ℤ) - 1 →
      1 ≤ cntW (edgesFrom (0, 0) (boundaryWordOf w1 w2)) x := fun x ha hb => by
    rw [hL2 x]
    split_ifs <;> omega
  have hN1 : ∀ y, cntN (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y ≤ 1 := fun y => by
    rw [hL3 y]
    split_ifs <;> omega
  have hN2 : ∀ y, (0 : ℤ) ≤ y → y ≤ (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 - 1 →
      1 ≤ cntN (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y := fun y ha hb => by
    rw [hL3 y]
    split_ifs <;> omega
  have hS1 : ∀ y, cntS (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y ≤ 1 := fun y => by
    rw [hL4 y]
    split_ifs <;> omega
  have hS2 : ∀ y, (0 : ℤ) ≤ y → y ≤ (List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 - 1 →
      1 ≤ cntS (edgesFrom (0, 0) (boundaryWordOf w1 w2)) y := fun y ha hb => by
    rw [hL4 y]
    split_ifs <;> omega
  exact cover_nodup_of (cellTileOf P) (edgesFrom (0, 0) (boundaryWordOf w1 w2))
    (-(List.count Unit4.negOne w2 : ℤ)) ((List.count Unit4.one w1 : ℤ) - 1) 0
    ((List.count Unit4.i w1 : ℤ) + List.count Unit4.i w2 - 1)
    hcol hrow hbox hsub' hE1 hE2 hW1 hW2 hN1 hN2 hS1 hS2

end FLatticePaper.Tiles.SeamCover
