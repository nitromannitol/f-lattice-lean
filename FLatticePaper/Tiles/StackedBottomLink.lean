import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.NeighbourDisjoint
import FLatticePaper.Tiles.StandardCornerCells
import FLatticePaper.Tiles.StandardBoundary

/-! The lower bound of the sites of a standard tile over a column by its bottom walk. A site of the tile over column `t` is a
corner of a cell of the tile, and the row form of that cell (`mem_iff_nr`) puts the column `t` at or below the exit column of
the bottom walk at the cell's row. The least row of the walk that reaches column `t` then gives a point of the bottom walk over
`t` at or below the site: the lowest site over `t` is at or above the bottom walk over `t` (the text's `B^- ≤ x2`). -/

namespace FLatticePaper.Tiles.StackedBottomLink

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.OverlapSides
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause

/-- **The walk reaches every column up to its exit column.** For a word with letters `one` and `i`, a column `r` with
`0 ≤ r ≤ colN u (0,0) n` is reached by the walk from `(0,0)` at a row `h ≤ n`: take the least row whose exit column is at
least `r`. -/
theorem walk_reach (u : F2Word) (hu : ∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i) (r n : ℤ) (hr : 0 ≤ r) (hn0 : 0 ≤ n)
    (hnu : n ≤ cntI u) (hrn : r ≤ colN u (0, 0) n) :
    ∃ h : ℤ, 0 ≤ h ∧ h ≤ n ∧ ((r, h) : GInt) ∈ F2Word.walk (0, 0) u := by
  classical
  have hk : r ≤ colN u (0, 0) ((n.toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hn0]; exact hrn
  have hex : ∃ k : ℕ, r ≤ colN u (0, 0) (k : ℤ) := ⟨n.toNat, hk⟩
  have hm : r ≤ colN u (0, 0) ((Nat.find hex : ℕ) : ℤ) := Nat.find_spec hex
  have hmle : Nat.find hex ≤ n.toNat := Nat.find_min' hex hk
  have hmn : ((Nat.find hex : ℕ) : ℤ) ≤ n := by
    have := Int.toNat_of_nonneg hn0
    omega
  refine ⟨((Nat.find hex : ℕ) : ℤ), by positivity, hmn, ?_⟩
  apply OverlapSides.mem_walk_one_i u hu (0, 0) r ((Nat.find hex : ℕ) : ℤ)
  · simp
  · have := cntI_nonneg u
    simp only
    omega
  · intro _
    simpa using hr
  · intro hpos
    simp only at hpos
    have hpos' : 1 ≤ Nat.find hex := by omega
    have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hnot := Nat.find_min hex hlt
    have hcast : ((Nat.find hex : ℕ) : ℤ) - 1 = ((Nat.find hex - 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    push_neg at hnot
    exact hnot.le
  · exact hm

/-- **The lower bound of the sites over a column.** Let `P` be a site set whose sites are corners of its cells, with boundary word
`boundaryWordOf w1 w2` from the origin. A site `x` of `P` over a column `t` with `0 ≤ t ≤ w1`'s total width has a point of the
bottom walk over `t` at or below it. -/
theorem lower_link (P : Finset GInt) (w1 w2 : F2Word) (hP : HasCornerCell P)
    (hT : IsBoundaryWordAt (cellTileOf P) (0, 0) (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = Unit4.one ∨ x = Unit4.i) (h2 : ∀ x ∈ w2, x = Unit4.i ∨ x = Unit4.negOne)
    (x : GInt) (hx : x ∈ P) (t : ℤ) (ht : x.1 = t) (ht0 : 0 ≤ t) (htF : t ≤ (F2Word.sum w1).1) :
    ∃ h : ℤ, h ≤ x.2 ∧ ((t, h) : GInt) ∈ F2Word.walk (0, 0) w1 := by
  obtain ⟨c, hc, hxc⟩ := corner_of_hcc hP hx
  have hc' : ((c.1, c.2) : GInt) ∈ cellTileOf P := by simpa using hc
  have hrow := (mem_iff_nr hT h1 h2 c.1 c.2).1 hc'
  obtain ⟨⟨hb0, _⟩, _, hN⟩ := hrow
  have hb0' : 0 ≤ c.2 := by simpa using hb0
  have hN' : c.1 < Nrow (0, 0) w1 w2 c.2 := by simpa using hN
  have hkey : t ≤ c.1 + 1 ∧ c.2 ≤ x.2 := by
    have e1 : (x.1 = c.1 ∧ x.2 = c.2) ∨ (x.1 = c.1 + 1 ∧ x.2 = c.2) ∨
        (x.1 = c.1 ∧ x.2 = c.2 + 1) ∨ (x.1 = c.1 + 1 ∧ x.2 = c.2 + 1) := by
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hxc
      rcases hxc with h | h | h | h <;> subst h <;> simp [gOne, gI] <;> omega
    omega
  rcases lt_or_ge c.2 (cntI w1) with hlt | hge
  · rw [nrow_lo hlt] at hN'
    obtain ⟨h, hh0, hhn, hw⟩ := walk_reach w1 h1 t c.2 ht0 hb0' hlt.le (by omega)
    exact ⟨h, by omega, hw⟩
  · have hcn : 0 ≤ cntI w1 := cntI_nonneg w1
    have hu : ∀ y ∈ w1, y ≠ Unit4.negI := fun y hy => by
      rcases h1 y hy with h | h <;> rw [h] <;> decide
    have hcol : colN w1 (0, 0) (cntI w1) = (F2Word.sum w1).1 :=
      colN_top w1 hu (cntI w1) le_rfl
    obtain ⟨h, hh0, hhn, hw⟩ := walk_reach w1 h1 t (cntI w1) ht0 hcn le_rfl (by rw [hcol]; exact htF)
    exact ⟨h, by omega, hw⟩

/-- **The lower bound of the sites of the odd standard tile over a column**, by its bottom walk `oddBottom w`. -/
theorem odd_lower_link (w : Word) (x : GInt) (hx : x ∈ oddTile w) (t : ℤ) (ht : x.1 = t) (ht0 : 0 ≤ t)
    (htF : t ≤ (F2Word.sum (oddBottom w)).1) :
    ∃ h : ℤ, h ≤ x.2 ∧ ((t, h) : GInt) ∈ F2Word.walk (0, 0) (oddBottom w) :=
  lower_link (oddTile w) (oddBottom w) (oddRight w) (oddTile_hcc w) (OverlapSides.boundary_odd w)
    (admissible_oddStandard w).1.1 (OverlapSides.letters_w2 (admissible_oddStandard w).2) x hx t ht ht0 htF

end FLatticePaper.Tiles.StackedBottomLink
