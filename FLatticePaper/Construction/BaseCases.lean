import FLatticePaper.Plane.OdometerTheorem
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Construction.LadderCoverage
import FLatticePaper.Farey.EarlierChain
import FLatticePaper.Farey.Rotation

namespace FLatticePaper.Construction
open Farey

/-- The children of the word `3^k`: the even child is `1/(2k+3)`, the odd child is `1/(2k+2)`. -/
theorem baseChildren_threes (k : ℕ) :
    (parentsAt (List.replicate k .three)).current .even = ⟨1, 2 * k + 3⟩ ∧
      (parentsAt (List.replicate k .three)).current .odd = ⟨1, 2 * k + 2⟩ := by
  unfold parentsAt
  rw [Parents.walk_threes]
  constructor
  · simp only [Parents.current, Parents.combine, root]
    congr 1
    ring
  · simp only [Parents.current, Parents.combine, root]
    congr 1
    ring

/-- The parents of the word `2^k` are the rotations of those of `3^k`. -/
theorem parentsAt_replicate_two (k : ℕ) :
    parentsAt (List.replicate k .two) = (parentsAt (List.replicate k .three)).rotate := by
  rw [rotate_parentsAt, List.map_replicate]
  rfl

/-- The children of the word `2^k` are the rotations of the children of `3^k`, with the parities exchanged. -/
theorem baseChildren_twos (k : ℕ) :
    (parentsAt (List.replicate k .two)).current .odd = Fraction.rotate ⟨1, 2 * k + 3⟩ ∧
      (parentsAt (List.replicate k .two)).current .even = Fraction.rotate ⟨1, 2 * k + 2⟩ := by
  constructor
  · rw [parentsAt_replicate_two, ← (baseChildren_threes k).1]
    exact ((parentsAt_valid (List.replicate k .three)).rotate_current_even).symm
  · rw [parentsAt_replicate_two, ← (baseChildren_threes k).2]
    exact ((parentsAt_valid (List.replicate k .three)).rotate_current_odd).symm

/-- A cover of the reciprocal deck by the raw sites, read through the tile, covers every class with a deck vector. -/
theorem covers_tile_of_covers {d : ℤ} {sites : Finset Site} {tile : Set Site}
    (hcov : (Fraction.mk 1 d).modifiedDeck.Covers sites) (hmem : ∀ x, x ∈ tile ↔ x ∈ sites) :
    ∀ z : Site, ∃ y ∈ tile, ∃ i j : ℤ, z = y + (Fraction.mk 1 d).modifiedDeck.combine i j := by
  intro z
  obtain ⟨y, hy, hs⟩ := hcov z
  obtain ⟨i, j, hij⟩ := hs
  exact ⟨y, (hmem y).mpr hy, i, j, by rw [← hij]; abel⟩

/-- `prop:base_cases` (b), odd denominators: the stair alternate tile covers every class of `L'(1/d)`. -/
theorem prop_base_cases_alternate_cover_odd {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∀ z : Site, ∃ y ∈ paperStairAltTile d, ∃ i j : ℤ,
      z = y + (Fraction.mk 1 d).modifiedDeck.combine i j :=
  covers_tile_of_covers (stairEvenAlt_raw_cover (show BaseMask.stairEvenAlt.Valid d from hd))
    (fun x => mem_paperStairAltTile_iff d hd.1 x)

/-- `prop:base_cases` (b), even denominators: the ladder alternate tile covers every class of `L'(1/d)`. -/
theorem prop_base_cases_alternate_cover_even {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∀ z : Site, ∃ y ∈ paperLadderAltTile d, ∃ i j : ℤ,
      z = y + (Fraction.mk 1 d).modifiedDeck.combine i j :=
  covers_tile_of_covers (ladderOddAlt_raw_cover (show BaseMask.ladderOddAlt.Valid d from hd))
    (fun x => mem_paperLadderAltTile_iff d hd.1 x)

/-- `prop:base_cases` (c): both children of the word `3^k` satisfy `theorem:odometers`. -/
theorem prop_base_cases_odometers (k : ℕ) :
    OdometersTheoremAt ((parentsAt (List.replicate k .three)).current .odd) ∧
      OdometersTheoremAt ((parentsAt (List.replicate k .three)).current .even) ∧
      OdometersTheoremAt ((parentsAt (List.replicate k .two)).current .odd) ∧
      OdometersTheoremAt ((parentsAt (List.replicate k .two)).current .even) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(baseChildren_threes k).2]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h2 : OdometersTheoremAt (Fraction.rotate ⟨1, 3⟩) := (odometersTheoremAt_base (d := 3) (by norm_num)).2
      have e : Fraction.rotate (⟨1, 3⟩ : Fraction) = ⟨1, 2⟩ := by decide
      rw [e] at h2
      simpa using h2
    · exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 2) (by omega)).1
  · rw [(baseChildren_threes k).1]
    exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 3) (by omega)).1
  · rw [(baseChildren_twos k).1]
    exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 3) (by omega)).2
  · rw [(baseChildren_twos k).2]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h3 : OdometersTheoremAt (⟨1, 3⟩ : Fraction) := (odometersTheoremAt_base (d := 3) (by norm_num)).1
      have e : Fraction.rotate (⟨1, 2 * ((0 : ℕ) : ℤ) + 2⟩ : Fraction) = ⟨1, 3⟩ := by decide
      rw [e]
      exact h3
    · exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 2) (by omega)).2

end FLatticePaper.Construction
