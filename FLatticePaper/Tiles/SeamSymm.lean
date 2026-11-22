import FLatticePaper.Tiles.StandardHalfTurn
import FLatticePaper.Tiles.FourWalks
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.BaseCellIdentities

/-! The half-turn symmetry of the boundary of a standard cell tile (the `symm` input of `BottomSeam`).

The cell tile commutes with the rotation and the translation of the vertex tile (`cellTileOf_rot`, `cellTileOf_shift`).
Hence `rot_rot_oddTile` gives `rotCells (rotCells C) = C + c'` for the cell tile `C`, and the boundary edges give the
symmetry `e ↦ -e - c'` of `C`. The centre `-c'` is the sum of the bottom and right words (`sum_odd_identity`), from the
bottom sums of `StandardBoundary.lean` and the rotation of the parents (`current_swap`). -/

namespace FLatticePaper.Tiles.SeamSymm

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BoundaryWalks
open FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StandardHalfTurn
open FLatticePaper.Tiles.FourWalks


theorem cellTileOf_rot (P : Tile) : cellTileOf (rot P) = rotCells (cellTileOf P) := by
  ext ⟨x, y⟩
  simp only [mem_cellTileOf, mem_rotCells, rotCInv]
  rw [cellCorners_subset_iff, cellCorners_subset_iff]
  simp only [mem_rot]
  ring_nf
  tauto

theorem cellTileOf_shift (P : Tile) (v : GInt) : cellTileOf (shift P v) = (cellTileOf P).image (· + v) := by
  obtain ⟨v1, v2⟩ := v
  ext ⟨x, y⟩
  rw [mem_cellTileOf, mem_image_add_iff, mem_cellTileOf]
  unfold shift
  simp only [mem_image_add_iff, Prod.mk_sub_mk, cellCorners_subset_iff]
  ring_nf


/-- The rotation of the parents: the even child of the swapped word is the rotated odd child, and conversely. -/
theorem current_swap (w : Word) :
    (parentsAt (swapW w)).current .even = ((parentsAt w).current .odd).rotate ∧
      (parentsAt (swapW w)).current .odd = ((parentsAt w).current .even).rotate := by
  have hV := parentsAt_valid w
  have ho := hV.odd_parity
  have he := hV.even_parity
  unfold Fraction.Odd at ho
  unfold Fraction.Even at he
  have hsw : parentsAt (swapW w) = ⟨(parentsAt w).even.rotate, (parentsAt w).odd.rotate⟩ :=
    parentsAt_swap_eq w
  rw [hsw]
  constructor
  · simp only [Parents.current, Parents.combine, Fraction.rotate]
    split_ifs <;> simp only [Fraction.mk.injEq] <;> omega
  · simp only [Parents.current, Parents.combine, Fraction.rotate]
    split_ifs <;> simp only [Fraction.mk.injEq] <;> omega

/-- The bottom and right sums of the odd tile of `w`, and the rotation centre. -/
theorem sum_odd_identity (w : Word) :
    F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) =
      -(tF ((parentsAt (swapW w)).current .even) + mulI (tF ((parentsAt w).current .odd))) := by
  have hS1 : F2Word.sum (oddBottom w) = texV1Odd (fracOdd w) - gI := by
    have h := sum_oddBottom w
    unfold almostV₁ at h
    exact eq_sub_of_add_eq h
  have hS2 : F2Word.sum (oddRight w) = texV2 (fracOdd w) + gOne := by
    have h := sum_oddRight w
    unfold almostV₂ at h
    exact eq_add_of_sub_eq h
  have hV := parentsAt_valid w
  have ho := hV.odd_parity
  have he := hV.even_parity
  unfold Fraction.Odd at ho
  unfold Fraction.Even at he
  have hodd : ((parentsAt w).current .odd).Odd := by
    unfold Fraction.Odd
    simp only [Parents.current, Parents.combine]
    omega
  rw [hS1, hS2, (current_swap w).1, rotate_eq_of_odd hodd]
  simp only [fracOdd]
  ext <;> simp [texV1Odd, texV2, tF, tV, mulI, gI, gOne] <;> omega

/-- The bottom and right sums of the even tile of `w`, and the rotation centre. -/
theorem sum_even_identity (w : Word) :
    F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) =
      -(tF ((parentsAt (swapW w)).current .odd) + mulI (tF ((parentsAt w).current .even))) := by
  have hS1 : F2Word.sum (evenBottom w) = texV1Even (fracEven w) - gI := by
    have h := sum_evenBottom w
    unfold almostV₁ at h
    exact eq_sub_of_add_eq h
  have hS2 : F2Word.sum (evenRight w) = texV2 (fracEven w) + gOne := by
    have h := sum_evenRight w
    unfold almostV₂ at h
    exact eq_add_of_sub_eq h
  have hV := parentsAt_valid w
  have ho := hV.odd_parity
  have he := hV.even_parity
  unfold Fraction.Odd at ho
  unfold Fraction.Even at he
  have heven : ((parentsAt w).current .even).Even := by
    unfold Fraction.Even
    simp only [Parents.current, Parents.combine]
    omega
  unfold Fraction.Even at heven
  rw [hS1, hS2, (current_swap w).2, rotate_eq_of_even (show ((parentsAt w).current .even).Even from heven)]
  simp only [fracEven]
  ext <;> simp [texV1Even, texV2, tF, tV, mulI, gI, gOne] <;> omega

theorem rotI_rotI (z : GInt) : rotI (rotI z) = -z := by
  ext <;> simp [rotI]


/-- A tile whose half-turn is a translate of itself has a boundary symmetric under `e ↦ -c - e`. -/
theorem symm_of_rot (P : Tile) (c : GInt) (hP : rot (rot P) = shift P c) :
    ∀ e ∈ (cellTileOf P).boundaryEdges, halfE (-c) e ∈ (cellTileOf P).boundaryEdges := by
  intro e he
  have hrr : rotCells (rotCells (cellTileOf P)) = (cellTileOf P).image (· + c) := by
    rw [← cellTileOf_rot, ← cellTileOf_rot, hP, cellTileOf_shift]
  have hb1 : (rotCells (rotCells (cellTileOf P))).boundaryEdges =
      ((cellTileOf P).boundaryEdges.image rotE).image rotE := by
    rw [boundaryEdges_rotCells, boundaryEdges_rotCells]
  have hb2 : CellTile.boundaryEdges ((cellTileOf P).image (· + c)) = (cellTileOf P).boundaryEdges.image (transE c) :=
    boundaryEdges_translate _ c
  have hmem : rotE (rotE e) ∈ CellTile.boundaryEdges ((cellTileOf P).image (· + c)) := by
    rw [← hrr, hb1]
    exact Finset.mem_image.2 ⟨rotE e, Finset.mem_image.2 ⟨e, he, rfl⟩, rfl⟩
  rw [hb2] at hmem
  obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 hmem
  have hfx : f = halfE (-c) e := by
    refine Prod.ext ?_ ?_
    · have h1 : f.1 + c = rotI (rotI e.1) := congrArg Prod.fst hfe
      rw [rotI_rotI] at h1
      show f.1 = -c - e.1
      rw [eq_sub_of_add_eq h1]
      abel
    · have h2 : f.2 + c = rotI (rotI e.2) := congrArg Prod.snd hfe
      rw [rotI_rotI] at h2
      show f.2 = -c - e.2
      rw [eq_sub_of_add_eq h2]
      abel
  rw [hfx] at hf
  exact hf

/-- The symmetry of the odd cell tile, about the centre of its bottom and right words. -/
theorem symm_odd (w : Word) : ∀ e ∈ (cellTileOf (oddTile w)).boundaryEdges,
    halfE (F2Word.sum (oddBottom w) + F2Word.sum (oddRight w)) e ∈ (cellTileOf (oddTile w)).boundaryEdges := by
  rw [sum_odd_identity]
  exact symm_of_rot (oddTile w) _ (rot_rot_oddTile w)

/-- The symmetry of the even cell tile, about the centre of its bottom and right words. -/
theorem symm_even (w : Word) : ∀ e ∈ (cellTileOf (evenTile w)).boundaryEdges,
    halfE (F2Word.sum (evenBottom w) + F2Word.sum (evenRight w)) e ∈ (cellTileOf (evenTile w)).boundaryEdges := by
  rw [sum_even_identity]
  exact symm_of_rot (evenTile w) _ (rot_rot_evenTile w)

end FLatticePaper.Tiles.SeamSymm
