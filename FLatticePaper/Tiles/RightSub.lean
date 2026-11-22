import FLatticePaper.Tiles.SeamSymm
import FLatticePaper.Tiles.OriginCell

/-! The right edge of a standard tile is the turned top of the tile of the swapped word (TeX 2723, step 2, right edge).

`rot_standard_tiles` gives `rot (oddTile w) = shift (evenTile (swapW w)) a`, and the right word of the odd tile is the turned
bottom word of the even tile of the swapped word, `oddRight w = mulI (evenBottom (swapW w))`. Turning the right walk
gives the top side of the even tile of the swapped word, which is the half-turn of its bottom side (`symm_even`). So the
right edge is a boundary walk of `oddTile w` once the bottom walk of `evenTile (swapW w)` is one. -/

namespace FLatticePaper.Tiles.RightSub

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BoundaryWalks
open FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.BaseCellIdentities FLatticePaper.Tiles.StandardHalfTurn
open FLatticePaper.Tiles.FourWalks FLatticePaper.Tiles.SeamSymm FLatticePaper.Tiles.OriginCell

theorem mulI_mulI (x : Unit4) : Unit4.mulI (Unit4.mulI x) = Unit4.neg x := by
  cases x <;> rfl

/-- The turned walk with letters `mulI` is the walk with letters `neg`, turned. -/
theorem edgesFrom_map_rotE (S : GInt) (X : F2Word) :
    (edgesFrom S (X.map Unit4.mulI)).map rotE = edgesFrom (rotI S) (X.map Unit4.neg) := by
  have h := edgesFrom_rotI S (X.map Unit4.mulI)
  rw [← h]
  congr 1
  simp only [List.map_map, Function.comp_def, mulI_mulI]

/-- Transfer of the boundary along a rotation: `rot P = shift Q a` and the bottom walk of `Q` is a boundary walk. -/
theorem right_sub_general (P Q : Tile) (a z S : GInt) (X : F2Word) (hrot : rot P = shift Q a)
    (hS : rotI S = z + a)
    (hX : ∀ e ∈ edgesFrom 0 X, e ∈ CellTile.boundaryEdges (cellTileOf Q))
    (hsym : ∀ e ∈ CellTile.boundaryEdges (cellTileOf Q), halfE z e ∈ CellTile.boundaryEdges (cellTileOf Q)) :
    ∀ g ∈ edgesFrom S (X.map Unit4.mulI), g ∈ CellTile.boundaryEdges (cellTileOf P) := by
  intro g hg
  have hbridge : (CellTile.boundaryEdges (cellTileOf P)).image rotE =
      (CellTile.boundaryEdges (cellTileOf Q)).image (transE a) := by
    have h1 : rotCells (cellTileOf P) = (cellTileOf Q).image (· + a) := by
      rw [← cellTileOf_rot, hrot, cellTileOf_shift]
    have h2 := congrArg CellTile.boundaryEdges h1
    rw [boundaryEdges_rotCells, boundaryEdges_translate] at h2
    exact h2
  have hwalk : (edgesFrom S (X.map Unit4.mulI)).map rotE =
      ((edgesFrom 0 X).map (halfE z)).map (transE a) := by
    rw [edgesFrom_map_rotE, hS, edgesFrom_translate]
    congr 1
    have h := edgesFrom_neg_half z X 0
    rw [sub_zero] at h
    rw [h]
  have hg' : rotE g ∈ (edgesFrom S (X.map Unit4.mulI)).map rotE := List.mem_map.2 ⟨g, hg, rfl⟩
  rw [hwalk] at hg'
  obtain ⟨e1, he1, hrg⟩ := List.mem_map.1 hg'
  obtain ⟨e2, he2, hre⟩ := List.mem_map.1 he1
  have hf : transE a (halfE z e2) ∈ (CellTile.boundaryEdges (cellTileOf Q)).image (transE a) :=
    Finset.mem_image.2 ⟨halfE z e2, hsym e2 (hX e2 he2), rfl⟩
  rw [← hbridge] at hf
  obtain ⟨h, hh, hhg⟩ := Finset.mem_image.1 hf
  have hrg' : transE a (halfE z e2) = rotE g := by
    rw [hre]
    exact hrg
  have hhg' : rotE h = rotE g := by
    rw [hhg, ← hrg']
  have := rotE_injective hhg'
  rw [← this]
  exact hh

/-- The bottom walk of the swapped even tile gives the right edge of the odd tile. -/
theorem lattice_odd (w : Word) :
    rotI (F2Word.sum (oddBottom w)) =
      tF ((parentsAt w).current .odd) + (F2Word.sum (evenBottom (swapW w)) + F2Word.sum (evenRight (swapW w))) := by
  have hE := sum_even_identity (swapW w)
  rw [swapW_swapW] at hE
  rw [hE, (current_swap w).1]
  have hV := parentsAt_valid w
  have ho := hV.odd_parity
  have he := hV.even_parity
  unfold Fraction.Odd at ho
  unfold Fraction.Even at he
  have hodd : ((parentsAt w).current .odd).Odd := by
    unfold Fraction.Odd
    simp only [Parents.current, Parents.combine]
    omega
  have hS1 : F2Word.sum (oddBottom w) = texV1Odd (fracOdd w) - gI := by
    have h := sum_oddBottom w
    unfold almostV₁ at h
    exact eq_sub_of_add_eq h
  rw [hS1, rotate_eq_of_odd hodd]
  simp only [fracOdd]
  ext <;> simp [texV1Odd, tF, tV, mulI, gI, rotI] <;> omega

/-- The bottom walk of the swapped odd tile gives the right edge of the even tile. -/
theorem lattice_even (w : Word) :
    rotI (F2Word.sum (evenBottom w)) =
      tF ((parentsAt w).current .even) + (F2Word.sum (oddBottom (swapW w)) + F2Word.sum (oddRight (swapW w))) := by
  have hO := sum_odd_identity (swapW w)
  rw [swapW_swapW] at hO
  rw [hO, (current_swap w).2]
  have hV := parentsAt_valid w
  have ho := hV.odd_parity
  have he := hV.even_parity
  unfold Fraction.Odd at ho
  unfold Fraction.Even at he
  have heven : ((parentsAt w).current .even).Even := by
    unfold Fraction.Even
    simp only [Parents.current, Parents.combine]
    omega
  have hS1 : F2Word.sum (evenBottom w) = texV1Even (fracEven w) - gI := by
    have h := sum_evenBottom w
    unfold almostV₁ at h
    exact eq_sub_of_add_eq h
  unfold Fraction.Even at heven
  rw [hS1, rotate_eq_of_even (show ((parentsAt w).current .even).Even from heven)]
  simp only [fracEven]
  ext <;> simp [texV1Even, tF, tV, mulI, gI, rotI] <;> omega

/-- The right edge of the odd tile of `w`: the turned bottom walk of the even tile of the swapped word. -/
theorem right_sub_odd (w : Word)
    (hX : ∀ e ∈ edgesFrom 0 (evenBottom (swapW w)), e ∈ CellTile.boundaryEdges (cellTileOf (evenTile (swapW w)))) :
    ∀ g ∈ edgesFrom (F2Word.sum (oddBottom w)) (oddRight w), g ∈ CellTile.boundaryEdges (cellTileOf (oddTile w)) :=
  right_sub_general (oddTile w) (evenTile (swapW w)) (tF ((parentsAt w).current .odd))
    (F2Word.sum (evenBottom (swapW w)) + F2Word.sum (evenRight (swapW w))) (F2Word.sum (oddBottom w))
    (evenBottom (swapW w)) (rot_standard_tiles w).1
    (by rw [lattice_odd w, add_comm]) hX (symm_even (swapW w))

/-- The right edge of the even tile of `w`: the turned bottom walk of the odd tile of the swapped word. -/
theorem right_sub_even (w : Word)
    (hX : ∀ e ∈ edgesFrom 0 (oddBottom (swapW w)), e ∈ CellTile.boundaryEdges (cellTileOf (oddTile (swapW w)))) :
    ∀ g ∈ edgesFrom (F2Word.sum (evenBottom w)) (evenRight w), g ∈ CellTile.boundaryEdges (cellTileOf (evenTile w)) :=
  right_sub_general (evenTile w) (oddTile (swapW w)) (tF ((parentsAt w).current .even))
    (F2Word.sum (oddBottom (swapW w)) + F2Word.sum (oddRight (swapW w))) (F2Word.sum (evenBottom w))
    (oddBottom (swapW w)) (rot_standard_tiles w).2
    (by rw [lattice_even w, add_comm]) hX (symm_odd (swapW w))

end FLatticePaper.Tiles.RightSub
