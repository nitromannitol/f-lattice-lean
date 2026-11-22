import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.AlmostTilingCover

/-! # Deck coverage of the standard tiles (task 41)

The covering clause of the almost tiling `IsAlmostTiling T (latticeOf v1 v2)` (every lattice point is a vertex of a cell
of some translate of the cell tile) is proved from the boundary word, the simplicity of the tile and the admissibility of
`w1`, `-i w2` only: `covering_unconditional` is the covering part of `almost_square_tiling`, whose packing inputs
`NoFirstCrossing`, `NoFarAdjacency` only serve the uniqueness and the edge clause. The lattice `latticeOf (texV1Odd f)
(texV2 f)` of the odd tile is the span of the modified deck `f.modifiedDeck` (the kernel is doubled for odd `f`, as in
`eq:modified_lattice`), so a tile whose cell tile covers in this sense meets every class of its modified deck.

The inputs used are those of `StandardInputsNoPack` (the fields of `StandardInputs` of `StandardClauseA` except the
packing fields `packOdd`, `packEven`): `bdOdd`, `bdEven`, `sumOdd`, `sumEven`, `admOdd`, `admEven`, `simpleOdd`,
`simpleEven`. -/

namespace FLatticePaper.Tiles.DeckCoverage

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.StandardClause

/-! ### The covering clause without the packing inputs -/

/-- The covering clause of `almost_square_tiling`: for a simple tile with boundary word `w1 w2 hat(rev w1) hat(rev w2)`
and admissible `w1`, `-i w2`, every lattice point is a vertex of a cell of a translate of the tile, under the lattice of
the almost tiling. The packing inputs are not used. -/
theorem covering_unconditional {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hS : IsSimpleTile T) (hB : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) :
    ∀ x : GInt, ∃ v ∈ latticeOf (almostV₁ w1) (almostV₂ w2), ∃ y ∈ T, x ∈ cellCorners (y + v) := by
  obtain ⟨-, hE⟩ := hS
  have h1 : ∀ x ∈ w1, x = .one ∨ x = .i := hA1.1
  have hmono : ∀ y ∈ w2.map Unit4.mulNegI, y = .one ∨ y = .i := hA2.1
  have h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne := by
    intro x hx
    have hm := hmono x.mulNegI (List.mem_map_of_mem hx)
    have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
    rcases hm with h | h
    · rw [hxe, h]; simp [Unit4.mulI]
    · rw [hxe, h]; simp [Unit4.mulI]
  exact covering_clause_of_succ hB h1 h2 (cntI_w2_pos hA2) (succCover_proved hB hE hA1 hA2)

/-! ### The lattice of a deck -/

/-- The lattice `latticeOf k v` of a period deck is its span. -/
theorem latticeOf_kernel_transverse (deck : PeriodDeck) :
    latticeOf deck.kernel deck.transverse = deck.span := by
  ext v
  constructor
  · rintro ⟨k, k', rfl⟩
    exact ⟨k, k', rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨i, j, rfl⟩

/-- The kernel of the modified deck of an odd fraction is the TeX vector `texV1Odd`, which is doubled. -/
theorem modifiedDeck_kernel_of_odd {f : Fraction} (h : f.Odd) : f.modifiedDeck.kernel = texV1Odd f := by
  have hodd : (f.num + f.den) % 2 = 1 := h
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, hodd, texV1Odd]

/-- The kernel of the modified deck of an even fraction is the TeX vector `texV1Even`. -/
theorem modifiedDeck_kernel_of_even {f : Fraction} (h : f.Even) : f.modifiedDeck.kernel = texV1Even f := by
  have heven : (f.num + f.den) % 2 = 0 := h
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, heven, texV1Even]

/-- The transverse vector of the modified deck is the TeX vector `texV2`. -/
theorem modifiedDeck_transverse (f : Fraction) : f.modifiedDeck.transverse = texV2 f := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck, texV2]

/-- The lattice `L'(n/d)` of the odd tile is the span of the modified deck of `f`. -/
theorem lattice_odd_eq_span {f : Fraction} (h : f.Odd) :
    latticeOf (texV1Odd f) (texV2 f) = f.modifiedDeck.span := by
  rw [← modifiedDeck_kernel_of_odd h, ← modifiedDeck_transverse, latticeOf_kernel_transverse]

/-- The lattice `L'(n/d)` of the even tile is the span of the modified deck of `f`. -/
theorem lattice_even_eq_span {f : Fraction} (h : f.Even) :
    latticeOf (texV1Even f) (texV2 f) = f.modifiedDeck.span := by
  rw [← modifiedDeck_kernel_of_even h, ← modifiedDeck_transverse, latticeOf_kernel_transverse]

/-! ### The named inputs of the coverage -/

/-- The named inputs of the standard tiles' coverage: those of `StandardInputs` (`StandardClauseA`) without the packing
fields `packOdd`, `packEven`. -/
structure StandardInputsNoPack where
  W1 : Word → F2Word
  W2 : Word → F2Word
  V1 : Word → F2Word
  V2 : Word → F2Word
  bdOdd : ∀ w, IsBoundaryWordAt (cellTileOf (oddTile w)) (0, 0) (boundaryWordOf (W1 w) (W2 w))
  bdEven : ∀ w, IsBoundaryWordAt (cellTileOf (evenTile w)) (0, 0) (boundaryWordOf (V1 w) (V2 w))
  sumOdd : ∀ w, almostV₁ (W1 w) = texV1Odd (fracOdd w) ∧ almostV₂ (W2 w) = texV2 (fracOdd w)
  sumEven : ∀ w, almostV₁ (V1 w) = texV1Even (fracEven w) ∧ almostV₂ (V2 w) = texV2 (fracEven w)
  admOdd : ∀ w, Admissible (W1 w) ∧ Admissible ((W2 w).map Unit4.mulNegI)
  admEven : ∀ w, Admissible (V1 w) ∧ Admissible ((V2 w).map Unit4.mulNegI)
  simpleOdd : ∀ w, IsSimpleTile (cellTileOf (oddTile w))
  simpleEven : ∀ w, IsSimpleTile (cellTileOf (evenTile w))

/-- The cell tile of a vertex set has its vertices in the set. -/
theorem corners_subset_of_mem {P : Finset Site} {y : GInt} (hy : y ∈ cellTileOf P) : cellCorners y ⊆ P :=
  (Finset.mem_filter.mp hy).2

/-! ### Coverage of the standard tiles by their modified decks -/

/-- The odd standard tile: its cell tile covers the lattice `L'(f)`, `f = fracOdd w`, and so the tile meets every class of
`f.modifiedDeck`. -/
theorem deck_covers_odd (I : StandardInputsNoPack) (w : Word) : (fracOdd w).modifiedDeck.Covers (oddTile w) := by
  intro x
  have h := covering_unconditional (I.simpleOdd w) (I.bdOdd w) (I.admOdd w).1 (I.admOdd w).2
  rw [(I.sumOdd w).1, (I.sumOdd w).2] at h
  obtain ⟨v, hv, y, hy, hxy⟩ := h x
  have hrep : x - v ∈ oddTile w :=
    corners_subset_of_mem hy ((mem_cellCorners_add_iff x y v).mp hxy)
  refine ⟨x - v, hrep, ?_⟩
  rw [sub_sub_cancel]
  rw [lattice_odd_eq_span (f := fracOdd w) (parentsAt_valid w).current_odd_parity] at hv
  exact hv

/-- The even standard tile: its cell tile covers the lattice `L'(f)`, `f = fracEven w`, and so the tile meets every class
of `f.modifiedDeck`. -/
theorem deck_covers_even (I : StandardInputsNoPack) (w : Word) : (fracEven w).modifiedDeck.Covers (evenTile w) := by
  intro x
  have h := covering_unconditional (I.simpleEven w) (I.bdEven w) (I.admEven w).1 (I.admEven w).2
  rw [(I.sumEven w).1, (I.sumEven w).2] at h
  obtain ⟨v, hv, y, hy, hxy⟩ := h x
  have hrep : x - v ∈ evenTile w :=
    corners_subset_of_mem hy ((mem_cellCorners_add_iff x y v).mp hxy)
  refine ⟨x - v, hrep, ?_⟩
  rw [sub_sub_cancel]
  rw [lattice_even_eq_span (f := fracEven w) (parentsAt_valid w).current_even_parity] at hv
  exact hv

/-- Any site set equal to the odd standard tile covers its modified deck. This is the form in which the constructor's
standard tile enters: wherever the constructor's tile equals `oddTile w` (the ordinary outputs). -/
theorem covers_of_eq_odd (I : StandardInputsNoPack) {P : Finset Site} {w : Word} (h : P = oddTile w) :
    (fracOdd w).modifiedDeck.Covers P := by
  subst h
  exact deck_covers_odd I w

/-- Any site set equal to the even standard tile covers its modified deck. -/
theorem covers_of_eq_even (I : StandardInputsNoPack) {P : Finset Site} {w : Word} (h : P = evenTile w) :
    (fracEven w).modifiedDeck.Covers P := by
  subst h
  exact deck_covers_even I w

end FLatticePaper.Tiles.DeckCoverage
