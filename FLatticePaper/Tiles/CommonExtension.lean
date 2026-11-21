import FLatticePaper.Tiles.PseudoSquare
import FLatticePaper.Tiles.AlmostTilingAssembly
import FLatticePaper.Tiles.BaseCaseAlmostTiling
import FLatticePaper.Tiles.BaseCaseGlobal
import FLatticePaper.Plane.Induction.Periodization

/-! `lemma:common-extension-pseudo-square` (line 1705).

First sentence: a `(w_h, w_v)`-pseudo-square `T` with `(w_1, w_2) = G(w_h, w_v)` satisfying the conditions of
`lemma:almost_square_tiling` generates a `(Σw_1 + i, Σw_2 - 1)`-regular almost tiling. The boundary word comes from the
pseudo-square boundary lemma (`pseudoSquare_boundaryWord`), the regular almost tiling from `almost_square_tiling`.

Final clause: the translation condition `RespectsPeriodsOn` (the `eq:translation_condition` of the paper, on the vertex
set of `T`) extends `o` uniquely to a field with the generator periods, once the vertices of `T` meet every class of the
period lattice; that covering clause is read off the almost tiling. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Farey (Fraction PeriodDeck)
open FLatticePaper.Construction (paperStairTile paperLadderTile)

/-- The first sentence of `lemma:common-extension-pseudo-square`: a pseudo-square with admissible `G`-words satisfying
the two global inputs generates the regular almost tiling `(Σw_1 + i, Σw_2 - 1)`. -/
theorem common_extension_almost {T : CellTile} {wh wv : BinaryWord} (hT : IsPseudoSquare T wh wv)
    (hS : IsSimpleTile T) (hA1 : Admissible (gPseudo wh wv).1)
    (hA2 : Admissible ((gPseudo wh wv).2.map Unit4.mulNegI))
    (hF : NoFirstCrossing T (almostV₁ (gPseudo wh wv).1) (almostV₂ (gPseudo wh wv).2))
    (hG : NoFarAdjacency T (almostV₁ (gPseudo wh wv).1) (almostV₂ (gPseudo wh wv).2)) :
    IsRegularAlmostTiling T (almostV₁ (gPseudo wh wv).1) (almostV₂ (gPseudo wh wv).2) := by
  obtain ⟨c, hc⟩ := pseudoSquare_boundaryWord hT
  exact (almost_square_tiling hS hc hA1 hA2 hF hG).1

/-- The reciprocal stair `stairCells (2k+3)` is a `(stairH k, stairV k)`-pseudo-square at the cell level: its boundary word
is the stair boundary word. -/
theorem gPseudo_fst (wh wv : BinaryWord) : (gPseudo wh wv).1 = gH wh := rfl

theorem gPseudo_snd (wh wv : BinaryWord) : (gPseudo wh wv).2 = gV wv := rfl

theorem stair_isPseudoSquare (k : ℕ) : IsPseudoSquare (stairCells (2 * (k : ℤ) + 3)) (stairH k) (stairV k) := by
  obtain ⟨c, hc⟩ := (stair_base_tile k).1
  exact ⟨⟨c, gH (stairH k), gV (stairV k), hc, (gPseudo_fst _ _).symm, (gPseudo_snd _ _).symm⟩⟩

/-- The first sentence applied to the reciprocal stair `stairCells (2k+3)` with its `G`-words. The words are moved to
`gPseudo` by rewriting, so no definition of `gH` is unfolded during unification. -/
theorem stair_common_extension (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k)))) :
    IsRegularAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))) := by
  have hA1 : Admissible (gPseudo (stairH k) (stairV k)).1 := by
    rw [gPseudo_fst]
    exact (stair_base_tile k).2.1
  have hA2 : Admissible ((gPseudo (stairH k) (stairV k)).2.map Unit4.mulNegI) := by
    rw [gPseudo_snd]
    exact (stair_base_tile k).2.2.1
  have hF' : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3))
      (almostV₁ (gPseudo (stairH k) (stairV k)).1) (almostV₂ (gPseudo (stairH k) (stairV k)).2) := by
    rw [gPseudo_fst, gPseudo_snd]
    exact hF
  have hG' : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3))
      (almostV₁ (gPseudo (stairH k) (stairV k)).1) (almostV₂ (gPseudo (stairH k) (stairV k)).2) := by
    rw [gPseudo_fst, gPseudo_snd]
    exact hG
  have h := common_extension_almost (stair_isPseudoSquare k) (stair_simple k) hA1 hA2 hF' hG'
  rw [gPseudo_fst, gPseudo_snd] at h
  exact h

/-- The period lattice of a fraction is the set of its period-deck combinations: `paperLattice n d` is the modified
deck span of `n/d`. -/
theorem paperLattice_eq_combine (F : Fraction) :
    paperLattice F.num F.den = {v | ∃ i j : ℤ, v = F.modifiedDeck.combine i j} := by
  ext v
  unfold paperLattice
  by_cases hp : (F.num + F.den) % 2 = 0
  · have hmu : F.periodMultiplicity = 1 := if_pos hp
    rw [if_pos hp]
    simp only [latticeOf, Set.mem_setOf_eq, Fraction.modifiedDeck, PeriodDeck.combine, Fraction.unmodifiedDeck,
      hmu, one_mul]
  · have hmu : F.periodMultiplicity = 2 := if_neg hp
    rw [if_neg hp]
    simp only [latticeOf, Set.mem_setOf_eq, Fraction.modifiedDeck, PeriodDeck.combine, Fraction.unmodifiedDeck,
      hmu]

/-- The covering clause: the vertices of an almost tiling meet every class of its period lattice. -/
theorem cover_of_almost (F : Fraction) {T : CellTile} (hT : IsAlmostTiling T (paperLattice F.num F.den)) :
    ∀ z : GInt, ∃ y ∈ (T.vertices : Set GInt), ∃ i j : ℤ, z = y + F.modifiedDeck.combine i j := by
  intro z
  obtain ⟨v, hv, y, hy, hz⟩ := hT.2 z
  rw [paperLattice_eq_combine] at hv
  obtain ⟨i, j, hij⟩ := hv
  refine ⟨z - v, ?_, i, j, ?_⟩
  · have hcorner : z - v ∈ cellCorners y := by
      rw [mem_cellCorners_iff] at hz ⊢
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hz ⊢
      omega
    show z - v ∈ T.vertices
    unfold CellTile.vertices
    rw [Finset.mem_biUnion]
    exact ⟨y, hy, hcorner⟩
  · rw [← hij, sub_add_cancel]

/-- The translation condition extends `o` uniquely to the plane, given that the almost tiling `T` meets every class of the
period lattice (the covering clause) and `o` respects the period law on the vertices of `T`. -/
theorem common_extension_unique (F : Fraction) (hF : F.InUnitInterval) {T : CellTile}
    (hT : IsAlmostTiling T (paperLattice F.num F.den)) {c1 c2 : ℤ} {g : FLatticePaper.Field}
    (hcompat : FLatticePaper.Induction.RespectsPeriodsOn F c1 c2 (T.vertices : Set GInt) g) :
    ∃ field : FLatticePaper.Field, (∀ y ∈ (T.vertices : Set GInt), field y = g y) ∧
      FLatticePaper.HasGeneratorPeriods F field c1 c2 ∧
      ∀ other : FLatticePaper.Field, (∀ y ∈ (T.vertices : Set GInt), other y = g y) →
        FLatticePaper.HasGeneratorPeriods F other c1 c2 → other = field :=
  FLatticePaper.Induction.exists_unique_extension_of_respectsPeriodsOn hF (cover_of_almost F hT) hcompat

/-- The stair family: the translation condition on the reciprocal stair extends uniquely to the plane. -/
theorem stair_common_extension_unique (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k)))) {c1 c2 : ℤ} {g : FLatticePaper.Field}
    (hcompat : FLatticePaper.Induction.RespectsPeriodsOn (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) c1 c2
      ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt) g) :
    ∃ field : FLatticePaper.Field,
      (∀ y ∈ ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt), field y = g y) ∧
      FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) field c1 c2 ∧
      ∀ other : FLatticePaper.Field,
        (∀ y ∈ ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt), other y = g y) →
          FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) other c1 c2 → other = field :=
  common_extension_unique (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)
    (by unfold Fraction.InUnitInterval; dsimp only; omega) (stair_almost_tiling_paper k hF hG) hcompat

/-! ### The two readings of the base tiles, for every `k` and `m` -/

/-- The reciprocal ladder `ladderCells (2m+4)` is a `(ladderH (m+1), ladderV (m+1))`-pseudo-square at the cell level,
its trace being the ladder boundary word. -/
theorem ladder_isPseudoSquare (m : ℕ) :
    IsPseudoSquare (ladderCells (2 * (m : ℤ) + 4)) (ladderH (m + 1)) (ladderV (m + 1)) := by
  obtain ⟨c, hc⟩ := (ladder_base_tile m).1
  exact ⟨⟨c, gH (ladderH (m + 1)), gV (ladderV (m + 1)), hc, (gPseudo_fst _ _).symm, (gPseudo_snd _ _).symm⟩⟩

/-- The vertex-level reading of the reciprocal stair: the walk placement holds on the vertex set of `stairCells (2k+3)`,
for every `k`. -/
theorem stair_isPseudoSquareAlongT_vertices (k : ℕ) :
    IsPseudoSquareAlongT ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt) (stairH k) (stairV k) := by
  have hset : ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt) = paperStairTile (2 * (k : ℤ) + 3) := by
    ext x
    exact mem_stairVertices (2 * (k : ℤ) + 3) (by omega) x
  rw [hset]
  exact stair_isPseudoSquareAlongT k

/-- The vertex-level reading of the reciprocal ladder: the walk placement holds on the vertex set of
`ladderCells (2m+4)`, for every `m`. -/
theorem ladder_isPseudoSquareAlongT_vertices (m : ℕ) :
    IsPseudoSquareAlongT ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt) (ladderH (m + 1)) (ladderV (m + 1)) := by
  have hset : ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt) = paperLadderTile (2 * (m : ℤ) + 4) := by
    ext x
    exact mem_ladderVertices (2 * (m : ℤ) + 4) (by omega) x
  rw [hset]
  have h := ladder_isPseudoSquareAlongT (m + 1) (by omega)
  have hd : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [hd] at h
  exact h

/-- Agreement of the two readings on the reciprocal stair `stairCells (2k+3)`, for every `k`: the cell-level
`IsPseudoSquare` and the vertex-level `IsPseudoSquareAlongT` on the vertex set of the same cell tile hold together. Both
sides are established from independent data (the stair boundary word and the walk placement), so this is agreement of
truth values for the base tile, not an implication for general tiles. -/
theorem stair_readings_agree (k : ℕ) :
    IsPseudoSquare (stairCells (2 * (k : ℤ) + 3)) (stairH k) (stairV k) ↔
      IsPseudoSquareAlongT ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt) (stairH k) (stairV k) :=
  ⟨fun _ => stair_isPseudoSquareAlongT_vertices k, fun _ => stair_isPseudoSquare k⟩

/-- Agreement of the two readings on the reciprocal ladder `ladderCells (2m+4)`, for every `m`. -/
theorem ladder_readings_agree (m : ℕ) :
    IsPseudoSquare (ladderCells (2 * (m : ℤ) + 4)) (ladderH (m + 1)) (ladderV (m + 1)) ↔
      IsPseudoSquareAlongT ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt) (ladderH (m + 1)) (ladderV (m + 1)) :=
  ⟨fun _ => ladder_isPseudoSquareAlongT_vertices m, fun _ => ladder_isPseudoSquare m⟩

/-- The first sentence for the ladder base tiles: the cell-level pseudo-square with admissible `G`-words and the two
global inputs gives the regular almost tiling `(Σw_1 + i, Σw_2 - 1)`. -/
theorem ladder_common_extension (m : ℕ)
    (hF : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1)))))
    (hG : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1))))) :
    IsRegularAlmostTiling (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1)))) := by
  have hA1 : Admissible (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).1 := by
    rw [gPseudo_fst]
    exact (ladder_base_tile m).2.1
  have hA2 : Admissible ((gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2.map Unit4.mulNegI) := by
    rw [gPseudo_snd]
    exact (ladder_base_tile m).2.2.1
  have hF' : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).1)
      (almostV₂ (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2) := by
    rw [gPseudo_fst, gPseudo_snd]
    exact hF
  have hG' : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).1)
      (almostV₂ (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2) := by
    rw [gPseudo_fst, gPseudo_snd]
    exact hG
  have h := common_extension_almost (ladder_isPseudoSquare m) (ladder_simple m) hA1 hA2 hF' hG'
  rw [gPseudo_fst, gPseudo_snd] at h
  exact h

/-- The first sentence for every reciprocal stair base tile `stairCells (2k+3)`, with no global hypothesis. -/
theorem stair_first_sentence_all (k : ℕ) :
    IsRegularAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))) :=
  stair_common_extension k (stair_global k).1 (stair_global k).2

/-- The first sentence for every reciprocal ladder base tile `ladderCells (2m+4)`, with no global hypothesis. -/
theorem ladder_first_sentence_all (m : ℕ) :
    IsRegularAlmostTiling (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1)))) :=
  ladder_common_extension m (ladder_global m).1 (ladder_global m).2

/-- The translation condition on the reciprocal stair extends uniquely to the plane, for every `k`. -/
theorem stair_common_extension_unique_all (k : ℕ) {c1 c2 : ℤ} {g : FLatticePaper.Field}
    (hcompat : FLatticePaper.Induction.RespectsPeriodsOn (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) c1 c2
      ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt) g) :
    ∃ field : FLatticePaper.Field,
      (∀ y ∈ ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt), field y = g y) ∧
      FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) field c1 c2 ∧
      ∀ other : FLatticePaper.Field,
        (∀ y ∈ ((stairCells (2 * (k : ℤ) + 3)).vertices : Set GInt), other y = g y) →
          FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) other c1 c2 → other = field :=
  stair_common_extension_unique k (stair_global k).1 (stair_global k).2 hcompat

/-- The translation condition on the reciprocal ladder extends uniquely to the plane, for every `m`. -/
theorem ladder_common_extension_unique_all (m : ℕ) {c1 c2 : ℤ} {g : FLatticePaper.Field}
    (hcompat : FLatticePaper.Induction.RespectsPeriodsOn (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) c1 c2
      ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt) g) :
    ∃ field : FLatticePaper.Field,
      (∀ y ∈ ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt), field y = g y) ∧
      FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) field c1 c2 ∧
      ∀ other : FLatticePaper.Field,
        (∀ y ∈ ((ladderCells (2 * (m : ℤ) + 4)).vertices : Set GInt), other y = g y) →
          FLatticePaper.HasGeneratorPeriods (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) other c1 c2 → other = field :=
  common_extension_unique (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction)
    (by unfold Fraction.InUnitInterval; dsimp only; omega) (ladder_almost_tiling_paper_all m) hcompat

end FLatticePaper.Tiles
