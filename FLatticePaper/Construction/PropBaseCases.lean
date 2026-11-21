import FLatticePaper.Construction.BaseCases
import FLatticePaper.Construction.NearOneBaseCases
import FLatticePaper.Tiles.BaseCaseGlobal
import FLatticePaper.Tiles.NearOneAlmostTiling
import FLatticePaper.Tiles.BaseCasePseudoSquares
import FLatticePaper.Tiles.NearOneRotation

/-! `prop:base_cases` (paper lines 1901-1963), assembled per base family.

Each family is one theorem stating the proved items together:
- (a) the almost pseudo-square tiling under `L'(n/d)` (the cell tile, `IsAlmostTiling`);
- (b) the alternate tile covers every class of `L'(n/d)`;
- (c) `theorem:odometers` at the fraction, with the unique recurrent extensions of the standard and the alternate tile;
- (d) the pseudo-square, by the boundary-walk placement (`IsPseudoSquareAlongT`), or by the rotated placement
  (`IsRotPseudoSquareT`) for the near-one rows.

Item (e), the exact translations of earlier odometers (paper lines 1939-1962), is not stated: its parity obstruction is
recorded in SOURCE-MAP, Root and pure cases row. -/

namespace FLatticePaper.Construction

open Farey
open FLatticePaper.Tiles (stairCells ladderCells paperLattice IsAlmostTiling)
open FLatticePaper.Tiles.NearTurn (cellTurn)

/-- A unique recurrent extension of a reciprocal base tile: the shape of `staircase_recurrent`. -/
def UniqueRecurrentExtension (F : Fraction) (T : Set Site) (value : Site → ℤ) : Prop :=
  ∃ constantU constantV : ℤ, ∃ field : Field,
    (∀ x ∈ T, field x = value x) ∧ HasGeneratorPeriods F field constantU constantV ∧
      Superharmonic field ∧ Recurrent field ∧
      ∀ other : Field, (∀ x ∈ T, other x = value x) →
        HasGeneratorPeriods F other constantU constantV → other = field

/-- A unique recurrent extension of a near-one base tile in the TeX chart: the shape of `near_staircase_base`, with
superharmonicity and recurrence for the physical translate `z ↦ field (z - (0,1))`. -/
def UniqueNearOneExtension (F : Fraction) (T : Set Site) (value : Site → ℤ) : Prop :=
  ∃ constantU constantV : ℤ, ∃ field : Field,
    (∀ x ∈ T, field x = value x) ∧ HasGeneratorPeriods F field constantU constantV ∧
      (∀ other : Field, (∀ x ∈ T, other x = value x) →
        HasGeneratorPeriods F other constantU constantV → other = field) ∧
      Superharmonic (fun z => field (z - (0, 1))) ∧ Recurrent (fun z => field (z - (0, 1)))

/-- The rotated fraction of the near-one stair `d = 2k+3` is `(k+1)/(k+2)`. -/
theorem rotate_stair_fraction (k : ℕ) :
    Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) = ⟨(k : ℤ) + 1, (k : ℤ) + 2⟩ := by
  have h : Fraction.Even (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction) := by
    unfold Fraction.Even
    dsimp only
    omega
  rw [Fraction.rotate_of_even h]
  ext <;> dsimp only <;> omega

/-- The rotated fraction of the near-one ladder `d = 2m+4` is `(2m+3)/(2m+5)`. -/
theorem rotate_ladder_fraction (m : ℕ) :
    Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) = ⟨2 * (m : ℤ) + 3, 2 * (m : ℤ) + 5⟩ := by
  have h : Fraction.Odd (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction) := by
    unfold Fraction.Odd
    dsimp only
    omega
  rw [Fraction.rotate_of_odd h]
  ext <;> dsimp only <;> omega

set_option maxHeartbeats 400000 in
/-- The alternate cover of the near-one stair: the TeX alternate tile covers every class of `L'(R(1/d))`. It is the
centred-chart cover `stairOddAlt_cover`, placed at the chart point `(0,1)` and read through the tile. -/
theorem near_alt_stair_cover {d : ℤ} (hd : 3 ≤ d ∧ d % 2 = 1) :
    ∀ z : Site, ∃ y ∈ paperNearStairAltTile d, ∃ i j : ℤ,
      z = y + (Fraction.rotate ⟨1, d⟩).modifiedDeck.combine i j := by
  have hden : BaseMask.stairOddAlt.Valid d := hd
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.stairOddAlt.raw d).sites :=
    BaseMask.mem_stairOddAlt_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.stairOddAlt.raw d).sites ↔ x ∈ paperNearStairAltTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_stairOddAlt_raw_direct]
    simp only [paperNearStairAltTile, paperNearStairAltA, paperNearStairAltB, paperNearStairAltC,
      paperNearStairAltD, Set.mem_union, Set.mem_setOf_eq]
    constructor <;> intro h <;> omega
  have hcover : (Fraction.rotate ⟨1, d⟩).modifiedDeck.Covers (BaseMask.stairOddAlt.raw d).sites :=
    covers_of_place (-(BaseMask.stairOddAlt.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0 (stairOddAlt_cover hden)
  intro z
  obtain ⟨y, hy, hspan⟩ := hcover z
  obtain ⟨i, j, hij⟩ := hspan
  exact ⟨y, (hmem y).mp hy, i, j, by rw [← hij]; abel⟩

set_option maxHeartbeats 400000 in
/-- The alternate cover of the near-one doubled staircase: the TeX alternate tile covers every class of `L'(R(1/d))`. -/
theorem near_alt_ladder_cover {d : ℤ} (hd : 4 ≤ d ∧ d % 2 = 0) :
    ∀ z : Site, ∃ y ∈ paperNearLadderAltTile d, ∃ i j : ℤ,
      z = y + (Fraction.rotate ⟨1, d⟩).modifiedDeck.combine i j := by
  have hden : BaseMask.ladderEvenAlt.Valid d := hd
  have hpt : ((0 : ℤ), (1 : ℤ)) ∈ (BaseMask.ladderEvenAlt.raw d).sites :=
    BaseMask.mem_ladderEvenAlt_raw_direct.mpr (by dsimp only; omega)
  have hmem : ∀ x, x ∈ (BaseMask.ladderEvenAlt.raw d).sites ↔ x ∈ paperNearLadderAltTile d := by
    intro x
    obtain ⟨a, b⟩ := x
    rw [BaseMask.mem_ladderEvenAlt_raw_direct]
    simp only [paperNearLadderAltTile, paperNearLadderAltA, paperNearLadderAltB, paperNearLadderAltC,
      paperNearLadderAltD, Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    constructor <;> intro h <;> omega
  have hcover : (Fraction.rotate ⟨1, d⟩).modifiedDeck.Covers (BaseMask.ladderEvenAlt.raw d).sites :=
    covers_of_place (-(BaseMask.ladderEvenAlt.raw d).boxOrigin ⟨(0, 1), hpt⟩) 0 (ladderEvenAlt_cover hden)
  intro z
  obtain ⟨y, hy, hspan⟩ := hcover z
  obtain ⟨i, j, hij⟩ := hspan
  exact ⟨y, (hmem y).mp hy, i, j, by rw [← hij]; abel⟩

/-- `prop:base_cases` for the reciprocal staircase `d = 2k+3` (the `3^k` even row), for every `k`. -/
theorem prop_base_cases_reciprocal_stair (k : ℕ) :
    IsAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (paperLattice 1 (2 * (k : ℤ) + 3)) ∧
      (∀ z : Site, ∃ y ∈ paperStairAltTile (2 * (k : ℤ) + 3), ∃ i j : ℤ,
        z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) ∧
      (OdometersTheoremAt (Fraction.mk 1 (2 * (k : ℤ) + 3)) ∧
        UniqueRecurrentExtension (Fraction.mk 1 (2 * (k : ℤ) + 3)) (paperStairTile (2 * (k : ℤ) + 3))
          (paperStairValue (2 * (k : ℤ) + 3)) ∧
        UniqueRecurrentExtension (Fraction.mk 1 (2 * (k : ℤ) + 3)) (paperStairAltTile (2 * (k : ℤ) + 3))
          (paperStairAltValue (2 * (k : ℤ) + 3))) ∧
      FLatticePaper.Tiles.IsPseudoSquareAlongT (paperStairTile (2 * (k : ℤ) + 3)) (FLatticePaper.Tiles.stairH k)
        (FLatticePaper.Tiles.stairV k) :=
  ⟨FLatticePaper.Tiles.stair_almost_tiling_paper_all k,
    prop_base_cases_alternate_cover_odd ⟨by omega, by omega⟩,
    ⟨(odometersTheoremAt_base (d := 2 * (k : ℤ) + 3) (by omega)).1,
      staircase_recurrent ⟨by omega, by omega⟩, alt_staircase_recurrent ⟨by omega, by omega⟩⟩,
    FLatticePaper.Tiles.stair_isPseudoSquareAlongT k⟩

/-- `prop:base_cases` for the doubled staircase `d = 2m+4` (the `3^k` odd row, `k = m+1`), for every `m`. -/
theorem prop_base_cases_doubled_stair (m : ℕ) :
    IsAlmostTiling (ladderCells (2 * (m : ℤ) + 4)) (paperLattice 1 (2 * (m : ℤ) + 4)) ∧
      (∀ z : Site, ∃ y ∈ paperLadderAltTile (2 * (m : ℤ) + 4), ∃ i j : ℤ,
        z = y + (Fraction.mk 1 (2 * (m : ℤ) + 4)).modifiedDeck.combine i j) ∧
      (OdometersTheoremAt (Fraction.mk 1 (2 * (m : ℤ) + 4)) ∧
        UniqueRecurrentExtension (Fraction.mk 1 (2 * (m : ℤ) + 4)) (paperLadderTile (2 * (m : ℤ) + 4))
          (paperLadderValue (2 * (m : ℤ) + 4)) ∧
        UniqueRecurrentExtension (Fraction.mk 1 (2 * (m : ℤ) + 4)) (paperLadderAltTile (2 * (m : ℤ) + 4))
          (paperLadderAltValue (2 * (m : ℤ) + 4))) ∧
      FLatticePaper.Tiles.IsPseudoSquareAlongT (paperLadderTile (2 * (m : ℤ) + 4))
        (FLatticePaper.Tiles.ladderH (m + 1)) (FLatticePaper.Tiles.ladderV (m + 1)) := by
  refine ⟨FLatticePaper.Tiles.ladder_almost_tiling_paper_all m,
    prop_base_cases_alternate_cover_even ⟨by omega, by omega⟩,
    ⟨(odometersTheoremAt_base (d := 2 * (m : ℤ) + 4) (by omega)).1,
      doubled_staircase_recurrent ⟨by omega, by omega⟩, doubled_alt_staircase_recurrent ⟨by omega, by omega⟩⟩,
    ?_⟩
  have h := FLatticePaper.Tiles.ladder_isPseudoSquareAlongT (m + 1) (by omega)
  have hd : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
  rw [hd] at h
  exact h

/-- `prop:base_cases` for the near-one stair `d = 2k+3` (the `2^k` odd row, rotated fraction `R(1/d)`), for every `k`. -/
theorem prop_base_cases_near_stair (k : ℕ) :
    IsAlmostTiling
        (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2)
          (stairCells (2 * (k : ℤ) + 3)))
        (paperLattice (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)).num
          (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)).den) ∧
      (∀ z : Site, ∃ y ∈ paperNearStairAltTile (2 * (k : ℤ) + 3), ∃ i j : ℤ,
        z = y + (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)).modifiedDeck.combine i j) ∧
      (OdometersTheoremAt (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction)) ∧
        UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction))
          (paperNearStairTile (2 * (k : ℤ) + 3)) (paperNearStairValue (2 * (k : ℤ) + 3)) ∧
        UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction))
          (paperNearStairAltTile (2 * (k : ℤ) + 3)) (paperNearStairAltValue (2 * (k : ℤ) + 3))) ∧
      FLatticePaper.Tiles.IsRotPseudoSquareT
        (FLatticePaper.Tiles.chartDown (paperNearStairTile (2 * (k : ℤ) + 3)))
        (FLatticePaper.Tiles.nearStairH k) (FLatticePaper.Tiles.nearStairV k) := by
  refine ⟨?_, near_alt_stair_cover ⟨by omega, by omega⟩, ⟨?_, ?_, ?_⟩,
    FLatticePaper.Tiles.nearStair_isRotPseudoSquareT k⟩
  · rw [rotate_stair_fraction]
    exact FLatticePaper.Tiles.NearTurn.nearStair_almost_all k
  · exact (odometersTheoremAt_base (d := 2 * (k : ℤ) + 3) (by omega)).2
  · exact near_staircase_base ⟨by omega, by omega⟩
  · exact near_alt_staircase_base ⟨by omega, by omega⟩

/-- `prop:base_cases` for the near-one doubled staircase `d = 2m+4` (the `2^k` even row, rotated fraction `R(1/d)`),
for every `m`. -/
theorem prop_base_cases_near_doubled_stair (m : ℕ) :
    IsAlmostTiling
        (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2)
          (ladderCells (2 * (m : ℤ) + 4)))
        (paperLattice (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction)).num
          (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction)).den) ∧
      (∀ z : Site, ∃ y ∈ paperNearLadderAltTile (2 * (m : ℤ) + 4), ∃ i j : ℤ,
        z = y + (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction)).modifiedDeck.combine i j) ∧
      (OdometersTheoremAt (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction)) ∧
        UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction))
          (paperNearLadderTile (2 * (m : ℤ) + 4)) (paperNearLadderValue (2 * (m : ℤ) + 4)) ∧
        UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction))
          (paperNearLadderAltTile (2 * (m : ℤ) + 4)) (paperNearLadderAltValue (2 * (m : ℤ) + 4))) ∧
      FLatticePaper.Tiles.IsRotPseudoSquareT
        (FLatticePaper.Tiles.chartDown (paperNearLadderTile (2 * (m : ℤ) + 4)))
        (FLatticePaper.Tiles.nearLadderH (m + 1)) (FLatticePaper.Tiles.nearLadderV (m + 1)) := by
  refine ⟨?_, near_alt_ladder_cover ⟨by omega, by omega⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [rotate_ladder_fraction]
    exact FLatticePaper.Tiles.NearTurn.nearLadder_almost_all m
  · exact (odometersTheoremAt_base (d := 2 * (m : ℤ) + 4) (by omega)).2
  · exact near_doubled_staircase_base ⟨by omega, by omega⟩
  · exact near_doubled_alt_staircase_base ⟨by omega, by omega⟩
  · have h := FLatticePaper.Tiles.nearLadder_isRotPseudoSquareT (m + 1) (by omega)
    have hd : (2 * ((m + 1 : ℕ) : ℤ) + 2) = 2 * (m : ℤ) + 4 := by push_cast; ring
    rw [hd] at h
    exact h

end FLatticePaper.Construction
