import FLatticePaper.Tiles.SiteMaskNear3
import FLatticePaper.Construction.StaircaseCoverage
import FLatticePaper.Tiles.SiteCovers

/-! Task 53, item 1: the cover of the near-one odd staircase `CV3`.

The repository's `stairOdd_cover` covers the trimmed tile of `stairOdd` by the rotated deck `(Fraction.mk 1 d).rotate`. Here the
raw odd staircase is the quarter turn of the raw even staircase (`BaseMask.mem_stairOdd_raw_iff`), which is `nstairF d` in
coordinates; the tile is a translate of the raw sites (`mem_place_sites`); and a cover is invariant under translation. -/

namespace FLatticePaper.Tiles.SiteCoversNear

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair FLatticePaper.Tiles.SiteMaskNear3
open FLatticePaper.Tiles.SiteCovers

/-- A cover of a finite set `T` by a deck covers every finite set `S` whose translate `S + u` is `T`. -/
theorem covers_of_mem_shift {deck : PeriodDeck} {T S : Finset Site} (h : deck.Covers T) (u : Site)
    (hS : ∀ z, z ∈ S ↔ z + u ∈ T) : deck.Covers S := by
  intro z
  obtain ⟨r, hr, hspan⟩ := h (z + u)
  refine ⟨r - u, (hS (r - u)).2 (by rw [sub_add_cancel]; exact hr), ?_⟩
  have e : z - (r - u) = z + u - r := by abel
  rw [e]
  exact hspan

/-- The raw odd staircase is `nstairF d`: its sites are the quarter turn of the raw even staircase. -/
theorem stairOdd_raw_mem (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) :
    (x, y) ∈ (BaseMask.stairOdd.raw d).sites ↔ (x, y) ∈ nstairF d := by
  have h := BaseMask.mem_stairOdd_raw_iff (den := d) (y - d + 1, d + 1 - x)
  have e : QuarterTurn.counterclockwise.mapSite (d + 1, d - 1) (y - d + 1, d + 1 - x) = (x, y) := by
    simp only [QuarterTurn.mapSite, QuarterTurn.turn, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  rw [e] at h
  rw [h, BaseMask.mem_stairEven_raw_iff, mem_nstairF (by omega : (2 : ℤ) ≤ d)]
  simp only [BaseMask.StairEvenCorner]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- The sites of the tile of `stairOdd` are the raw sites translated by a fixed vector (the box origin). -/
theorem stairOdd_tile_mem (d : ℤ) (hden : BaseMask.stairOdd.Valid d) (hd : 3 ≤ d) (hdo : d % 2 = 1) :
    ∃ w : Site, ∀ z : Site, z ∈ (BaseMask.stairOdd.tile d hden).sites ↔ z + w ∈ (BaseMask.stairOdd.raw d).sites := by
  have hmem : (0, d + 1) ∈ nstairF d := by
    rw [mem_nstairF (by omega : (2 : ℤ) ≤ d)]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have hne : (BaseMask.stairOdd.raw d).sites.Nonempty :=
    ⟨(0, d + 1), (stairOdd_raw_mem d 0 (d + 1) hd hdo).2 hmem⟩
  refine ⟨(BaseMask.stairOdd.raw d).boxOrigin hne, fun z => ?_⟩
  unfold BaseMask.tile HeightTile.trim
  rw [HeightTile.mem_place_sites, sub_neg_eq_add]

/-- `CV3`: the near-one odd staircase covers its `H` set, with the periods of `⟨k + 1, k + 2⟩`. -/
theorem cover_nstair3 (k : ℤ) (hk : 0 ≤ k) :
    QuotientCover (HSet ⟨k + 1, k + 2⟩) (perU ⟨k + 1, k + 2⟩) (perV ⟨k + 1, k + 2⟩) := by
  rw [← nstair_eq3 k hk]
  have hden : BaseMask.stairOdd.Valid (2 * k + 3) :=
    (show 3 ≤ 2 * k + 3 ∧ (2 * k + 3) % 2 = 1 from ⟨by omega, by omega⟩)
  have hcov := stairOdd_cover hden
  have hrot : (Fraction.mk 1 (2 * k + 3)).rotate = ⟨k + 1, k + 2⟩ := by
    rw [rotate_eq_of_even (show (Fraction.mk 1 (2 * k + 3)).Even from by
      show (1 + (2 * k + 3)) % 2 = 0
      omega)]
    show (⟨((2 * k + 3) - 1) / 2, ((2 * k + 3) + 1) / 2⟩ : Fraction) = ⟨k + 1, k + 2⟩
    simp only [Fraction.mk.injEq]
    omega
  rw [hrot] at hcov
  obtain ⟨w, hw⟩ := stairOdd_tile_mem (2 * k + 3) hden (by omega) (by omega)
  apply quotientCover_of_covers ⟨k + 1, k + 2⟩ _
  refine covers_of_mem_shift hcov ((0, 1) - w) ?_
  intro z
  rw [hw]
  have e : z + ((0, 1) - w) + w = (z.1, z.2 + 1) := by
    exact Prod.ext (by simp only [Prod.fst_add, Prod.fst_sub]; omega) (by simp only [Prod.snd_add, Prod.snd_sub]; omega)
  rw [e, stairOdd_raw_mem (2 * k + 3) z.1 (z.2 + 1) (by omega) (by omega), ← mem_nstairN_iff]

/-- The raw even ladder is the set `nladderF`: the quarter turn of the raw odd ladder. -/
theorem ladderEven_raw_mem (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) :
    (x, y) ∈ (BaseMask.ladderEven.raw d).sites ↔ (x, y) ∈ nladderF d := by
  have h := BaseMask.mem_ladderEven_raw_iff (den := d) (y - d + 1, d + 1 - x)
  have e : QuarterTurn.counterclockwise.mapSite (d + 1, d - 1) (y - d + 1, d + 1 - x) = (x, y) := by
    simp only [QuarterTurn.mapSite, QuarterTurn.turn, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  rw [e] at h
  rw [h, BaseMask.mem_ladderOdd_raw_iff, mem_nladderF (by omega : (2 : ℤ) ≤ d)]
  simp only [BaseMask.LadderOddCorner]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- A site is in `nladderN d` when the site shifted by `(0, 1)` is in `nladderF d`. -/
theorem mem_nladderN_iff (d x y : ℤ) : (x, y) ∈ nladderN d ↔ (x, y + 1) ∈ nladderF d := by
  unfold nladderN shift
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have ha : a = x := by linarith
    have hb : b = y + 1 := by linarith
    subst ha
    subst hb
    exact hab
  · intro h
    exact ⟨(x, y + 1), h, Prod.ext (by simp) (by simp)⟩

/-- The sites of the tile of `ladderEven` are the raw sites translated by a fixed vector. -/
theorem ladderEven_tile_mem (d : ℤ) (hden : BaseMask.ladderEven.Valid d) (hd : 4 ≤ d) (hde : d % 2 = 0) :
    ∃ w : Site, ∀ z : Site, z ∈ (BaseMask.ladderEven.tile d hden).sites ↔ z + w ∈ (BaseMask.ladderEven.raw d).sites := by
  have hmem : (-1, 2 * d + 1) ∈ nladderF d := by
    rw [mem_nladderF (by omega : (2 : ℤ) ≤ d)]
    refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
    omega
  have hne : (BaseMask.ladderEven.raw d).sites.Nonempty :=
    ⟨(-1, 2 * d + 1), (ladderEven_raw_mem d (-1) (2 * d + 1) hd hde).2 hmem⟩
  refine ⟨(BaseMask.ladderEven.raw d).boxOrigin hne, fun z => ?_⟩
  unfold BaseMask.tile HeightTile.trim
  rw [HeightTile.mem_place_sites, sub_neg_eq_add]

/-- `CV4`, conditional on the mask identity `M4` (`nladderN (2k + 2) = H_{⟨2k + 1, 2k + 3⟩}`): the near-one even ladder covers
its `H` set. -/
theorem cover_nladder_of (k : ℤ) (hk : 1 ≤ k)
    (hM4 : ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩) :
    QuotientCover (HSet ⟨2 * k + 1, 2 * k + 3⟩) (perU ⟨2 * k + 1, 2 * k + 3⟩) (perV ⟨2 * k + 1, 2 * k + 3⟩) := by
  rw [← hM4]
  have hden : BaseMask.ladderEven.Valid (2 * k + 2) :=
    (show 4 ≤ 2 * k + 2 ∧ (2 * k + 2) % 2 = 0 from ⟨by omega, by omega⟩)
  have hcov := ladderEven_cover hden
  have hrot : (Fraction.mk 1 (2 * k + 2)).rotate = ⟨2 * k + 1, 2 * k + 3⟩ := by
    rw [rotate_eq_of_odd (show (Fraction.mk 1 (2 * k + 2)).Odd from by
      show (1 + (2 * k + 2)) % 2 = 1
      omega)]
    simp only [Fraction.mk.injEq]
    omega
  rw [hrot] at hcov
  obtain ⟨w, hw⟩ := ladderEven_tile_mem (2 * k + 2) hden (by omega) (by omega)
  apply quotientCover_of_covers ⟨2 * k + 1, 2 * k + 3⟩ _
  refine covers_of_mem_shift hcov ((0, 1) - w) ?_
  intro z
  rw [hw]
  have e : z + ((0, 1) - w) + w = (z.1, z.2 + 1) :=
    Prod.ext (by simp only [Prod.fst_add, Prod.fst_sub]; omega) (by simp only [Prod.snd_add, Prod.snd_sub]; omega)
  rw [e, ladderEven_raw_mem (2 * k + 2) z.1 (z.2 + 1) (by omega) (by omega), ← mem_nladderN_iff]

end FLatticePaper.Tiles.SiteCoversNear
