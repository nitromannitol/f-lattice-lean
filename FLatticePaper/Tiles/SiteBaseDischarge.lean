import FLatticePaper.Tiles.SiteBase
import FLatticePaper.Tiles.SiteMaskStair
import FLatticePaper.Tiles.SiteMaskLadder
import FLatticePaper.Tiles.SiteMaskNear3
import FLatticePaper.Tiles.SiteCovers
import FLatticePaper.Tiles.SiteCoversNear

/-! Task 53, item 1: `baseEq` and `baseCov` of `SiteInduction.SourceHyps` for the base words, with the mask identity `M4` (the near-one
even doubled ladder) as the only remaining hypothesis. `M1` (`stair_eq`), `M2` (`ladder_eq`), `M3` (`nstair_eq3`) and the four covers
`CV1` (`cover_stair`), `CV2` (`cover_ladder`), `CV3` (`cover_nstair3`) are proved; `CV4` (`cover_nladder_of`) is proved from `M4`. -/

namespace FLatticePaper.Tiles.SiteBaseDischarge

open FLatticePaper.Tiles.SiteBase FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair
open FLatticePaper.Tiles.SiteMaskLadder FLatticePaper.Tiles.SiteMaskNear3 FLatticePaper.Tiles.SiteCovers
open FLatticePaper.Tiles.SiteCoversNear FLatticePaper.Tiles.Standard

/-- The four pure masks, from `M4` as the only hypothesis. -/
theorem maskHyps_of_m4
    (m4 : ∀ k : ℤ, 1 ≤ k → ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩) :
    MaskHyps where
  stair := fun k => stair_eq k
  ladder := fun k hk => ladder_eq k hk
  nstair := fun k => nstair_eq3 (k : ℤ) (by positivity)
  nladder := fun k hk => m4 (k : ℤ) (by exact_mod_cast hk)

/-- The four covers, from `M4` as the only hypothesis. -/
theorem coverHyps_of_m4
    (m4 : ∀ k : ℤ, 1 ≤ k → ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩) :
    CoverHyps where
  stair := fun k => cover_stair k
  ladder := fun k hk => cover_ladder k hk
  nstair := fun k => cover_nstair3 (k : ℤ) (by positivity)
  nladder := fun k hk => cover_nladder_of (k : ℤ) (by exact_mod_cast hk) (m4 (k : ℤ) (by exact_mod_cast hk))

/-- `baseEq` of `SiteInduction.SourceHyps` for every base word, from the mask identity `M4`. -/
theorem baseEq_of_m4
    (m4 : ∀ k : ℤ, 1 ≤ k → ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩)
    (w : FLatticePaper.Farey.Word) (hb : IsBase w) :
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) ∧
      ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) :=
  baseEq_of_masks (maskHyps_of_m4 m4) w hb

/-- `baseCov` of `SiteInduction.SourceHyps` for every base word, from the mask identity `M4`. -/
theorem baseCov_of_m4
    (m4 : ∀ k : ℤ, 1 ≤ k → ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩)
    (w : FLatticePaper.Farey.Word) (hb : IsBase w) :
    QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) ∧
      QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w)) :=
  baseCov_of_covers (coverHyps_of_m4 m4) w hb

end FLatticePaper.Tiles.SiteBaseDischarge
