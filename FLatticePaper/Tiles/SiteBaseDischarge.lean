import FLatticePaper.Tiles.SiteBase
import FLatticePaper.Tiles.SiteMaskStair
import FLatticePaper.Tiles.SiteMaskLadder
import FLatticePaper.Tiles.SiteMaskNear3
import FLatticePaper.Tiles.SiteMaskNear4
import FLatticePaper.Tiles.SiteCovers
import FLatticePaper.Tiles.SiteCoversNear

/-! Task 53, item 1: `baseEq` and `baseCov` of `SiteInduction.SourceHyps` for every base word, unconditionally.

The four pure masks are `H_X` (`stair_eq` for `stairF`, `ladder_eq` for `ladderF`, `nstair_eq3` for `nstairN`, `nladder_eq4` for
`nladderN`), and the four quotient covers of the `H` sets are `cover_stair`, `cover_ladder`, `cover_nstair3` and
`cover_nladder_of` applied to these identities. -/

namespace FLatticePaper.Tiles.SiteBaseDischarge

open FLatticePaper.Tiles.SiteBase FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair
open FLatticePaper.Tiles.SiteMaskLadder FLatticePaper.Tiles.SiteMaskNear3 FLatticePaper.Tiles.SiteMaskNear4
open FLatticePaper.Tiles.SiteCovers FLatticePaper.Tiles.SiteCoversNear FLatticePaper.Tiles.Standard

/-- The four pure masks, proved. -/
theorem maskHyps_all : MaskHyps where
  stair := fun k => stair_eq k
  ladder := fun k hk => ladder_eq k hk
  nstair := fun k => nstair_eq3 (k : ℤ) (by positivity)
  nladder := fun k hk => nladder_eq4 (k : ℤ) (by exact_mod_cast hk)

/-- The four quotient covers, proved. -/
theorem coverHyps_all : CoverHyps where
  stair := fun k => cover_stair k
  ladder := fun k hk => cover_ladder k hk
  nstair := fun k => cover_nstair3 (k : ℤ) (by positivity)
  nladder := fun k hk => cover_nladder_of (k : ℤ) (by exact_mod_cast hk) (nladder_eq4 (k : ℤ) (by exact_mod_cast hk))

/-- `baseEq` of `SiteInduction.SourceHyps` for every base word. -/
theorem baseEq_all (w : FLatticePaper.Farey.Word) (hb : IsBase w) :
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) ∧
      ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) :=
  baseEq_of_masks maskHyps_all w hb

/-- `baseCov` of `SiteInduction.SourceHyps` for every base word. -/
theorem baseCov_all (w : FLatticePaper.Farey.Word) (hb : IsBase w) :
    QuotientCover (HSet (curO w)) (perU (curO w)) (perV (curO w)) ∧
      QuotientCover (HSet (curE w)) (perU (curE w)) (perV (curE w)) :=
  baseCov_of_covers coverHyps_all w hb

end FLatticePaper.Tiles.SiteBaseDischarge
