import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.SiteStrings
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.SiteLowLeft
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.HBottom

/-! The horizontal pair of the walk form of H2: the top side of the boundary walk of each standard tile lies in the marked sites
`markedSites`, for both children (`top_marks_odd_all`, `top_marks_even`).

The top side of the walk from `0` is the reflection of the bottom side through the corner `Σw1 + Σw2` (`WalkDecomp.walk_decomp`).
The marked sites contain the half-turn `halfTurn T` of the horizontal string sites. So the top side lies in the marks once:
* the bottom side lies in the horizontal string sites: `HBottom.hB_odd` and `HBottom.hB_even`, proved by telescoping the `gH` walk
  tile by tile (`HBottom.gH_walk_mem`); and
* the corner `Σw1 + Σw2` is the half-turn centre `halfTurnCentre T`: `hP_odd` and `hP_even`, from the sum identities and the centre
  formulas `SiteHullOdd.centre_odd` and `SiteHullEven.centre_even`. -/

namespace FLatticePaper.Tiles.HorizontalPair

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary
open FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.SiteInduction

/-- The top side of the walk from `0` (the reflection of the bottom side through the corner `Σw1 + Σw2`) lies in the marked sites,
given the two inputs. -/
theorem top_marks_of_bottom (T : Finset (ℤ × ℤ)) (wh vw : List Letter) (w1 w2 : F2Word)
    (hc : lowLeft T = (0, 0))
    (hP : F2Word.sum w1 + F2Word.sum w2 = halfTurnCentre T)
    (hB : ∀ s ∈ F2Word.walk 0 w1, s ∈ stringSites false false wh) :
    ∀ p ∈ (F2Word.walk 0 w1).map (fun z => (0 + F2Word.sum w1 + F2Word.sum w2) - z),
      p ∈ markedSites T wh vw := by
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
  have hsS : s ∈ stringSites false false wh := hB s hs
  have hz : (0 : ℤ × ℤ) + F2Word.sum w1 + F2Word.sum w2 = halfTurnCentre T := by
    rw [zero_add]
    exact hP
  have hpt : (0 + F2Word.sum w1 + F2Word.sum w2) - s = halfTurn T s := by
    rw [hz]
    ext <;> simp [halfTurn]
  rw [hpt]
  simp only [markedSites, hc]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  refine List.mem_map.2 ⟨(s.1 + 0, s.2 + 0), List.mem_map.2 ⟨s, hsS, rfl⟩, ?_⟩
  simp

/-- **hP for the odd tile.** The bottom and right words of the odd tile sum to the half-turn centre of the tile: the sums are the
lattice vectors `texV1Odd` and `texV2` shifted by `(0,1)` and `(1,0)` (`sum_oddBottom`, `sum_oddRight`), and the centre is
`centre_odd`. -/
theorem hP_odd (w : Word) :
    F2Word.sum (oddBottom w) + F2Word.sum (oddRight w) = halfTurnCentre (oddTile w) := by
  have h1 := FLatticePaper.Tiles.StandardBoundary.sum_oddBottom w
  have h2 := FLatticePaper.Tiles.StandardBoundary.sum_oddRight w
  rw [FLatticePaper.Tiles.SiteHullOdd.centre_odd w]
  unfold almostV₁ at h1
  unfold almostV₂ at h2
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have e3 := congrArg Prod.fst h2
  have e4 := congrArg Prod.snd h2
  simp only [gI, gOne, texV1Odd, texV2, fracOdd, curO, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3 e4 ⊢
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- **hP for the even tile.** The same identity for the even child: `texV1Even` and `texV2` of the even fraction. -/
theorem hP_even (w : Word) :
    F2Word.sum (evenBottom w) + F2Word.sum (evenRight w) = halfTurnCentre (evenTile w) := by
  have h1 := FLatticePaper.Tiles.StandardBoundary.sum_evenBottom w
  have h2 := FLatticePaper.Tiles.StandardBoundary.sum_evenRight w
  rw [FLatticePaper.Tiles.SiteHullEven.centre_even w]
  unfold almostV₁ at h1
  unfold almostV₂ at h2
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have e3 := congrArg Prod.fst h2
  have e4 := congrArg Prod.snd h2
  simp only [gI, gOne, texV1Even, texV2, fracEven, curE, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3 e4 ⊢
  refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- **The top side of the odd tile lies in the marks**, given the bottom side lies in the horizontal string sites (`hB`, the
remaining input). -/
theorem top_marks_odd (w : Word)
    (hB : ∀ s ∈ F2Word.walk 0 (oddBottom w), s ∈ stringSites false false (hWordOf w false)) :
    ∀ p ∈ (F2Word.walk 0 (oddBottom w)).map (fun z => (0 + F2Word.sum (oddBottom w) + F2Word.sum (oddRight w)) - z),
      p ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) :=
  top_marks_of_bottom (oddTile w) (hWordOf w false) (vWordOf w false) (oddBottom w) (oddRight w)
    (FLatticePaper.Tiles.SiteLowLeft.lowLeft_oddTile w) (hP_odd w) hB

/-- **The top side of the odd child lies in the marks**, with no remaining input: the bottom side lies in the horizontal string
sites by `HBottom.hB_odd`. -/
theorem top_marks_odd_all (w : Word) :
    ∀ p ∈ (F2Word.walk 0 (oddBottom w)).map (fun z => (0 + F2Word.sum (oddBottom w) + F2Word.sum (oddRight w)) - z),
      p ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) :=
  top_marks_odd w (FLatticePaper.Tiles.HBottom.hB_odd w)

/-- **The top side of the even child lies in the marks**: the bottom side lies in the horizontal string sites by
`HBottom.hB_even`, and the corner is the half-turn centre (`hP_even`). -/
theorem top_marks_even (w : Word) :
    ∀ p ∈ (F2Word.walk 0 (evenBottom w)).map (fun z => (0 + F2Word.sum (evenBottom w) + F2Word.sum (evenRight w)) - z),
      p ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true) :=
  top_marks_of_bottom (evenTile w) (hWordOf w true) (vWordOf w true) (evenBottom w) (evenRight w)
    (FLatticePaper.Tiles.SiteLowLeft.lowLeft_evenTile w) (hP_even w) (FLatticePaper.Tiles.HBottom.hB_even w)

end FLatticePaper.Tiles.HorizontalPair
