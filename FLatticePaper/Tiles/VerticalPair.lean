import FLatticePaper.Tiles.VerticalRight
import FLatticePaper.Tiles.HorizontalPair
import FLatticePaper.Tiles.SiteLowLeft

/-! The vertical pair of the walk form of H2: the right side of the boundary walk of the odd tile lies in the marked sites.

The right side is the rotated walk of the horizontal word `gH (hWordOf (swapW w) true)` (`VerticalRight.oddRight_eq_gV` and
`walk_map_mulI_shift`). Its points are `Σw1 + rotI z` for `z` on that walk. The half-turn of such a point is `rotI (E - z)`, the
rotated reflection of the walk through its end `E`. This point lies in the vertical string sites of the marks: that containment is
the input `hR` (the reflection lemma), whose proof is a reversed telescoping of the tile list and is not yet written. -/

namespace FLatticePaper.Tiles.VerticalPair

open FLatticePaper.Tiles FLatticePaper.Farey FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.VerticalRight

/-- **The right side of the odd tile lies in the marks**, given the reflection input `hR`. -/
theorem right_marks_odd (w : Word)
    (hR : ∀ z ∈ F2Word.walk 0 (gH (hWordOf (swapW w) true)),
      rotI (F2Word.sum (gH (hWordOf (swapW w) true)) - z) + ((1 : ℤ), (1 : ℤ)) ∈
        stringSites true true (vWordOf w false).reverse) :
    ∀ p ∈ (F2Word.walk (0 + F2Word.sum (oddBottom w)) (oddRight w)).tail,
      p ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) := by
  intro p hp
  have hrot : oddRight w = (gH (hWordOf (swapW w) true)).map Unit4.mulI := by
    rw [oddRight_eq_gV, gV]
    exact congrArg (fun u => (gH u).map Unit4.mulI) (flipW_vWordOf w false)
  have hsum : F2Word.sum (oddRight w) = rotI (F2Word.sum (gH (hWordOf (swapW w) true))) := by
    rw [hrot, F2Word_sum_map_mulI]
  have hP := FLatticePaper.Tiles.HorizontalPair.hP_odd w
  have hc := FLatticePaper.Tiles.SiteLowLeft.lowLeft_oddTile w
  have hp' := List.mem_of_mem_tail hp
  rw [hrot, walk_map_mulI_shift, List.mem_map] at hp'
  obtain ⟨z, hz, rfl⟩ := hp'
  have hsv := hR z hz
  have hpt : halfTurn (oddTile w) (rotI (F2Word.sum (gH (hWordOf (swapW w) true)) - z))
      = 0 + F2Word.sum (oddBottom w) + rotI z := by
    have key : ∀ a b c : GInt, a + b - (b - c) = 0 + a + c := by
      intro a b c
      abel
    unfold halfTurn
    rw [← hP, hsum, rotI_sub]
    exact key _ _ _
  simp only [markedSites, hc]
  refine List.mem_append_right _ (List.mem_map.2 ⟨rotI (F2Word.sum (gH (hWordOf (swapW w) true)) - z), ?_, hpt⟩)
  refine List.mem_map.2 ⟨rotI (F2Word.sum (gH (hWordOf (swapW w) true)) - z) + ((1 : ℤ), (1 : ℤ)), hsv, ?_⟩
  ext <;> simp

/-- **The right side of the even tile lies in the marks**, given the reflection input `hR` for the even child. -/
theorem right_marks_even (w : Word)
    (hR : ∀ z ∈ F2Word.walk 0 (gH (hWordOf (swapW w) false)),
      rotI (F2Word.sum (gH (hWordOf (swapW w) false)) - z) + ((1 : ℤ), (1 : ℤ)) ∈
        stringSites true true (vWordOf w true).reverse) :
    ∀ p ∈ (F2Word.walk (0 + F2Word.sum (evenBottom w)) (evenRight w)).tail,
      p ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true) := by
  intro p hp
  have hrot : evenRight w = (gH (hWordOf (swapW w) false)).map Unit4.mulI := by
    rw [evenRight_eq_gV, gV]
    exact congrArg (fun u => (gH u).map Unit4.mulI) (flipW_vWordOf w true)
  have hsum : F2Word.sum (evenRight w) = rotI (F2Word.sum (gH (hWordOf (swapW w) false))) := by
    rw [hrot, F2Word_sum_map_mulI]
  have hP := FLatticePaper.Tiles.HorizontalPair.hP_even w
  have hc := FLatticePaper.Tiles.SiteLowLeft.lowLeft_evenTile w
  have hp' := List.mem_of_mem_tail hp
  rw [hrot, walk_map_mulI_shift, List.mem_map] at hp'
  obtain ⟨z, hz, rfl⟩ := hp'
  have hsv := hR z hz
  have key : ∀ a b c : GInt, a + b - (b - c) = 0 + a + c := by
    intro a b c
    abel
  have hpt : halfTurn (evenTile w) (rotI (F2Word.sum (gH (hWordOf (swapW w) false)) - z))
      = 0 + F2Word.sum (evenBottom w) + rotI z := by
    unfold halfTurn
    rw [← hP, hsum, rotI_sub]
    exact key _ _ _
  simp only [markedSites, hc]
  refine List.mem_append_right _ (List.mem_map.2 ⟨rotI (F2Word.sum (gH (hWordOf (swapW w) false)) - z), ?_, hpt⟩)
  refine List.mem_map.2 ⟨rotI (F2Word.sum (gH (hWordOf (swapW w) false)) - z) + ((1 : ℤ), (1 : ℤ)), hsv, ?_⟩
  ext <;> simp

end FLatticePaper.Tiles.VerticalPair
