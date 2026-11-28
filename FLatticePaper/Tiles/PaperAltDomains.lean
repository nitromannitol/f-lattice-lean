import FLatticePaper.Tiles.JointFamily
import FLatticePaper.Tiles.BaseTileProps

/-! # The alternate boundary tiles at the base words

`JointFamily.PaperAltBdry` takes the printed alternate tiles (`SurgicalAltTiles.altOddTile`, `altEvenTile` over
`PaperAltBase.paperAltBaseTiles`) as the domains of the alternate odometers. At a base word these are the base alternates, and
`altBase_domains` shows they are the domains that `PaperAltBaseCond` fixes: the paper's sets of `prop:base_cases` are inside the
boxes `PaperAltBase.boxF d` for `d ≥ 3`, and the frames (the read points `x + (0, 1)` and `x - (1, 1)`) are the translations of
`paperAltBaseTiles`. -/

namespace FLatticePaper.Tiles.PaperAltDomains

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Construction
open FLatticePaper.Tiles.PaperAltBase
open FLatticePaper.Tiles.SurgicalAlt (PaperAltBaseCond)
open FLatticePaper.Tiles.BaseTileProps (mem_stAlt mem_ladAlt mem_nsAlt mem_nlAlt)
open FLatticePaper.Tiles.Standard (IsBase shift mem_shift)

theorem stairAltF_iff (d : ℤ) (hd : 3 ≤ d) (z : Site) : z ∈ stairAltF d ↔ z ∈ paperStairAltTile d := by
  obtain ⟨a, b⟩ := z
  rw [mem_stAlt]
  simp only [stairAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => by simpa only [or_assoc] using h.2, fun h => ⟨?_, by simpa only [or_assoc] using h⟩⟩
  omega

theorem ladderAltF_iff (d : ℤ) (hd : 3 ≤ d) (z : Site) : z ∈ ladderAltF d ↔ z ∈ paperLadderAltTile d := by
  obtain ⟨a, b⟩ := z
  rw [mem_ladAlt]
  simp only [ladderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk.injEq]
  refine ⟨fun h => by simpa only [or_assoc] using h.2, fun h => ⟨?_, by simpa only [or_assoc] using h⟩⟩
  have h1 := h.1
  clear h
  omega

theorem nearStairAltF_iff (d : ℤ) (hd : 3 ≤ d) (z : Site) : z ∈ nearStairAltF d ↔ z ∈ paperNearStairAltTile d := by
  obtain ⟨a, b⟩ := z
  rw [mem_nsAlt]
  simp only [nearStairAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => by simpa only [or_assoc] using h.2, fun h => ⟨?_, by simpa only [or_assoc] using h⟩⟩
  omega

theorem nearLadderAltF_iff (d : ℤ) (hd : 3 ≤ d) (z : Site) : z ∈ nearLadderAltF d ↔ z ∈ paperNearLadderAltTile d := by
  obtain ⟨a, b⟩ := z
  rw [mem_nlAlt]
  simp only [nearLadderAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.mk.injEq]
  refine ⟨fun h => by simpa only [or_assoc] using h.2, fun h => ⟨?_, by simpa only [or_assoc] using h⟩⟩
  have h1 := h.1
  clear h
  omega

theorem mem_shift_down (T : Standard.Tile) (x : Site) : x ∈ shift T ((0 : ℤ), (-1 : ℤ)) ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ T := by
  rw [mem_shift]
  have : x - ((0 : ℤ), (-1 : ℤ)) = x + ((0 : ℤ), (1 : ℤ)) := by
    ext <;> simp
  rw [this]

theorem altOddTile_base (w : Word) (hb : IsBase w) :
    SurgicalAltTiles.altOddTile paperAltBaseTiles w = (paperAltBaseTiles w).1 := by
  simp only [SurgicalAltTiles.altOddTile, SurgicalAltTiles.altChild, if_pos hb]

theorem altEvenTile_base (w : Word) (hb : IsBase w) :
    SurgicalAltTiles.altEvenTile paperAltBaseTiles w = (paperAltBaseTiles w).2 := by
  simp only [SurgicalAltTiles.altEvenTile, SurgicalAltTiles.altChild, if_pos hb]

/-- At a base word, the alternate odometers of `PaperAltBaseCond` are defined exactly on the printed alternate tiles, the
domains of `JointFamily.PaperAltBdry`. -/
theorem altBase_domains (w : Word) (hb : IsBase w) (O E : PartialOdometer) (h : PaperAltBaseCond w O E) :
    O.dom = SurgicalAltTiles.altOddTile paperAltBaseTiles w ∧
      E.dom = SurgicalAltTiles.altEvenTile paperAltBaseTiles w := by
  rw [altOddTile_base w hb, altEvenTile_base w hb]
  by_cases h0 : w = []
  · subst h0
    obtain ⟨hO, -, hE, -⟩ := h.1 rfl
    simp only [paperAltBaseTiles, if_true]
    refine ⟨Finset.ext fun x => ?_, Finset.ext fun x => ?_⟩
    · rw [hO, mem_shift_down, nearStairAltF_iff 3 le_rfl]
    · rw [hE, stairAltF_iff 3 le_rfl]
  have hn : 1 ≤ w.length := by
    cases w with
    | nil => exact absurd rfl h0
    | cons a l => simp
  by_cases h3 : w = List.replicate w.length Digit.three
  · obtain ⟨hO, -, hE, -⟩ := h.2.1 w.length hn h3
    simp only [paperAltBaseTiles, if_neg h0, if_pos h3]
    refine ⟨Finset.ext fun x => ?_, Finset.ext fun x => ?_⟩
    · rw [hO, mem_shift, ladderAltF_iff _ (by omega)]
    · rw [hE, stairAltF_iff _ (by omega)]
  have h2 : w = List.replicate w.length Digit.two := by
    rcases hb with hb | hb | hb
    · exact absurd hb h0
    · exact absurd (List.eq_replicate_iff.mpr ⟨rfl, hb⟩) h3
    · exact List.eq_replicate_iff.mpr ⟨rfl, hb⟩
  obtain ⟨hO, -, hE, -⟩ := h.2.2 w.length hn h2
  simp only [paperAltBaseTiles, if_neg h0, if_neg h3]
  refine ⟨Finset.ext fun x => ?_, Finset.ext fun x => ?_⟩
  · rw [hO, mem_shift_down, nearStairAltF_iff _ (by omega)]
  · rw [hE, mem_shift_down, nearLadderAltF_iff _ (by omega)]

/-- With `PaperAltBdry`, the base condition `PaperAltBaseCond` and the domain clause of `WeakAltPart` agree at the base words. -/
theorem paperAltBdry_base (D : JointFamily.JointData) (hB : JointFamily.PaperAltBdry D) (w : Word) (hb : IsBase w)
    (O E : PartialOdometer) (h : PaperAltBaseCond w O E) :
    O.dom = D.altBdry (some w) true ∧ E.dom = D.altBdry (some w) false := by
  rw [(hB w).1, (hB w).2]
  exact altBase_domains w hb O E h

end FLatticePaper.Tiles.PaperAltDomains
