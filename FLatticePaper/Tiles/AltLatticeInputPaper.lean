import FLatticePaper.Tiles.TileStepAssembly
import FLatticePaper.Tiles.AltLatticeCorrOWrap

/-! # The alternate lattice input of the tile step for the paper data

(b) of `lemma:weak_alternate_odometer_properties` along the second lattice vector, for the alternate tile odometers of the
corrected alternate children: the odd alternate child of a word ending in `2` and the even alternate child of a word ending
in `3` (`AltLatticeCorrOWrap.odd_W_corr_family`, `AltLatticeCorrEWrap.even_V_corr_family`). -/

namespace FLatticePaper.Tiles.AltLatticeInputPaper

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.TileStepAssembly (AltLatticeInput)

/-- A word whose last letter is `d` is a word followed by `d`. -/
theorem eq_snoc_of_getLast (w : Word) (d : Digit) (h : w.getLast? = some d) : ∃ u, w = u ++ [d] := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u a _ =>
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
    exact ⟨u, by rw [h]⟩

/-- **`AltLatticeInput` for the paper data.** -/
theorem altLatticeInput_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) (hAB : PaperAltBdry D) (hlS : D.lSides = paperLSides) :
    AltLatticeInput D := by
  intro f w wo we wao wae tod tev aod aev hg hP hho hhe
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨u, rfl⟩ := eq_snoc_of_getLast w Digit.two hc.2
    exact AltLatticeCorrOWrap.odd_W_corr_family D hS hA hlS f u hc.1 hg aod (hP.2.1 hc.1).2.2.1
      (hP.2.2.2.2.2.2.2.2.2.2.1.trans (hAB _).1) hho
  · obtain ⟨u, rfl⟩ := eq_snoc_of_getLast w Digit.three hc.2
    exact AltLatticeCorrEWrap.even_V_corr_family D hS hA hlS f u hc.1 hg aev (hP.2.1 hc.1).2.2.2
      (hP.2.2.2.2.2.2.2.2.2.2.2.trans (hAB _).2) hhe

end FLatticePaper.Tiles.AltLatticeInputPaper
