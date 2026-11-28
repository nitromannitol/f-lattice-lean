import FLatticePaper.Tiles.BaseInsideTile
import FLatticePaper.Tiles.BaseHpLadder
import FLatticePaper.Tiles.BaseHmOddFull
import FLatticePaper.Tiles.BaseVertOdoFamily
import FLatticePaper.Tiles.BaseVertVp
import FLatticePaper.Tiles.BaseHmAnchor
import FLatticePaper.Tiles.RespectsTransfer
import FLatticePaper.Tiles.SurgicalWeakOdometers

/-! # RespectsAnchored for the odd 3^k odometer

The four clauses of `RespectsAnchored` (Hp, Hm, Vm, Vp) are the four base clauses proved on the explicit families, transferred to
the odometer `wo.val` by `RespectsTiles.congr_placed`, since `wo.val` equals the paper value on the placed sites (they lie in the
domain by `insideTile_odd`). The `InsideTile` clause is `insideTile_odd`. -/

namespace FLatticePaper.Tiles.BaseRespectsAnchoredOdd

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Construction FLatticePaper.Tiles.BaseHmAnchor FLatticePaper.Tiles.BaseVertVp FLatticePaper.Tiles.BaseVertOdoFamily
open FLatticePaper.Tiles.BaseHpLadder FLatticePaper.Tiles.BaseHmOddFull

theorem mem_whole_1 (A B C D : List (ZTile × GInt)) {x : GInt} (hx : x ∈ placedSites A) :
    x ∈ placedSites (A ++ B ++ C ++ D) := by
  simp only [placedSites_append, List.mem_append] at hx ⊢
  tauto

theorem mem_whole_2 (A B C D : List (ZTile × GInt)) {x : GInt} (hx : x ∈ placedSites B) :
    x ∈ placedSites (A ++ B ++ C ++ D) := by
  simp only [placedSites_append, List.mem_append] at hx ⊢
  tauto

theorem mem_whole_3 (A B C D : List (ZTile × GInt)) {x : GInt} (hx : x ∈ placedSites C) :
    x ∈ placedSites (A ++ B ++ C ++ D) := by
  simp only [placedSites_append, List.mem_append] at hx ⊢
  tauto

theorem mem_whole_4 (A B C D : List (ZTile × GInt)) {x : GInt} (hx : x ∈ placedSites D) :
    x ∈ placedSites (A ++ B ++ C ++ D) := by
  simp only [placedSites_append, List.mem_append] at hx ⊢
  tauto

theorem respectsAnchored_odd (m : ℕ) (wo we : PartialOdometer)
    (hS : PaperBaseCond (List.replicate (m + 1) Digit.three) wo we) :
    RespectsAnchored wo.dom (hWordOf (List.replicate (m + 1) Digit.three) false)
      (vWordOf (List.replicate (m + 1) Digit.three) false) wo.val := by
  obtain ⟨hOd, hOv, -, -⟩ := hS.2.1 (m + 1) (by omega) rfl
  have hval : ∀ x, x ∈ placedSites (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0) ++
        hRevStringAt (hWordOf (List.replicate (m + 1) Digit.three) false).reverse
          (lastPosOf (vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0))) ++
        vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0) ++
        vStringAt (vWordOf (List.replicate (m + 1) Digit.three) false)
          (lastPosOf (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0)))) →
      paperLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) x = wo.val x := by
    intro x hx
    have hxI := insideTile_odd m x hx
    rw [Finset.mem_coe] at hxI
    have hxD : x ∈ wo.dom := by rw [hOd]; exact hxI
    exact (hOv x hxD).symm
  have hp : RespectsTiles .horizontal false (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0))
      (fun x => paperLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) x) := by
    rw [hWordOf_three_false]
    exact respects_hp_odd_three (m + 1) (by omega)
  have hm : RespectsTiles .horizontal true
      (hRevStringAt (hWordOf (List.replicate (m + 1) Digit.three) false).reverse
        (lastPosOf (vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0))))
      (fun x => paperLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) x) := by
    rw [anchor_hm_odd (m + 1) (by omega), hWordOf_three_false]
    exact respects_hm_odd (m + 1) (by omega)
  have hvm : RespectsTiles .vertical true (vRevStringAt (vWordOf (List.replicate (m + 1) Digit.three) false).reverse (0, 0))
      (fun x => paperLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) x) :=
    vm_odd_respects (m + 1) (by omega)
  have hvp : RespectsTiles .vertical false
      (vStringAt (vWordOf (List.replicate (m + 1) Digit.three) false)
        (lastPosOf (hStringAt (hWordOf (List.replicate (m + 1) Digit.three) false) (0, 0))))
      (fun x => paperLadderValue (2 * ((m + 1 : ℕ) : ℤ) + 2) x) :=
    vp_odd_respects (m + 1) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hOd]
    exact insideTile_odd m
  · exact RespectsTiles.congr_placed hp (fun x hx => hval x (mem_whole_1 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hm (fun x hx => hval x (mem_whole_2 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hvm (fun x hx => hval x (mem_whole_3 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hvp (fun x hx => hval x (mem_whole_4 _ _ _ _ hx))

end FLatticePaper.Tiles.BaseRespectsAnchoredOdd
