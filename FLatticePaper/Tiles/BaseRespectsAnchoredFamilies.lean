import FLatticePaper.Tiles.BaseRespectsAnchoredOdd
import FLatticePaper.Tiles.BaseHpStair
import FLatticePaper.Tiles.BaseHmThreeEven
import FLatticePaper.Tiles.BaseThreeEven
import FLatticePaper.Tiles.BaseInsideAlongEven
import FLatticePaper.Tiles.BaseHpNear
import FLatticePaper.Tiles.BaseHmTwoAnchor
import FLatticePaper.Tiles.BaseHmTwoOddOdo
import FLatticePaper.Tiles.BaseTwoOdd
import FLatticePaper.Tiles.BaseNearContain
import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.BaseHmTwoEven
import FLatticePaper.Tiles.BaseTwoEven
import FLatticePaper.Tiles.BaseNearContainEven

/-! # RespectsAnchored for the base families, from the paper values

`RespectsAnchored` for an odometer whose values are a paper value `P` on its domain follows from the four boundary clauses
for `P` (`respectsAnchored_of_paper`), and the InsideTile clause. The even `3^k` child (`k ≥ 0`, so the empty word's even
child is the case `k = 0`) is the first instance. -/

namespace FLatticePaper.Tiles.BaseRespectsAnchoredFamilies

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SurgicalWeak FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Construction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.BaseRespectsAnchoredOdd

/-- `RespectsAnchored` transferred from a paper value `P` on the domain `T` of the odometer `O`: the four boundary clauses
for `P` give the clauses for `O.val`, since `O.val = P` on the placed sites, which lie in `T` by the InsideTile clause. -/
theorem respectsAnchored_of_paper (O : PartialOdometer) (wh wv : BinaryWord) (T : Finset Site) (P : Site → ℤ)
    (hT : InsideTile (↑T : Set GInt) (hStringAt wh (0, 0) ++
      hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse (0, 0))) ++
      vRevStringAt wv.reverse (0, 0) ++ vStringAt wv (lastPosOf (hStringAt wh (0, 0)))))
    (hdom : O.dom = T) (hval : ∀ x ∈ O.dom, O.val x = P x)
    (hp : RespectsTiles .horizontal false (hStringAt wh (0, 0)) P)
    (hm : RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse (0, 0)))) P)
    (hvm : RespectsTiles .vertical true (vRevStringAt wv.reverse (0, 0)) P)
    (hvp : RespectsTiles .vertical false (vStringAt wv (lastPosOf (hStringAt wh (0, 0)))) P) :
    RespectsAnchored O.dom wh wv O.val := by
  have hv : ∀ x ∈ placedSites (hStringAt wh (0, 0) ++
      hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse (0, 0))) ++
      vRevStringAt wv.reverse (0, 0) ++ vStringAt wv (lastPosOf (hStringAt wh (0, 0)))), P x = O.val x := by
    intro x hx
    exact (hval x (by rw [hdom]; exact hT x hx)).symm
  refine ⟨by rw [hdom]; exact hT, ?_, ?_, ?_, ?_⟩
  · exact RespectsTiles.congr_placed hp (fun x hx => hv x (mem_whole_1 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hm (fun x hx => hv x (mem_whole_2 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hvm (fun x hx => hv x (mem_whole_3 _ _ _ _ hx))
  · exact RespectsTiles.congr_placed hvp (fun x hx => hv x (mem_whole_4 _ _ _ _ hx))

/-- `RespectsAnchored` for the even child of `replicate k 3` (`k ≥ 0`; `k = 0` is the even child of the empty word), whose
odometer has the stair domain and the stair values `paperStairValue (2k+3)`. -/
theorem respectsAnchored_even_three (k : ℕ) (E : PartialOdometer)
    (hdom : E.dom = stairF (2 * (k : ℤ) + 3))
    (hval : ∀ x ∈ E.dom, E.val x = paperStairValue (2 * (k : ℤ) + 3) x) :
    RespectsAnchored E.dom (hWordOf (List.replicate k Digit.three) true)
      (vWordOf (List.replicate k Digit.three) true) E.val :=
  respectsAnchored_of_paper E _ _ (stairF (2 * (k : ℤ) + 3)) (fun x => paperStairValue (2 * (k : ℤ) + 3) x)
    (insideTile_even k) hdom hval
    (by
      rw [FLatticePaper.Tiles.BaseHpStair.hWordOf_three_true]
      exact FLatticePaper.Tiles.BaseHpStair.respects_hp_even_three k)
    (by
      rw [FLatticePaper.Tiles.BaseHmThreeEven.anchor_hm_three, FLatticePaper.Tiles.BaseHpStair.hWordOf_three_true]
      exact FLatticePaper.Tiles.BaseHmThreeEven.respects_hm_three k)
    (FLatticePaper.Tiles.BaseThreeEven.vm3e_respects k)
    (FLatticePaper.Tiles.BaseThreeEven.vp3e_respects k)

/-- `RespectsAnchored` for the odd child of `replicate k 2` (`k ≥ 0`; `k = 0` is the odd child of the empty word), whose
odometer has the near-stair domain `nstairN (2k+3)` and the values `paperNearStairValue (2k+3)` read at `x + (0,1)`. The
odd horizontal reversed clause is `odo2_respects` at the anchor `posH2 k 0` (`anchor_hm_two`). -/
theorem respectsAnchored_odd_two (k : ℕ) (O : PartialOdometer)
    (hdom : O.dom = nstairN (2 * (k : ℤ) + 3))
    (hval : ∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))) :
    RespectsAnchored O.dom (hWordOf (List.replicate k Digit.two) false)
      (vWordOf (List.replicate k Digit.two) false) O.val :=
  respectsAnchored_of_paper O _ _ (nstairN (2 * (k : ℤ) + 3))
    (fun x => paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1)))
    (FLatticePaper.Tiles.BaseNearContain.insideTile_two_odd k) hdom hval
    (by
      rw [FLatticePaper.Tiles.BaseHpNear.hWordOf_two_false]
      exact FLatticePaper.Tiles.BaseHpNear.respects_hp_odd_two k)
    (by
      rw [FLatticePaper.Tiles.BaseHmTwoAnchor.anchor_hm_two, FLatticePaper.Tiles.BaseHpNear.hWordOf_two_false]
      exact FLatticePaper.Tiles.BaseHmTwoOddOdo.odo2_respects k)
    (FLatticePaper.Tiles.BaseTwoOdd.vm2_odd_respects k)
    (FLatticePaper.Tiles.BaseTwoOdd.vp2_odd_respects k)

/-- `RespectsAnchored` for the even child of `replicate k 2` (`k ≥ 1`), whose odometer has the near-ladder domain
`nladderN (2k+2)` and the values `paperNearLadderValue (2k+2)` read at `x + (0,1)`. The reversed horizontal clause is
`respects_hm_even` at the anchor `posE k 0` (`anchor_hm_even`). -/
theorem respectsAnchored_even_two (k : ℕ) (hk : 1 ≤ k) (E : PartialOdometer)
    (hdom : E.dom = nladderN (2 * (k : ℤ) + 2))
    (hval : ∀ x ∈ E.dom, E.val x = paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))) :
    RespectsAnchored E.dom (hWordOf (List.replicate k Digit.two) true)
      (vWordOf (List.replicate k Digit.two) true) E.val :=
  respectsAnchored_of_paper E _ _ (nladderN (2 * (k : ℤ) + 2))
    (fun x => paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1)))
    (FLatticePaper.Tiles.BaseNearContainEven.insideTile_two_even k hk) hdom hval
    (by
      rw [FLatticePaper.Tiles.BaseHpNearEven.hWordOf_two_true]
      exact FLatticePaper.Tiles.BaseHpNearEven.respects_hp_even_two k hk)
    (by
      rw [FLatticePaper.Tiles.BaseHmTwoEven.anchor_hm_even, FLatticePaper.Tiles.BaseHpNearEven.hWordOf_two_true]
      exact FLatticePaper.Tiles.BaseHmTwoEven.respects_hm_even k hk)
    (FLatticePaper.Tiles.BaseTwoEven.vm2e_respects k hk)
    (FLatticePaper.Tiles.BaseTwoEven.vp2e_respects k hk)

/-- The base case of `RespectsAnchored` for both children of a base word (`IsBase w`), from the concrete base condition
`PaperBaseCond`: the empty word has the odd child of `2^0` and the even child of `3^0`; `3^k` (`k ≥ 1`) and `2^k` (`k ≥ 1`)
have the odd and even children of the two families. -/
theorem respectsAnchored_of_base (w : Word) (hw : FLatticePaper.Tiles.Standard.IsBase w) (O E : PartialOdometer)
    (hS : PaperBaseCond w O E) :
    RespectsAnchored O.dom (hWordOf w false) (vWordOf w false) O.val ∧
    RespectsAnchored E.dom (hWordOf w true) (vWordOf w true) E.val := by
  by_cases hw0 : w = []
  · subst hw0
    obtain ⟨hOd, hOv, hEd, hEv⟩ := hS.1 rfl
    have e0 : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
    refine ⟨respectsAnchored_odd_two 0 O (by rw [e0]; exact hOd) (fun x hx => by rw [e0]; exact hOv x hx), ?_⟩
    exact respectsAnchored_even_three 0 E (by rw [e0]; exact hEd) (fun x hx => by rw [e0]; exact hEv x hx)
  · rcases hw with h | h | h
    · exact absurd h hw0
    · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.three :=
        ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := by
        cases k with
        | zero => simp at hw0
        | succ m => exact ⟨m, rfl⟩
      have hk := hS.2.1 (m + 1) (by omega) rfl
      exact ⟨respectsAnchored_odd m O E hS, respectsAnchored_even_three (m + 1) E hk.2.2.1 hk.2.2.2⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = List.replicate k Digit.two :=
        ⟨w.length, List.eq_replicate_iff.2 ⟨rfl, h⟩⟩
      have hk1 : 1 ≤ k := by
        cases k with
        | zero => simp at hw0
        | succ m => omega
      have hk := hS.2.2 k hk1 rfl
      exact ⟨respectsAnchored_odd_two k O hk.1 hk.2.1, respectsAnchored_even_two k hk1 E hk.2.2.1 hk.2.2.2⟩

end FLatticePaper.Tiles.BaseRespectsAnchoredFamilies
