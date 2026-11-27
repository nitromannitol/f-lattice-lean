import FLatticePaper.Plane.Induction.PlusRowEndpoint
import FLatticePaper.Plane.Induction.H0Core

/-! # The plus entry `V_{-1} = (1,-1)` is refuted by the earlier entry `V_{-2} = (1,-2)` (eta = 1)

The refutation tree is the same for every word: `V_{-1} = (1,-1)` is a free white whose free prescription is the odd site
`y = (2,-1)`; `y` is black with inputs `incomingNeg y = (2,-2)` and `incomingPos y = (2,0)`; the site `(2,-2)` is a non-free white
whose permitted input is its incoming site `(1,-2) = V_{-2}` (the earlier entry); `(2,0)` is a `lowPair` leaf. The laplacians,
the free-closure fact at `(2,-2)` and the price/slip facts at `(2,0)` are inputs, as for the minus core. -/

namespace FLatticePaper.PlusVm1

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows

/-- **The plus `V_{-1}` is refuted by `V_{-2}`.** -/
theorem refuted_Vm1_plus (frame : ChildFrame) (F : Field) {E C : Site → Prop}
    (hw : laplacian F ((1 : ℤ), (-1 : ℤ)) = 0)
    (hp : ∀ i, FreePolicy.FreePresc frame 1 ((1 : ℤ), (-1 : ℤ)) i ↔ i = ((2 : ℤ), (-1 : ℤ)))
    (hy : laplacian F ((2 : ℤ), (-1 : ℤ)) = -1)
    (hz : laplacian F ((2 : ℤ), (-2 : ℤ)) = 0)
    (hnfz : ¬ FreeClosure.freeClosure frame ((2 : ℤ), (-2 : ℤ)))
    (hwp : frame.price F ((2 : ℤ), (0 : ℤ)) ≤ frame.cutPrice)
    (hwj : frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≤ 0)
    (hwne : frame.price F ((2 : ℤ), (0 : ℤ)) ≠ frame.cutPrice ∨ frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≠ 0)
    (hE : E ((1 : ℤ), (-2 : ℤ))) :
    RefuteTree.Refuted frame F 1 E C ((1 : ℤ), (-1 : ℤ)) := by
  have hodd : ¬ EvenSite ((2 : ℤ), (-1 : ℤ)) := by unfold EvenSite; norm_num
  have hev : EvenSite ((2 : ℤ), (-2 : ℤ)) := by unfold EvenSite; norm_num
  have hn : incomingNeg ((2 : ℤ), (-1 : ℤ)) = ((2 : ℤ), (-2 : ℤ)) := by
    rw [H0Core.incomingNeg_of_not_even _ hodd]
    norm_num
  have hpo : incomingPos ((2 : ℤ), (-1 : ℤ)) = ((2 : ℤ), (0 : ℤ)) := by
    rw [H0Core.incomingPos_of_not_even _ hodd]
    norm_num
  -- the non-free white (2,-2) is refuted by its incoming site (1,-2) = V_{-2}
  have hzref : RefuteTree.Refuted frame F 1 E C ((2 : ℤ), (-2 : ℤ)) :=
    RefuteTree.Refuted.white hz (Or.inr ⟨hz, Or.inr ⟨hnfz, Or.inl (by
      rw [H0Core.incomingNeg_of_even _ hev]
      norm_num)⟩⟩) (RefuteTree.Refuted.earlier hE)
  -- the lowPair leaf (2,0)
  have hwref : RefuteTree.Refuted frame F 1 E C ((2 : ℤ), (0 : ℤ)) :=
    RefuteTree.Refuted.lowPair hwp hwj hwne
  -- the black site (2,-1) with both inputs refuted
  have hyref : RefuteTree.Refuted frame F 1 E C ((2 : ℤ), (-1 : ℤ)) := by
    refine RefuteTree.Refuted.black hy ?_ ?_
    · rw [hn]; exact hzref
    · rw [hpo]; exact hwref
  -- the free white V_{-1} with its free prescription (2,-1)
  have hpos : FreePolicy.FreePresc frame 1 ((1 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-1 : ℤ)) := (hp _).mpr rfl
  have hperm : permitsQ1 frame F 1 ((1 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-1 : ℤ)) :=
    Or.inr ⟨hw, Or.inl ⟨PlusRowEndpoint.freeClosure_of_freePresc frame hpos, hpos⟩⟩
  exact RefuteTree.Refuted.white hw hperm hyref

end FLatticePaper.PlusVm1
