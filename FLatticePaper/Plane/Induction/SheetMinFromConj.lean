import FLatticePaper.Plane.Induction.SheetMinRank
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.WordInduction

namespace FLatticePaper.Induction
open Farey

/-- The earlier chain potential in the coordinates of the quarter-turned parent: `Ξ(x) = Φ'(Z x)`, with
`Z(x) = (−x₂, x₁ − 1)`. -/
def sheetChainPotential (word : Word) (G : Field) (x : Site) : ℤ :=
  FLatticePaper.earlierChainPrice G (frameAt (conjWord word)).parents.odd
    (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (-x.2, x.1 - 1)

theorem incomingNeg_sub_even' (c v : Site) (hv : EvenSite v) :
    FLatticePaper.incomingNeg (c - v) = FLatticePaper.incomingNeg c - v := by
  rw [sub_eq_add_neg c v, FLatticePaper.incomingNeg_add_of_even c (-v) (evenSite_neg_site v hv),
    sub_eq_add_neg (FLatticePaper.incomingNeg c) v]

theorem incomingPos_sub_even' (c v : Site) (hv : EvenSite v) :
    FLatticePaper.incomingPos (c - v) = FLatticePaper.incomingPos c - v := by
  rw [sub_eq_add_neg c v, FLatticePaper.incomingPos_add_of_even c (-v) (evenSite_neg_site v hv),
    sub_eq_add_neg (FLatticePaper.incomingPos c) v]

/-- Physical edges are invariant under an even translation. -/
theorem edge_sub_even (i c v : Site) (hv : EvenSite v) (h : FLatticePaper.Edge i c) :
    FLatticePaper.Edge (i - v) (c - v) := by
  unfold FLatticePaper.Edge at h ⊢
  rcases h with rfl | rfl
  · exact Or.inl (by rw [incomingNeg_sub_even' c v hv])
  · exact Or.inr (by rw [incomingPos_sub_even' c v hv])

/-- (I3) from properties of the conjugate, stated for the quarter-turned parent `Fp = quarterTurnField G`:
(a) the chain potential `Ξ` changes by at most one along physical edges; (b) there are constrained burning ranks of
`Fp` whose chosen inputs do not increase `Ξ` (A-type) and do not decrease `Ξ` after the shift by the sheet offset
(C-type). Then the sheet minimum `M = min(A, C)` is binary and recurrent on the whole plane. -/
theorem sheetMin_binary_recurrent_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1)
    {α : Type*} [LinearOrder α] (rankA rankC : Site → α)
    (hrankA : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankA
      (fun c i => sheetChainPotential word (standardField (conjWord word)) i ≤
        sheetChainPotential word (standardField (conjWord word)) c))
    (hrankC : IsConstrainedBurningRank (quarterTurnField (standardField (conjWord word))) rankC
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c + (frameAt word).sheetOffset) ≤
        sheetChainPotential word (standardField (conjWord word)) (i + (frameAt word).sheetOffset))) :
    (∀ z ∈ (frameAt word).closedPolygon,
        laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = -1 ∨
          laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = 0) ∧
      Recurrent ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  obtain ⟨K, hK⟩ := sheetDifference_identifies h hG
  have hs : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  have hid : ∀ z : Site,
      (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z -
          (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z =
        sheetChainPotential word (standardField (conjWord word)) (z - (frameAt word).sheetShift) - K := by
    intro z
    have := hK z
    unfold sheetChainPotential
    linarith
  have hslip : ∀ c i : Site,
      slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i =
        sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift) -
          sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift) := by
    intro c i
    unfold slipIncrement
    rw [hid i, hid c]
    ring
  have hunitAC : HasUnitSlip ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) := by
    intro c i hE
    rw [hslip c i]
    exact hunit (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift)
      (edge_sub_even i c (frameAt word).sheetShift hs hE)
  have hpermA : (fun c i => slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i ≤ 0) =
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift) ≤
        sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift)) := by
    funext c i
    rw [hslip c i]
    exact propext ⟨fun hh => by linarith, fun hh => by linarith⟩
  have hA : IsConstrainedBurningRank ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
      (fun z => rankA (z - (frameAt word).sheetShift))
      (fun c i => slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i ≤ 0) := by
    rw [hpermA]
    exact ChildFrame.sheetA_rank hrankA
  have e1 : ∀ c : Site, c - ((frameAt word).sheetShift + (frameAt word).sheetOffset) +
      (frameAt word).sheetOffset = c - (frameAt word).sheetShift := fun c => by abel
  have hpermC : (fun c i => 0 ≤ slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i) =
      (fun c i => sheetChainPotential word (standardField (conjWord word)) (c - (frameAt word).sheetShift) ≤
        sheetChainPotential word (standardField (conjWord word)) (i - (frameAt word).sheetShift)) := by
    funext c i
    rw [hslip c i]
    exact propext ⟨fun hh => by linarith, fun hh => by linarith⟩
  have hC : IsConstrainedBurningRank ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word))))
      (fun z => rankC (z - ((frameAt word).sheetShift + (frameAt word).sheetOffset)))
      (fun c i => 0 ≤ slipIncrement ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
          ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) c i) := by
    rw [hpermC]
    have h1 := ChildFrame.sheetC_rank (frame := frameAt word) hrankC
    simp only [e1] at h1
    exact h1
  obtain ⟨hbin, hrec⟩ := ChildFrame.sheetMin_binary_recurrent (frameAt word) hunitAC hA hC
  exact ⟨fun z _ => hbin z, hrec⟩

end FLatticePaper.Induction
