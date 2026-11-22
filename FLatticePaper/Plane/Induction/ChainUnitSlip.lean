import FLatticePaper.Plane.Induction.SheetMinFromConj

/-! Task 27: the unit increments of the chain potential `Xi = sheetChainPotential`, in the slip form used by the sheet
argument.

The premise (I3a) of LocalPremises is `Edge i c -> -1 <= Xi i - Xi c <= 1`. The two sheets `A = sheetA`, `C = sheetC`
of the quarter-turned field satisfy `A - C = Xi(. - lv) - K` (sheetDifference_identifies), so the slip increment of the
pair `(A, C)` is the increment of `Xi` on the shifted edge. Since the shift `lv` is even, edges are preserved. Hence the
unit increments of `Xi` are exactly `HasUnitSlip A C`, the hypothesis that the star arguments of the plane step use
(HasUnitSlip in AlternateMidpoint.lean). -/

namespace FLatticePaper.Induction
open Farey FLatticePaper

/-- (I3a) gives the unit slip of the sheet pair. -/
theorem hasUnitSlip_sheets_of_chain {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    (hunit : ∀ c i : Site, FLatticePaper.Edge i c →
      -1 ≤ sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ∧
        sheetChainPotential word (standardField (conjWord word)) i -
          sheetChainPotential word (standardField (conjWord word)) c ≤ 1) :
    HasUnitSlip ((frameAt word).sheetA (quarterTurnField (standardField (conjWord word))))
      ((frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))) := by
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
  intro c i hE
  unfold slipIncrement
  rw [hid i, hid c]
  have hu := hunit (c - (frameAt word).sheetShift) (i - (frameAt word).sheetShift)
    (edge_sub_even i c (frameAt word).sheetShift hs hE)
  constructor <;> linarith [hu.1, hu.2]

/-- The rise step of the archive (STRONG_PRICE_AND_ALTERNATE_STEP §4): "A Phi rise along a canonical F edge z -> u now
forces D(u) = D(z) and P(u + eta sigma) = P(z + eta sigma) + 1". With `D` nonincreasing along the edge (`dD <= 0`) and
`P` rising by at most one (`dP <= 1`), a rise of `Phi = D + P` (`1 <= dD + dP`) forces `dD = 0` and `dP = 1`. -/
theorem rise_forces_flat_D_and_P_step (dD dP : ℤ) (hD : dD ≤ 0) (hP : dP ≤ 1) (hrise : 1 ≤ dD + dP) :
    dD = 0 ∧ dP = 1 := by
  omega

end FLatticePaper.Induction
