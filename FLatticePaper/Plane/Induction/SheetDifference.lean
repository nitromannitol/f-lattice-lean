import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetSwap
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.EarlierChainPrice
import FLatticePaper.Construction.QuarterTurnCorrection

namespace FLatticePaper.Induction
open Farey

/-- The centred quarter-turn correction is the harmonic correction `h₀`: both have four times the same numerator. -/
theorem centeredQuarterTurnCorrection_eq_harmonicGrid (point : Site) :
    FLatticePaper.Construction.centeredQuarterTurnCorrection point = harmonicGrid point := by
  have h1 := FLatticePaper.Construction.four_mul_centeredQuarterTurnCorrection point
  have h2 := harmonicGrid_exact point
  linarith

/-- The harmonic correction of a translate by an even vector is affine in the site. -/
theorem harmonicGrid_sub_even (a x : Site) (ha : EvenSite a) :
    harmonicGrid (x - a) = harmonicGrid x + harmonicGrid (-a) -
      ((a.1 + a.2) / 2) * x.1 - ((a.1 - a.2) / 2) * x.2 := by
  have e1 := harmonicGrid_exact (x - a)
  have e2 := harmonicGrid_exact x
  have e3 := harmonicGrid_exact (-a)
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at e1 e3
  unfold EvenSite at ha
  have ha' : a.1 + a.2 = 2 * ((a.1 + a.2) / 2) := by omega
  have hb' : a.1 - a.2 = 2 * ((a.1 - a.2) / 2) := by omega
  have hp : (x.1 - a.1 + (x.2 - a.2)) % 2 = (x.1 + x.2) % 2 := by omega
  have hpa : (-a.1 + -a.2) % 2 = 0 := by omega
  have key : 4 * harmonicGrid (x - a) = 4 * (harmonicGrid x + harmonicGrid (-a) -
      ((a.1 + a.2) / 2) * x.1 - ((a.1 - a.2) / 2) * x.2) := by
    linear_combination e1 - e2 - e3 - 2 * x.1 * ha' - 2 * x.2 * hb' - hp + hpa
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) key

/-- The even offset `sheetOffset` of a frame has even coordinate sum. -/
theorem ChildFrame.evenSite_sheetOffset (frame : ChildFrame) : EvenSite frame.sheetOffset := by
  obtain ⟨k, hk, -, -, -, -, -, -, -, hof⟩ := frame.sheet_facts
  refine evenSite_of_sum _ (frame.parents.even.num + (2 * frame.phaseW - 1) * k) ?_
  rw [hof]
  dsimp only
  linear_combination (2 * frame.phaseW - 1) * hk

/-- The explicit difference of the two sheets: a difference of `G` along `Z(x − e)` and `Z x`, plus an affine
function of `z`, where `x = z − sheetShift` and `e = sheetOffset`. -/
theorem ChildFrame.sheetC_sub_sheetA_eq (frame : ChildFrame) (G : Field) (z : Site) :
    frame.sheetC (quarterTurnField G) z - frame.sheetA (quarterTurnField G) z =
      G (-(z - frame.sheetShift).2 + frame.sheetOffset.2,
          (z - frame.sheetShift).1 - 1 - frame.sheetOffset.1) -
        G (-(z - frame.sheetShift).2, (z - frame.sheetShift).1 - 1) +
        (frame.sheetConstant + harmonicGrid (-frame.sheetOffset)) +
        frame.siblingSlope (z - frame.sheetShift) -
        ((frame.sheetOffset.1 + frame.sheetOffset.2) / 2) * (z - frame.sheetShift).1 -
        ((frame.sheetOffset.1 - frame.sheetOffset.2) / 2) * (z - frame.sheetShift).2 := by
  have hE := frame.evenSite_sheetOffset
  unfold ChildFrame.sheetC ChildFrame.sheetA
  simp only [quarterTurnField_eq]
  rw [harmonicGrid_sub_even frame.sheetOffset (z - frame.sheetShift) hE]
  have hG : (-(z - frame.sheetShift - frame.sheetOffset).2,
      (z - frame.sheetShift - frame.sheetOffset).1 - 1) =
      (-(z - frame.sheetShift).2 + frame.sheetOffset.2,
        (z - frame.sheetShift).1 - 1 - frame.sheetOffset.1) :=
    Prod.ext (by simp only [Prod.snd_sub]; ring)
      (by simp only [Prod.fst_sub]; ring)
  rw [hG]
  unfold ChildFrame.siblingSlope
  ring

/-- The consumed even shift of the odd donor is the offset of the sheet C. -/
theorem consumedEvenShift_eq_sheetOffset (frame : ChildFrame) :
    FLatticePaper.consumedEvenShift frame.parents.even frame.eps = frame.sheetOffset := by
  unfold FLatticePaper.consumedEvenShift ChildFrame.sheetOffset
  simp only [Fraction.unmodifiedDeck, PeriodDeck.combine, Prod.smul_mk, smul_eq_mul]
  exact Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)

/-- The donor price of the quarter-turned parent is the sheet difference `C − A`. -/
theorem donorPrice_sheetDifference (frame : ChildFrame) (G : Field) (z : Site) :
    FLatticePaper.donorPrice (quarterTurnField G) frame.parents.even frame.eps frame.sheetConstant
        (z - frame.sheetShift) =
      frame.sheetC (quarterTurnField G) z - frame.sheetA (quarterTurnField G) z := by
  unfold FLatticePaper.donorPrice
  rw [consumedEvenShift_eq_sheetOffset]
  unfold ChildFrame.sheetC ChildFrame.sheetA ChildFrame.siblingSlope Fraction.transverseGrade
  ring

/-- Every proper word is the donor word of its birth prefix. -/
theorem exists_donorWord (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three) :
    ∃ (b : Bool) (k : ℕ), donorWord (oddBirthPrefix word) b k = word := by
  obtain ⟨x, hx, k, hw⟩ := oddBirthPrefix_decomp h
  cases x with
  | one =>
    refine ⟨true, k, ?_⟩
    simpa [donorWord] using hw.symm
  | two =>
    refine ⟨false, k, ?_⟩
    simpa [donorWord] using hw.symm
  | three => exact absurd rfl hx

/-- The sheet difference is the earlier chain potential, up to a constant: `Ψ(z) + Φ'(Z(z − lv)) = K`, for every
proper word, given the conjugate packet. -/
theorem sheetDifference_identifies {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {G : Field}
    (hG : (frameAt (conjWord word)).Packet G) :
    ∃ K : ℤ, ∀ z : Site,
      (frameAt word).sheetC (quarterTurnField G) z - (frameAt word).sheetA (quarterTurnField G) z +
        FLatticePaper.earlierChainPrice G (frameAt (conjWord word)).parents.odd
          (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
          (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) = K := by
  obtain ⟨b, k, hword⟩ := exists_donorWord word h
  have hcur : parentsAt (donorWord (oddBirthPrefix word) b k) = parentsAt word := by
    rw [hword]
  have hperiod : HasGeneratorPeriods ((parentsAt ((oddBirthPrefix word).map Digit.swapTwoThree)).current .even)
      G (frameAt (conjWord word)).coherentConstantU (frameAt (conjWord word)).coherentConstantV :=
    hG.periods
  have hrotate : ∀ site, quarterTurnField G site =
      G (QuarterTurn.counterclockwise.mapSite (0, -1) site) +
        FLatticePaper.Construction.centeredQuarterTurnCorrection site := by
    intro site
    rw [quarterTurn_site, centeredQuarterTurnCorrection_eq_harmonicGrid]
    simp only [quarterTurnField_eq]
  obtain ⟨value, hval⟩ := FLatticePaper.donorPrice_add_earlierChainPrice (oddBirthPrefix word) b k G
    (quarterTurnField G) (frameAt (conjWord word)).coherentConstantU
    (frameAt (conjWord word)).coherentConstantV (frameAt word).sheetConstant hperiod hrotate
  refine ⟨value, fun z => ?_⟩
  have hz := hval (z - (frameAt word).sheetShift)
  rw [quarterTurn_site, hcur] at hz
  have hz2 : FLatticePaper.donorPrice (quarterTurnField G) (frameAt word).parents.even (frameAt word).eps
        (frameAt word).sheetConstant ((z - (frameAt word).sheetShift)) +
      FLatticePaper.earlierChainPrice G (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
        (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) = value := hz
  rw [← donorPrice_sheetDifference (frameAt word) G z]
  exact hz2

/-- The identification when the conjugate word is pure: its standard field has the reciprocal packet. -/
theorem sheetDifference_identifies_pure {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {k : ℕ}
    (hk : conjWord word = List.replicate k Digit.three) :
    ∃ K : ℤ, ∀ z : Site,
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z +
        FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
          (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
          (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) = K := by
  have hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)) := by
    rw [hk]
    exact reciprocal_packet k
  exact sheetDifference_identifies h hG

end FLatticePaper.Induction
