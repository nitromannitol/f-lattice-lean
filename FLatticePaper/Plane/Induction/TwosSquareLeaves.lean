import FLatticePaper.Plane.Induction.TwosSquares

namespace FLatticePaper.TwosEPolicy
open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

set_option maxHeartbeats 400000 in
theorem sq_leaf_8 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -3)
    (_c3 : (y - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c4 : 0 ≤ (y - x))
    (_c5 : 1 ≤ y) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_low_down (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_10 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -3)
    (_c3 : -1 ≤ (y - (2 * (k : ℤ) + 4)))
    (_c4 : (x - (2 * (k : ℤ) + 4)) ≤ 0) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inl rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y + 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_low_up (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_13 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -3)
    (_c3 : -1 ≤ (y - (2 * (k : ℤ) + 4)))
    (_c4 : 1 ≤ (x - (2 * (k : ℤ) + 4)))
    (_c5 : 1 ≤ (y - (2 * (k : ℤ) + 4))) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨1, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_low_down (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_18 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -2 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : (y - x - (2 * (k : ℤ) + 4)) ≤ 1)
    (_c4 : (y - x - (2 * (k : ℤ) + 4)) ≤ -1)
    (_c5 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -3)
    (_c6 : (y - (2 * (k : ℤ) + 4)) ≤ -2) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_low_down (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_19 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -2 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : (y - x - (2 * (k : ℤ) + 4)) ≤ 1)
    (_c4 : (y - x - (2 * (k : ℤ) + 4)) ≤ -1)
    (_c5 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -3)
    (_c6 : -1 ≤ (y - (2 * (k : ℤ) + 4))) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inr rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y + 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd] at he ⊢
      first
      | (refine Or.inr (Or.inl (Or.inr (Or.inr ?_))); omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); omega)
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inr (Or.inl ?_))
    simp only [CandE]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (1, 0) := by
    exact candDisp_E (by simp only [CandE]; omega)
  have hout : SqOut (x, y) ((x + 1) + 1, (y + 1) + 0) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_21 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -2 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : (y - x - (2 * (k : ℤ) + 4)) ≤ 1)
    (_c4 : 0 ≤ (y - x - (2 * (k : ℤ) + 4))) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y) := by
    unfold SqCorner
    exact Or.inl rfl
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd] at he ⊢
      first
      | (refine Or.inl (Or.inr (Or.inr ?_)); omega)
      | (refine Or.inr (Or.inr (Or.inl ?_)); omega)
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inr (Or.inr ?_))
    simp only [CandW]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (-1, 0) := by
    exact candDisp_W (by simp only [CandW]; omega)
  have hout : SqOut (x, y) ((x) + -1, (y) + 0) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_22 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -2 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : 2 ≤ (y - x - (2 * (k : ℤ) + 4))) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_high_down (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_26 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : -1 ≤ (y - 2 * (2 * (k : ℤ) + 4)))
    (_c2 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -1)
    (_c3 : (x - (2 * (k : ℤ) + 4)) ≤ -1)
    (_c4 : (x - (2 * (k : ℤ) + 4)) ≤ -2) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inl rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y + 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_high_up (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_28 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : -1 ≤ (y - 2 * (2 * (k : ℤ) + 4)))
    (_c2 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -1)
    (_c3 : (x - (2 * (k : ℤ) + 4)) ≤ -1)
    (_c4 : -1 ≤ (x - (2 * (k : ℤ) + 4)))
    (_c5 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -3) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inl rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y + 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_high_up (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_31 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 0)
    (_c1 : -1 ≤ (y - 2 * (2 * (k : ℤ) + 4)))
    (_c2 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -1)
    (_c3 : 0 ≤ (x - (2 * (k : ℤ) + 4)))
    (_c4 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -3) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨1, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 1 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 1 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_high_down (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_42 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c3 : (y - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c4 : 1 ≤ x)
    (_c5 : (x - (2 * (k : ℤ) + 4)) ≤ 0)
    (_c6 : 1 ≤ y) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y) := by
    unfold SqCorner
    exact Or.inl rfl
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_low_down (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_45 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c3 : -1 ≤ (y - (2 * (k : ℤ) + 4)))
    (_c4 : (x - (2 * (k : ℤ) + 4)) ≤ -1) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inr rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y + 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inl ?_
    simp only [CandLow]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_low_up (by simp only [CandLow]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_49 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -1 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : (y - x - (2 * (k : ℤ) + 4)) ≤ 0)
    (_c4 : x ≤ 0) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inl rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y + 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd] at he ⊢
      first
      | (refine Or.inl (Or.inr (Or.inr ?_)); omega)
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inr (Or.inr ?_))
    simp only [CandW]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (-1, 0) := by
    exact candDisp_W (by simp only [CandW]; omega)
  have hout : SqOut (x, y) ((x) + -1, (y + 1) + 0) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_50 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -1 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : (y - x - (2 * (k : ℤ) + 4)) ≤ 0)
    (_c4 : 1 ≤ x) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y) := by
    unfold SqCorner
    exact Or.inr (Or.inl rfl)
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
    · refine Or.inr ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddOddWhite, LadderOddLowerBoundary, reflectLadderOdd] at he ⊢
      first
      | (refine Or.inr (Or.inl (Or.inr (Or.inr ?_))); omega)
      | (refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); omega)
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inr (Or.inl ?_))
    simp only [CandE]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (1, 0) := by
    exact candDisp_E (by simp only [CandE]; omega)
  have hout : SqOut (x, y) ((x + 1) + 1, (y) + 0) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_53 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2)
    (_c2 : -1 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c3 : 1 ≤ (y - x - (2 * (k : ℤ) + 4)))
    (_c4 : 0 ≤ x) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x, y) := by
    unfold SqCorner
    exact Or.inl rfl
  have hw : AliasOf (2 * (k : ℤ) + 4) (x, y) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, -1) := by
    exact candDisp_high_down (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x) + 0, (y) + -1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_57 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : -1 ≤ (y - 2 * (2 * (k : ℤ) + 4)))
    (_c2 : (x - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c3 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ 0)
    (_c4 : (x - (2 * (k : ℤ) + 4)) ≤ -3) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inr rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y + 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_high_up (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

set_option maxHeartbeats 400000 in
theorem sq_leaf_59 (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (x y : ℤ) (_hu : NativeT (2 * (k : ℤ) + 4) x y)
    (_c0 : (x + y) % 2 = 1)
    (_c1 : -1 ≤ (y - 2 * (2 * (k : ℤ) + 4)))
    (_c2 : (x - (2 * (k : ℤ) + 4)) ≤ -2)
    (_c3 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ 0)
    (_c4 : -2 ≤ (x - (2 * (k : ℤ) + 4)))
    (_c5 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -2) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  have ha : 4 ≤ 2 * (k : ℤ) + 4 := by omega
  simp only [NativeT] at _hu
  have hv : SqCorner (x, y) (x + 1, y + 1) := by
    unfold SqCorner
    exact Or.inr (Or.inr (Or.inr rfl))
  have hw : AliasOf (2 * (k : ℤ) + 4) (x + 1, y + 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) :=
    ⟨0, 0, by ext <;> simp⟩
  have hwn : NativeT (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    simp only [NativeT]
    omega
  have hcharge : (EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
      ¬ LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) ∨
      (¬ EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0)) ∧
        LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))) := by
    by_cases he : EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0, (y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0))
    · refine Or.inl ⟨he, ?_⟩
      rw [quarterTurn_offset_apply] at he ⊢
      simp only [EvenSite, LadderOddEvenBlack] at he ⊢
      omega
    · exfalso
      rw [quarterTurn_offset_apply] at he
      simp only [EvenSite] at he
      omega
  have hlap := lap_zero_of_charge hagree hperiod hw hwn hcharge
  have ht : ¬ (FreeSite (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) + 2) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - 2 * (2 * (k : ℤ) + 4)) ∨
      FreeSite (2 * (k : ℤ) + 4) (((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) - ((2 * (k : ℤ) + 4) + 1)) (((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) - ((2 * (k : ℤ) + 4) - 1))) := by
    intro h
    rcases h with h | h | h <;> simp only [FreeSite, FreeHSite, FreeVSite] at h <;> omega
  have hnf := nonfree_of_native_test ha hw hwn ht
  have hg : CandGuard (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) := by
    refine Or.inr (Or.inl ?_)
    simp only [CandHigh]
    omega
  have hd : candDisp (2 * (k : ℤ) + 4) ((x + 1) - 0 * ((2 * (k : ℤ) + 4) + 1) + 2 * 0) ((y + 1) - 0 * ((2 * (k : ℤ) + 4) - 1) - 2 * (2 * (k : ℤ) + 4) * 0) = (0, 1) := by
    exact candDisp_high_up (by simp only [CandHigh]; omega) (by omega)
  have hout : SqOut (x, y) ((x + 1) + 0, (y + 1) + 1) := by
    unfold SqOut
    dsimp only
    simp only [ne_eq, Prod.mk.injEq]
    omega
  exact sq_of_witness hv hlap hnf hw hwn hg (by rw [hd]; exact hout)

end FLatticePaper.TwosEPolicy
