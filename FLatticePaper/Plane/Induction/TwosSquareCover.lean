import FLatticePaper.Plane.Induction.TwosSquareLeaves

namespace FLatticePaper.TwosEPolicy
open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

set_option maxHeartbeats 400000 in
theorem sq_clause_native (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (η : ℤ) (hη : η = 1 ∨ η = -1) (x y : ℤ) (hu : NativeT (2 * (k : ℤ) + 4) x y) :
    SqClause (2 * (k : ℤ) + 4) η (standardField (List.replicate (k + 1) Digit.two)) (x, y) := by
  by_cases h0 : (x + y) % 2 = 0
  · by_cases h1 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2
    · by_cases h2 : (y - x - (2 * (k : ℤ) + 4)) ≤ -3
      · by_cases h3 : (y - (2 * (k : ℤ) + 4)) ≤ -2
        · by_cases h4 : (y - x) ≤ -1
          · by_cases h5 : (x - (2 * (k : ℤ) + 4)) ≤ -1
            · exact sq_leaf_6 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_7 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h8 : y ≤ 0
            · exact sq_leaf_9 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_10 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases h11 : (x - (2 * (k : ℤ) + 4)) ≤ 0
          · exact sq_leaf_12 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h13 : (y - x) ≤ -1
            · exact sq_leaf_14 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_15 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases h16 : (y - x - (2 * (k : ℤ) + 4)) ≤ 1
        · by_cases h17 : (y - x - (2 * (k : ℤ) + 4)) ≤ -1
          · by_cases h18 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -4
            · by_cases h19 : (y - (2 * (k : ℤ) + 4)) ≤ -2
              · exact sq_leaf_20 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact sq_leaf_21 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · by_cases h22 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -3
              · exact sq_leaf_23 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact sq_leaf_24 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h25 : x ≤ 0
            · exact sq_leaf_26 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_27 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · exact sq_leaf_28 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega)
    · by_cases h29 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -1
      · by_cases h30 : (x - (2 * (k : ℤ) + 4)) ≤ -1
        · by_cases h31 : (x - (2 * (k : ℤ) + 4)) ≤ -2
          · exact sq_leaf_32 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h33 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -3
            · exact sq_leaf_34 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_35 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases h36 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -3
          · exact sq_leaf_37 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact sq_leaf_38 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases h39 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -1
        · exact sq_leaf_40 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega)
        · by_cases h41 : (x - (2 * (k : ℤ) + 4)) ≤ -3
          · exact sq_leaf_42 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact sq_leaf_43 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
  · by_cases h44 : (x - (2 * (k : ℤ) + 4)) ≤ -2
    · by_cases h45 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -2
      · by_cases h46 : (y - x - (2 * (k : ℤ) + 4)) ≤ -2
        · by_cases h47 : (y - (2 * (k : ℤ) + 4)) ≤ -2
          · by_cases h48 : x ≤ 0
            · exact sq_leaf_49 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · by_cases h50 : y ≤ 0
              · exact sq_leaf_51 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              · exact sq_leaf_52 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact sq_leaf_53 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases h54 : (y - x - (2 * (k : ℤ) + 4)) ≤ 0
          · by_cases h55 : x ≤ 0
            · exact sq_leaf_56 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_57 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h58 : x ≤ -1
            · exact sq_leaf_59 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_60 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases h61 : x ≤ -1
        · exact sq_leaf_62 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega)
        · by_cases h63 : (x - (2 * (k : ℤ) + 4)) ≤ -3
          · exact sq_leaf_64 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h65 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -2
            · exact sq_leaf_66 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_67 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases h68 : (y - 2 * (2 * (k : ℤ) + 4)) ≤ -4
      · by_cases h69 : (x - (2 * (k : ℤ) + 4)) ≤ -1
        · by_cases h70 : (y - x) ≤ 0
          · exact sq_leaf_71 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact sq_leaf_72 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases h73 : (x - (2 * (k : ℤ) + 4)) ≤ 0
          · by_cases h74 : (y - x) ≤ 0
            · exact sq_leaf_75 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_76 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h77 : (y - (2 * (k : ℤ) + 4)) ≤ -1
            · exact sq_leaf_78 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_79 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases h80 : (x - (2 * (k : ℤ) + 4)) ≤ -1
        · by_cases h81 : (y - x - (2 * (k : ℤ) + 4)) ≤ 0
          · exact sq_leaf_82 k hagree hperiod η x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · by_cases h83 : (y - x - 2 * (2 * (k : ℤ) + 4)) ≤ -2
            · exact sq_leaf_84 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            · exact sq_leaf_85 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · by_cases h86 : (y - x - (2 * (k : ℤ) + 4)) ≤ -2
          · exact sq_leaf_87 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact sq_leaf_88 k hagree hperiod η hη x y hu (by omega) (by omega) (by omega) (by omega) (by omega)
end FLatticePaper.TwosEPolicy
