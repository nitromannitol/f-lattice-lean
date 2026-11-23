import FLatticePaper.Plane.Induction.W1OddZero
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TieReduce

/-! # Task 74 (odd_zero): the seed value from the two sheet offers at `Y = Z z + U`

For the fixer's seed `z` (on the odd line of `odd_zero`), the point `Y = Z z + U` (`U` the kernel of the child) lies in the closed polygon
`E` (checked numerically; the membership is the next step). On `E` the field is the sheet minimum (`standardField_eq_sheetMin_of_strong`), and
the kernel period makes `F(Z z) = F(Y)`. So if both sheets take the value `−h₀(z)` at `Y`, the quarter turn vanishes at `z`:
`quarterTurnField F z = F(Z z) − h₀(Z z) = −h₀(z) − (−h₀(z)) = 0`. The two sheet values are the transported offers (task 74, step 2). -/

namespace FLatticePaper.W1OddSeedZero

open Farey FLatticePaper FLatticePaper.Induction

/-- `h₀(Z x) = −h₀(x)` for the quarter turn `Z x = (−x₂, x₁ − 1)`. -/
theorem harmonicGrid_quarter_neg (x : Site) : harmonicGrid (-x.2, x.1 - 1) = -harmonicGrid x := by
  have e1 := harmonicGrid_exact (-x.2, x.1 - 1)
  have e0 := harmonicGrid_exact x
  have hp1 : (-x.2 + (x.1 - 1)) % 2 = 1 - (x.1 + x.2) % 2 := by omega
  have e1' : 4 * harmonicGrid (-x.2, x.1 - 1) =
      (-x.2) ^ 2 + 2 * (-x.2) * (x.1 - 1) - (x.1 - 1) ^ 2 - 2 * (x.1 - 1) - (-x.2 + (x.1 - 1)) % 2 := e1
  rw [hp1] at e1'
  have key : 4 * (harmonicGrid (-x.2, x.1 - 1) + harmonicGrid x) = 0 := by
    linear_combination e1' + e0
  exact (by linarith [key] : harmonicGrid (-x.2, x.1 - 1) = -harmonicGrid x)

/-- **The seed value from the two offers**: if the two sheets of `word` take the value `−h₀(z)` at `Y = Z z + U` (in `E`), then the
quarter turn of the standard field of `word` vanishes at `z`. -/
theorem seed_zero_of_offers {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) (z : Site)
    (hY : (-z.2, z.1 - 1) + (frameAt word).child.modifiedDeck.kernel ∈ (frameAt word).closedPolygon)
    (hA : (frameAt word).sheetA (quarterTurnField (standardField (conjWord word)))
        ((-z.2, z.1 - 1) + (frameAt word).child.modifiedDeck.kernel) = -harmonicGrid z)
    (hC : (frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
        ((-z.2, z.1 - 1) + (frameAt word).child.modifiedDeck.kernel) = -harmonicGrid z) :
    quarterTurnField (standardField word) z = 0 := by
  have hpk := packet_of_strong h hS
  have hper := FLatticePaper.W1VShift.packet_U_zsmul (frameAt word) hpk (-z.2, z.1 - 1) 1
  rw [one_smul] at hper
  have hF := standardField_eq_sheetMin_of_strong h hS hY
  have hsheet : (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))
      ((-z.2, z.1 - 1) + (frameAt word).child.modifiedDeck.kernel) = -harmonicGrid z := by
    unfold ChildFrame.sheetMin
    rw [hA, hC, min_self]
  have hFZ : standardField word (-z.2, z.1 - 1) = -harmonicGrid z := by
    rw [← hper, hF, hsheet]
  rw [FLatticePaper.W1ZeroStrip.quarterTurn_eq_sub, hFZ, harmonicGrid_quarter_neg]
  ring

end FLatticePaper.W1OddSeedZero
