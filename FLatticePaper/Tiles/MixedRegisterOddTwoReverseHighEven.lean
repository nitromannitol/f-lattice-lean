import FLatticePaper.Tiles.CorrectedMixedDiagram
import Mathlib.Tactic.ClearExcept

/-! The odd mixed alternate diagram, with prefix letter 2, previous sign 1,
sector 2, and even physical parity. -/

namespace FLatticePaper.Tiles.MixedRegisterOddTwoReverseHighEven

open FLatticePaper.Farey CorrectedLevelTests CorrectedRegisterDiagram CorrectedMixedDiagram Lean

private abbrev Piece (r : Register) (i : ℕ) := mixed r false 1 false i

local macro "close_register" "[" xs:term,* "]" : tactic => do
  let facts := xs.getElems
  let names := facts.mapIdx fun i _ => mkIdent (Name.mkSimple s!"rowFact{i}")
  let steps ← (names.zip facts).mapM fun (n,f) => `(tactic| have $n := $f)
  `(tactic| (
    $[$steps:tactic]*
    clear * - $names:ident*
    norm_num [Piece,mixed,Shape.probe,Shape.line,Probe.line,Line.fact,bias,displacement,
      orientation,oldOdd,oldEven,Fin.ext_iff,Prod.smul_mk,mulI] at $names:ident*
    all_goals omega))

private abbrev Pos (r : Register) (i : ℕ) := ∀ j, (Piece r i).bounds r false 2 j true
private abbrev Neg (r : Register) (i : ℕ) (j : Fin 4) := (Piece r i).bounds r false 2 j false
private abbrev Outside (r : Register) (i : ℕ) := Neg r i 0 ∨ Neg r i 1 ∨ Neg r i 2 ∨ Neg r i 3

private structure Hyp (r : Register) : Prop where
  regular : Regular r false 2
  multiple : r.M ∣ r.S
  scaleRun : r.S=r.M
  lattice : ∀ i : Fin 10, (Piece r i.val).lattice r 1 false 2

private abbrev gap {r : Register} (h : Hyp r) (i : Fin 10) (j : Fin 4) (l a k : ℤ) :=
  Shape.gap (h.lattice i) (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j l a k

private abbrev gapS {r : Register} (h : Hyp r) (j k : ℤ) :=
  period_gap (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j k

private theorem cell0 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n30 : Neg r 3 0) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scaleParity, n10 5, n30 0, n40 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0]

private theorem cell1 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n30 : Neg r 3 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n11 0, n30 0]

private theorem cell2 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n30 : Neg r 3 0) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scaleParity, n12 5, n30 0, n40 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 1 0, p 2 0, p 2 3, p 2 4, p 3 0]

private theorem cell3 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n13 0, n30 0, p 0 5]

private theorem cell4 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenSector.2, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.2, n31 0, n40 0]

private theorem cell5 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scaleParity, n10 5, n10 6, n32 0, n40 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0]

private theorem cell6 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n50 : Neg r 5 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n11 0, n50 0]

private theorem cell7 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n51 : Neg r 5 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n40 0, n51 0]

private theorem cell8 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n11 0, n52 0, p 2 5]

private theorem cell9 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n53 : Neg r 5 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n11 0, n32 0, n40 0, n53 0, p 3 0]

private theorem cell10 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n40 : Neg r 4 0) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddY, h.regular.scaleParity, n12 5, n12 6, n40 0, n50 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 2 4, p 2 5]

private theorem cell11 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scaleParity, n12 5, n32 0, n40 0, n52 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 1 0, p 2 0, p 2 3, p 2 4, p 2 5]

private theorem cell12 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n53 : Neg r 5 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n12 0, n53 0, p 3 0]

private theorem cell13 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n32 : Neg r 3 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n13 0, n32 0]

private theorem cell14 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n33 0, n40 0, p 1 0, p 3 4]

private theorem cell15 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n41 0, p 1 0]

private theorem cell16 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n30 : Neg r 3 0) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n10 5, n30 0, n42 0, p 0 4, p 0 5, p 2 0]

private theorem cell17 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n50 : Neg r 5 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n31 0, n50 0]

private theorem cell18 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n32 : Neg r 3 2) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, h.regular.oddY, n10 5, n10 6, n32 0, n42 0, p 0 4, p 0 5, p 2 0]

private theorem cell19 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n33 0, n42 0, p 2 0]

private theorem cell20 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n12 5, n12 6, n42 0, n50 0, p 0 4, p 1 0, p 2 0, p 2 1, p 2 2, p 2 3, p 2 4, p 2 5, p 3 0]

private theorem cell21 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n33 : Neg r 3 3) (n42 : Neg r 4 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n13 0, n33 0, n42 0]

private theorem cell22 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n51 : Neg r 5 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n42 0, n51 0, p 0 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 3 0]

private theorem cell23 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n42 : Neg r 4 2) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n10 5, n42 0, n52 0, p 0 4, p 2 0]

private theorem cell24 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n42 : Neg r 4 2) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n12 0, n12 5, n42 0, n52 0, p 0 1, p 0 4, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 3, p 2 4, p 2 5]

private theorem cell25 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n42 : Neg r 4 2) (n52 : Neg r 5 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n13 0, n42 0, n52 0]

private theorem cell26 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n53 : Neg r 5 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n42 0, n53 0]

private theorem cell27 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n43 0, p 3 0]

private theorem cell28 {r : Register} (h : Hyp r) (n30 : Neg r 3 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n30 0, p 0 0, p 1 0]

private theorem cell29 {r : Register} (h : Hyp r) (n51 : Neg r 5 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n51 0, n60 0]

private theorem cell30 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n61 : Neg r 6 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n20 0, n61 0]

private theorem cell31 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n21 4, n51 0, n61 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell32 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n22 0, n61 0, p 1 4]

private theorem cell33 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, n23 4, n31 0, n51 0, n61 0, p 1 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 3]

private theorem cell34 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, n31 0, n51 0, n62 0, p 2 5]

private theorem cell35 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n31 0, n40 0]

private theorem cell36 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n41 : Neg r 4 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n20 0, n41 0]

private theorem cell37 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n51 : Neg r 5 1) (n63 : Neg r 6 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n20 0, n31 0, n42 0, n51 0, n63 0]

private theorem cell38 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n43 : Neg r 4 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n20 0, n43 0, p 3 4]

private theorem cell39 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, n21 4, n21 5, n51 0, n63 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell40 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n63 : Neg r 6 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n22 0, n63 0]

private theorem cell41 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, n23 4, n23 5, n41 0, n51 0, n63 0, p 1 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 2, p 3 3, p 3 4]

private theorem cell42 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n42 : Neg r 4 2) : False := by
  close_register [h.regular.num, h.regular.scale, n23 0, n42 0]

private theorem cell43 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n23 4, n31 0, n43 0, n51 0, n63 0, p 1 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 2, p 3 3, p 3 4]

private theorem cell44 {r : Register} (h : Hyp r) (n52 : Neg r 5 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n52 0, p 2 0]

private theorem cell45 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n41 0, n60 0]

private theorem cell46 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n21 4, n53 0, n61 0, p 1 3, p 1 4, p 3 0]

private theorem cell47 {r : Register} (h : Hyp r) (n53 : Neg r 5 3) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n53 0, n62 0, p 3 0]

private theorem cell48 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n21 4, n21 5, n53 0, n63 0, p 1 3, p 1 4, p 3 0]

private theorem cell49 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n53 : Neg r 5 3) (n62 : Neg r 6 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n22 0, n53 0, n62 0]

private theorem cell50 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n23 4, n23 5, n31 0, n41 0, n53 0, p 1 3, p 2 0, p 3 0, p 3 1, p 3 2, p 3 3, p 3 4]

private theorem cell51 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n43 : Neg r 4 3) (n53 : Neg r 5 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n21 4, n43 0, n53 0, p 1 3, p 3 0]

private theorem cell52 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n43 : Neg r 4 3) (n53 : Neg r 5 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, n22 0, n43 0, n53 0]

private theorem cell53 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n53 : Neg r 5 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n23 4, n31 0, n43 0, n53 0, p 1 3, p 2 0, p 3 0, p 3 1, p 3 2, p 3 3, p 3 4]

private theorem cell54 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n32 0, p 0 4, p 1 0, p 1 1, p 1 4, p 2 0, p 2 1, p 2 2, p 2 3, p 2 4, p 3 0]

private theorem cell55 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n20 0, n33 0, n40 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 3 0]

private theorem cell56 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n42 : Neg r 4 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n33 0, n42 0, p 3 0]

private theorem cell57 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n33 : Neg r 3 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.2, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n21 4, n21 5, n33 0, p 1 3, p 1 4, p 3 0]

private theorem cell58 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n33 : Neg r 3 3) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.2, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.2, n22 0, n33 0]

private theorem cell59 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n33 0, n40 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 3 0]

private theorem cell60 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n33 : Neg r 3 3) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n23 4, n23 5, n33 0, n41 0, p 0 0, p 1 1, p 1 2, p 1 3, p 2 0, p 3 0, p 3 1, p 3 2, p 3 3, p 3 4]

private theorem cell61 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n33 : Neg r 3 3) (n43 : Neg r 4 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n23 4, n33 0, n43 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 1 1, p 1 2, p 1 3, p 2 0, p 3 0, p 3 1, p 3 2, p 3 3, p 3 4]

private theorem cell62 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 1) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scale, n00 0, n00 5, n00 6, p 0 4, p 0 5, p 2 0, p 3 4]

private theorem cell63 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n01 0, p 0 0, p 1 0]

private theorem cell64 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 1) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scale, n02 0, n02 5, n02 6, p 0 4, p 1 0, p 1 1, p 1 2, p 1 4, p 2 0, p 2 4, p 2 5]

private theorem cell65 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n03 0, p 0 0, p 1 0, p 3 0]

private theorem cell66 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n90 0, p 0 0, p 1 0]

private theorem cell67 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 2) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.num, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scale, n91 0, n91 4, n91 5, p 1 3, p 1 4, p 2 5, p 3 0]

private theorem cell68 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.oddDiff, h.regular.oddSector.2, h.regular.oddSize, n92 0, p 0 0, p 1 0, p 2 0]

private theorem cell69 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 2) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, h.regular.scale, n93 0, n93 4, n93 5, p 0 5, p 1 3, p 3 0, p 3 3, p 3 4]

private theorem cell70 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 3) : False := by
  close_register [h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.2, n00 6, p 0 0, p 3 0]

private theorem cell71 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n01 0, p 1 0]

private theorem cell72 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n02 0, p 2 0]

private theorem cell73 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 3) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, n03 5, p 0 0, p 3 0]

private theorem cell74 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.2, n90 6, p 0 0, p 3 0]

private theorem cell75 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n91 0, p 1 0]

private theorem cell76 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n92 0, p 2 0]

private theorem cell77 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 4) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, n93 5, p 0 0, p 3 0]

private theorem cell78 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n00 0, p 0 0]

private theorem cell79 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 5) : False := by
  close_register [h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.2, n01 5, p 1 0, p 2 0]

private theorem cell80 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 5) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, n02 6, p 1 0, p 2 0]

private theorem cell81 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 5) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n03 0, p 3 0]

private theorem cell82 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 6) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n90 0, p 0 0]

private theorem cell83 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 6) : False := by
  close_register [h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.2, n91 5, p 1 0, p 2 0]

private theorem cell84 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 6) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, n92 6, p 1 0, p 2 0]

private theorem cell85 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 6) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.2, n93 0, p 3 0]

private theorem cover0 {r : Register} (h : Hyp r) (n30 : Neg r 3 0) (n40 : Neg r 4 0) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell0 h n10 n30 n40 p
  · exact cell1 h n11 n30
  · exact cell2 h n12 n30 n40 p
  · exact cell3 h n13 n30 p

private theorem cover1 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell6 h n11 n50
  · exact cell7 h n40 n51
  · exact cell8 h n11 n52 p
  · exact cell9 h n11 n32 n40 n53 p

private theorem cover2 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell10 h n12 n40 n50 p
  · exact cell7 h n40 n51
  · exact cell11 h n12 n32 n40 n52 p
  · exact cell12 h n12 n53 p

private theorem cover3 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o1 : Outside r 1) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell5 h n10 n32 n40 p
  · exact cover1 h n11 n32 n40 o5 p
  · exact cover2 h n12 n32 n40 o5 p
  · exact cell13 h n13 n32

private theorem cover4 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (o1 : Outside r 1) (o3 : Outside r 3) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cover0 h n30 n40 o1 p
  · exact cell4 h n31 n40
  · exact cover3 h n32 n40 o1 o5 p
  · exact cell14 h n33 n40 p

private theorem cover5 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell16 h n10 n30 n42 p
  · exact cell17 h n31 n50
  · exact cell18 h n10 n32 n42 p
  · exact cell19 h n33 n42 p

private theorem cover6 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell3 h n13 n30 p
  · exact cell17 h n31 n50
  · exact cell13 h n13 n32
  · exact cell21 h n13 n33 n42

private theorem cover7 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (o1 : Outside r 1) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cover5 h n10 n42 n50 o3 p
  · exact cell6 h n11 n50
  · exact cell20 h n12 n42 n50 p
  · exact cover6 h n13 n42 n50 o3 p

private theorem cover8 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n52 : Neg r 5 2) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell23 h n10 n42 n52 p
  · exact cell8 h n11 n52 p
  · exact cell24 h n12 n42 n52 p
  · exact cell25 h n13 n42 n52

private theorem cover9 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (o1 : Outside r 1) (o3 : Outside r 3) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cover7 h n42 n50 o1 o3 p
  · exact cell22 h n42 n51 p
  · exact cover8 h n42 n52 o1 p
  · exact cell26 h n42 n53

private theorem cover10 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover4 h n40 o1 o3 o5 p
  · exact cell15 h n41 p
  · exact cover9 h n42 o1 o3 o5 p
  · exact cell27 h n43 p

private theorem cover11 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell30 h n20 n61
  · exact cell31 h n21 n51 n61 p
  · exact cell32 h n22 n61 p
  · exact cell33 h n23 n31 n51 n61 p

private theorem cover12 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell35 h n31 n40
  · exact cell36 h n20 n41
  · exact cell37 h n20 n31 n42 n51 n63
  · exact cell38 h n20 n43 p

private theorem cover13 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell35 h n31 n40
  · exact cell41 h n23 n41 n51 n63 p
  · exact cell42 h n23 n42
  · exact cell43 h n23 n31 n43 n51 n63 p

private theorem cover14 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (o2 : Outside r 2) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover12 h n20 n31 n51 n63 o4 p
  · exact cell39 h n21 n51 n63 p
  · exact cell40 h n22 n63
  · exact cover13 h n23 n31 n51 n63 o4 p

private theorem cover15 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n51 : Neg r 5 1) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell29 h n51 n60
  · exact cover11 h n31 n51 n61 o2 p
  · exact cell34 h n31 n51 n62 p
  · exact cover14 h n31 n51 n63 o2 o4 p

private theorem cover16 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell45 h n41 n60
  · exact cell46 h n21 n53 n61 p
  · exact cell47 h n53 n62 p
  · exact cell48 h n21 n53 n63 p

private theorem cover17 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell45 h n41 n60
  · exact cell32 h n22 n61 p
  · exact cell49 h n22 n53 n62
  · exact cell40 h n22 n63

private theorem cover18 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell36 h n20 n41
  · exact cover16 h n21 n41 n53 o6 p
  · exact cover17 h n22 n41 n53 o6 p
  · exact cell50 h n23 n31 n41 n53 p

private theorem cover19 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n53 : Neg r 5 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell38 h n20 n43 p
  · exact cell51 h n21 n43 n53 p
  · exact cell52 h n22 n43 n53
  · exact cell53 h n23 n31 n43 n53 p

private theorem cover20 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n53 : Neg r 5 3) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell35 h n31 n40
  · exact cover18 h n31 n41 n53 o2 o6 p
  · exact cell26 h n42 n53
  · exact cover19 h n31 n43 n53 o2 p

private theorem cover21 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell17 h n31 n50
  · exact cover15 h n31 n51 o2 o4 o6 p
  · exact cell44 h n52 p
  · exact cover20 h n31 n53 o2 o4 o6 p

private theorem cover22 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n33 : Neg r 3 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell55 h n20 n33 n40 p
  · exact cell36 h n20 n41
  · exact cell56 h n33 n42 p
  · exact cell38 h n20 n43 p

private theorem cover23 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n33 : Neg r 3 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell59 h n33 n40 p
  · exact cell60 h n23 n33 n41 p
  · exact cell56 h n33 n42 p
  · exact cell61 h n23 n33 n43 p

private theorem cover24 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (o2 : Outside r 2) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover22 h n20 n33 o4 p
  · exact cell57 h n21 n33 p
  · exact cell58 h n22 n33
  · exact cover23 h n23 n33 o4 p

private theorem cover25 {r : Register} (h : Hyp r) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell28 h n30 p
  · exact cover21 h n31 o2 o4 o5 o6 p
  · exact cell54 h n32 p
  · exact cover24 h n33 o2 o4 p

private theorem cover26 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 1) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell62 h n00 p
  · exact cell63 h n01 p
  · exact cell64 h n02 p
  · exact cell65 h n03 p

private theorem cover27 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 2) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell66 h n90 p
  · exact cell67 h n91 p
  · exact cell68 h n92 p
  · exact cell69 h n93 p

private theorem cover28 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 3) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell70 h n00 p
  · exact cell71 h n01 p
  · exact cell72 h n02 p
  · exact cell73 h n03 p

private theorem cover29 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell74 h n90 p
  · exact cell75 h n91 p
  · exact cell76 h n92 p
  · exact cell77 h n93 p

private theorem cover30 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 5) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell78 h n00 p
  · exact cell79 h n01 p
  · exact cell80 h n02 p
  · exact cell81 h n03 p

private theorem cover31 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell82 h n90 p
  · exact cell83 h n91 p
  · exact cell84 h n92 p
  · exact cell85 h n93 p

private theorem valid {r : Register} (h : Regular r false 2) (i : Fin 10) (j : Fin 4) :
    ((Piece r i.val).line r false 2 j).valid := by
  have a := h.scale
  have b := h.oddSize
  have c := h.evenSize
  have d := h.run
  have n := h.num
  have g := h.den
  fin_cases i <;> fin_cases j <;>
    norm_num [Piece,mixed,Shape.line,Shape.probe,Probe.line,Line.valid,orientation,
      Prod.smul_mk,Fin.ext_iff] at * <;> omega

private theorem inclusion0 {r : Register} (h : Hyp r) (yes : (Piece r 0).contains r false 2) :
    (Piece r 1).contains r false 2 ∨ (Piece r 2).contains r false 2 ∨ (Piece r 3).contains r false 2 ∨ (Piece r 4).contains r false 2 ∨ (Piece r 5).contains r false 2 ∨ (Piece r 6).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 0) r false 2 (valid h.regular 0) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover10 h (outside 1 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) p

private theorem inclusion1 {r : Register} (h : Hyp r) (yes : (Piece r 1).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 1) r false 2 (valid h.regular 1) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover26 h (outside 0 (by tauto)) p

private theorem inclusion2 {r : Register} (h : Hyp r) (yes : (Piece r 2).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 2) r false 2 (valid h.regular 2) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover27 h (outside 9 (by tauto)) p

private theorem inclusion3 {r : Register} (h : Hyp r) (yes : (Piece r 3).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 3) r false 2 (valid h.regular 3) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover28 h (outside 0 (by tauto)) p

private theorem inclusion4 {r : Register} (h : Hyp r) (yes : (Piece r 4).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 4) r false 2 (valid h.regular 4) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover29 h (outside 9 (by tauto)) p

private theorem inclusion5 {r : Register} (h : Hyp r) (yes : (Piece r 5).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 5) r false 2 (valid h.regular 5) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover30 h (outside 0 (by tauto)) p

private theorem inclusion6 {r : Register} (h : Hyp r) (yes : (Piece r 6).contains r false 2) :
    (Piece r 0).contains r false 2 ∨ (Piece r 9).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 6) r false 2 (valid h.regular 6) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover31 h (outside 9 (by tauto)) p

private theorem inclusion9 {r : Register} (h : Hyp r) (yes : (Piece r 9).contains r false 2) :
    (Piece r 1).contains r false 2 ∨ (Piece r 2).contains r false 2 ∨ (Piece r 3).contains r false 2 ∨ (Piece r 4).contains r false 2 ∨ (Piece r 5).contains r false 2 ∨ (Piece r 6).contains r false 2 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 9) r false 2 (valid h.regular 9) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 2) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover25 h (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 6 (by tauto)) p

/-- At an admissible register the target and the union of the component polygons contain the same site. -/
theorem coverage (r : Register) (regular : Regular r false 2) (multiple : r.M ∣ r.S) (scaleRun : r.S=r.M)
    (lattice : ∀ i : Fin 10, (mixed r false 1 false i.val).lattice r 1 false 2) :
    ((mixed r false 1 false 0).contains r false 2 ∨ (mixed r false 1 false 9).contains r false 2) ↔ ∃ i : Fin 6, (mixed r false 1 false (i.val+1)).contains r false 2 := by
  let h : Hyp r := ⟨regular,multiple,scaleRun,lattice⟩
  constructor
  · intro p
    have hit := p.elim (inclusion0 h) (inclusion9 h)
    rcases hit with h | h | h | h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
    · exact ⟨5,h⟩
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact inclusion1 h hi
    · exact inclusion2 h hi
    · exact inclusion3 h hi
    · exact inclusion4 h hi
    · exact inclusion5 h hi
    · exact inclusion6 h hi

end FLatticePaper.Tiles.MixedRegisterOddTwoReverseHighEven
