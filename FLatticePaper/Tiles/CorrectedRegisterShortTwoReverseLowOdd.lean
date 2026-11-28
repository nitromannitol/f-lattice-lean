import FLatticePaper.Tiles.CorrectedRegisterDiagram
import Mathlib.Tactic.ClearExcept

/-! The ordinary corrected diagram, with prefix letter 2, previous sign 1,
sector 0, and odd physical parity. -/

namespace FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseLowOdd

open FLatticePaper.Farey CorrectedLevelTests CorrectedRegisterDiagram Lean

private abbrev Piece (r : Register) (i : ℕ) := corrected r false 1 false i

local macro "close_register" "[" xs:term,* "]" : tactic => do
  let facts := xs.getElems
  let names := facts.mapIdx fun i _ => mkIdent (Name.mkSimple s!"rowFact{i}")
  let steps ← (names.zip facts).mapM fun (n,f) => `(tactic| have $n := $f)
  `(tactic| (
    $[$steps:tactic]*
    clear * - $names:ident*
    norm_num [Piece,corrected,Shape.probe,Shape.line,Probe.line,Line.fact,bias,displacement,
      orientation,oldOdd,oldEven,Fin.ext_iff,Prod.smul_mk,mulI] at $names:ident*
    all_goals omega))

private abbrev Pos (r : Register) (i : ℕ) := ∀ j, (Piece r i).bounds r true 0 j true
private abbrev Neg (r : Register) (i : ℕ) (j : Fin 4) := (Piece r i).bounds r true 0 j false
private abbrev Outside (r : Register) (i : ℕ) := Neg r i 0 ∨ Neg r i 1 ∨ Neg r i 2 ∨ Neg r i 3

private structure Hyp (r : Register) : Prop where
  regular : Regular r false 0
  multiple : r.M ∣ r.S
  lattice : ∀ i : Fin 9, (Piece r i.val).lattice r 1 true 0

private abbrev gap {r : Register} (h : Hyp r) (i : Fin 9) (j : Fin 4) (l a k : ℤ) :=
  Shape.gap (h.lattice i) (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j l a k

private abbrev gapS {r : Register} (h : Hyp r) (j k : ℤ) :=
  period_gap (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j k

private theorem cell0 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 5 0 0 0 0, n20 6, n30 0, p 0 4, p 0 5, p 0 6, p 2 0, p 2 5]

private theorem cell1 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, h.regular.run, n21 0, n30 0, p 2 0, p 3 0]

private theorem cell2 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, n22 6, n30 0, p 0 4, p 2 0, p 2 5, p 3 0]

private theorem cell3 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddX, h.regular.run, h.regular.scale, gap h 5 0 0 0 0, n23 0, n23 6, n30 0, p 0 5, p 0 6, p 3 0]

private theorem cell4 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n31 : Neg r 3 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddDiff, n10 0, n31 0]

private theorem cell5 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.den, h.regular.scale, n11 0, n40 0]

private theorem cell6 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.num, h.regular.scale, gap h 1 1 0 (-1) 0, n11 5, n31 0, n41 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 4]

private theorem cell7 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.num, h.regular.scale, n31 0, n42 0, p 2 5]

private theorem cell8 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, gap h 1 1 0 (-1) 0, n11 5, n11 6, n31 0, n43 0, p 1 0, p 1 1, p 1 2, p 1 3, p 2 0, p 3 0, p 3 4]

private theorem cell9 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDiff, h.regular.oddSector.1, h.regular.oddY, n31 0, n80 0]

private theorem cell10 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n40 0, n81 0]

private theorem cell11 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n81 : Neg r 8 1) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSize, h.regular.run, h.regular.scale, h.regular.scaleParity, gap h 1 1 0 (-1) 0, n12 0, n12 7, n31 0, n41 0, n81 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell12 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n43 : Neg r 4 3) (n60 : Neg r 6 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n12 0, n12 6, n43 0, n60 0, n81 6]

private theorem cell13 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n61 : Neg r 6 1) (n81 : Neg r 8 1) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, gap h 1 1 0 (-1) 0, gap h 4 1 0 0 1, n12 0, n12 7, n31 0, n43 0, n61 5, n61 6, n81 0, p 1 0, p 1 1, p 1 2, p 1 3]

private theorem cell14 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n62 : Neg r 6 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, n43 0, n62 0]

private theorem cell15 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n63 : Neg r 6 3) (n81 : Neg r 8 1) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scale, n12 0, n12 7, n31 0, n43 0, n63 0, n63 5, n63 6, n81 0, n81 6, p 1 0, p 1 1, p 1 2, p 1 3]

private theorem cell16 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n31 0, n70 0]

private theorem cell17 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddDiff, n40 0, n71 0]

private theorem cell18 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) : False := by
  close_register [h.regular.den, h.regular.scale, n20 0, n31 0]

private theorem cell19 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenDiff, h.regular.oddSector.1, h.regular.oddY, n21 0, n40 0]

private theorem cell20 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.scale, gap h 4 2 0 0 0, n22 6, n22 7, n31 0, n40 0, n82 0, p 2 5]

private theorem cell21 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n72 : Neg r 7 2) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, n23 0, n23 5, n31 0, n72 0, n82 0]

private theorem cell22 {r : Register} (h : Hyp r) (n73 : Neg r 7 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n73 0, n82 0]

private theorem cell23 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n41 0, n82 0, p 1 4]

private theorem cell24 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n43 0, n82 0]

private theorem cell25 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n83 : Neg r 8 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, n12 0, n12 6, n12 7, n31 0, n83 0, p 1 1, p 1 2, p 1 3, p 3 0]

private theorem cell26 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scale, gap h 3 3 0 0 0, n13 5, n13 6, n31 0, p 1 0, p 1 1, p 1 2, p 2 0, p 3 0, p 3 4]

private theorem cell27 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, gap h 5 0 0 0 0, n20 6, n20 7, n32 0, n40 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0, p 2 5, p 3 0]

private theorem cell28 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.den, h.regular.run, h.regular.scale, n21 0, n70 0]

private theorem cell29 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scale, n22 6, n32 0, n40 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 2 5]

private theorem cell30 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n50 : Neg r 5 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, gap h 3 0 0 0 0, gap h 5 0 0 0 0, n23 0, n23 6, n32 0, n40 0, n50 6, n50 7, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5]

private theorem cell31 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n51 : Neg r 5 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, n23 0, n51 0, n70 5]

private theorem cell32 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n40 : Neg r 4 0) (n52 : Neg r 5 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, n23 0, n23 6, n40 0, n52 0, n52 6, n52 7, n70 0, n70 5, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5]

private theorem cell33 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n53 : Neg r 5 3) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scale, n23 0, n32 0, n40 0, n53 0, n53 5, n53 6, n70 0, n70 5, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0]

private theorem cell34 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, gap h 5 0 0 0 0, n20 6, n20 7, n32 0, n40 0, n72 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0, p 2 5, p 3 0]

private theorem cell35 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scale, gap h 4 2 0 0 0, n22 6, n22 7, n40 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 2 5, p 3 0]

private theorem cell36 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, h.regular.scale, n23 0, n23 5, n23 6, n32 0, n40 0, n72 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5]

private theorem cell37 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n32 0, n73 0]

private theorem cell38 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n32 0, n41 0, p 1 4]

private theorem cell39 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenX, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddY, h.regular.run, h.regular.scale, n32 0, n42 0, p 0 4, p 2 0, p 2 5]

private theorem cell40 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n43 : Neg r 4 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n32 0, n43 0]

private theorem cell41 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSize, h.regular.oddY, h.regular.run, n33 0, p 0 7, p 1 0, p 1 1, p 1 2, p 3 0, p 3 4]

private theorem cell42 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n00 0, p 0 0]

private theorem cell43 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 1) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, n01 0, n01 4, p 1 3, p 1 4, p 2 6, p 3 0, p 3 4]

private theorem cell44 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n02 0, p 2 0, p 3 0]

private theorem cell45 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 1) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, n03 0, n03 5, p 0 6, p 1 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 4]

private theorem cell46 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 2) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, n00 0, n00 6, p 0 4, p 0 5, p 2 0, p 2 5, p 3 5]

private theorem cell47 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n01 0, p 1 0]

private theorem cell48 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 2) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, n02 0, n02 6, p 0 4, p 1 5, p 2 0, p 2 5]

private theorem cell49 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n03 0, p 2 0, p 3 0]

private theorem cell50 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 3) : False := by
  close_register [h.regular.evenSize, h.regular.evenY, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 3 0 0 1 1, n00 7, n00 8, p 0 0, p 2 0, p 3 0]

private theorem cell51 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, n01 0, p 1 0, p 2 0, p 3 0]

private theorem cell52 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, n02 0, p 2 0, p 3 0]

private theorem cell53 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 3 0 0 1 1, gap h 3 3 0 (-1) 0, n03 5, n03 6, p 0 0, p 2 0, p 3 0]

private theorem cell54 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell55 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 4 1 0 (-1) 0, gap h 4 2 0 1 0, n01 5, n01 6, p 1 0, p 2 0, p 3 0]

private theorem cell56 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenSize, h.regular.evenY, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 4 2 0 1 0, n02 6, n02 7, p 1 0, p 2 0, p 3 0]

private theorem cell57 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, n03 0, p 2 0, p 3 0]

private theorem cell58 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n00 0, n00 6, p 0 4, p 2 0, p 3 5]

private theorem cell59 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 5) : False := by
  close_register [h.regular.run, h.regular.scale, n01 0, p 1 0]

private theorem cell60 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 5) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, h.regular.scale, n02 0, p 2 0]

private theorem cell61 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 5) : False := by
  close_register [h.regular.run, h.regular.scale, n03 0, p 3 0]

private theorem cell62 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 6) : False := by
  close_register [h.regular.run, h.regular.scale, n00 0, p 0 0]

private theorem cell63 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 6) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n01 0, n01 4, p 1 3, p 2 6, p 3 0]

private theorem cell64 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 6) : False := by
  close_register [h.regular.run, h.regular.scale, n02 0, p 2 0]

private theorem cell65 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 6) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.num, h.regular.oddSector.1, h.regular.run, h.regular.scale, n03 0, p 3 0]

private theorem cell66 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n00 0, p 0 0]

private theorem cell67 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n01 0, p 1 0, p 2 0, p 3 0]

private theorem cell68 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n02 0, p 0 0, p 1 0, p 2 0]

private theorem cell69 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n03 0, p 0 0, p 1 0, p 3 0]

private theorem cell70 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell71 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n01 0, p 1 0]

private theorem cell72 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n02 0, p 0 0, p 1 0, p 2 0]

private theorem cell73 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n03 0, p 0 0, p 1 0, p 3 0]

private theorem cover0 {r : Register} (h : Hyp r) (n30 : Neg r 3 0) (o2 : Outside r 2) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell0 h n20 n30 p
  · exact cell1 h n21 n30 p
  · exact cell2 h n22 n30 p
  · exact cell3 h n23 n30 p

private theorem cover1 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n31 : Neg r 3 1) (o4 : Outside r 4) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell5 h n11 n40
  · exact cell6 h n11 n31 n41 p
  · exact cell7 h n31 n42 p
  · exact cell8 h n11 n31 n43 p

private theorem cover2 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 0) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell12 h n12 n43 n60 n81
  · exact cell13 h n12 n31 n43 n61 n81 p
  · exact cell14 h n43 n62
  · exact cell15 h n12 n31 n43 n63 n81 p

private theorem cover3 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n81 : Neg r 8 1) (o4 : Outside r 4) (o6 : Outside r 6) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell10 h n40 n81
  · exact cell11 h n12 n31 n41 n81 p
  · exact cell7 h n31 n42 p
  · exact cover2 h n12 n31 n43 n81 o6 p

private theorem cover4 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (n82 : Neg r 8 2) (o2 : Outside r 2) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell18 h n20 n31
  · exact cell19 h n21 n40
  · exact cell20 h n22 n31 n40 n82 p
  · exact cell21 h n23 n31 n72 n82

private theorem cover5 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n82 : Neg r 8 2) (o2 : Outside r 2) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell16 h n31 n70
  · exact cell17 h n40 n71
  · exact cover4 h n31 n40 n72 n82 o2 p
  · exact cell22 h n73 n82

private theorem cover6 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n82 : Neg r 8 2) (o2 : Outside r 2) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover5 h n31 n40 n82 o2 o7 p
  · exact cell23 h n41 n82 p
  · exact cell7 h n31 n42 p
  · exact cell24 h n43 n82

private theorem cover7 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell9 h n31 n80
  · exact cover3 h n12 n31 n81 o4 o6 p
  · exact cover6 h n31 n82 o2 o4 o7 p
  · exact cell25 h n12 n31 n83 p

private theorem cover8 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (o1 : Outside r 1) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell4 h n10 n31
  · exact cover1 h n11 n31 o4 p
  · exact cover7 h n12 n31 o2 o4 o6 o7 o8 p
  · exact cell26 h n13 n31 p

private theorem cover9 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell30 h n23 n32 n40 n50 n70 p
  · exact cell31 h n23 n51 n70
  · exact cell32 h n23 n40 n52 n70 p
  · exact cell33 h n23 n32 n40 n53 n70 p

private theorem cover10 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o2 : Outside r 2) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell27 h n20 n32 n40 n70 p
  · exact cell28 h n21 n70
  · exact cell29 h n22 n32 n40 n70 p
  · exact cover9 h n23 n32 n40 n70 o5 p

private theorem cover11 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (o2 : Outside r 2) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell34 h n20 n32 n40 n72 p
  · exact cell19 h n21 n40
  · exact cell35 h n22 n40 p
  · exact cell36 h n23 n32 n40 n72 p

private theorem cover12 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o2 : Outside r 2) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cover10 h n32 n40 n70 o2 o5 p
  · exact cell17 h n40 n71
  · exact cover11 h n32 n40 n72 o2 p
  · exact cell37 h n32 n73

private theorem cover13 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover12 h n32 n40 o2 o5 o7 p
  · exact cell38 h n32 n41 p
  · exact cell39 h n32 n42 p
  · exact cell40 h n32 n43

private theorem cover14 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cover0 h n30 o2 p
  · exact cover8 h n31 o1 o2 o4 o6 o7 o8 p
  · exact cover13 h n32 o2 o4 o5 o7 p
  · exact cell41 h n33 p

private theorem cover15 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 1) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell42 h n00 p
  · exact cell43 h n01 p
  · exact cell44 h n02 p
  · exact cell45 h n03 p

private theorem cover16 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 2) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell46 h n00 p
  · exact cell47 h n01 p
  · exact cell48 h n02 p
  · exact cell49 h n03 p

private theorem cover17 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 3) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell50 h n00 p
  · exact cell51 h n01 p
  · exact cell52 h n02 p
  · exact cell53 h n03 p

private theorem cover18 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 4) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell54 h n00 p
  · exact cell55 h n01 p
  · exact cell56 h n02 p
  · exact cell57 h n03 p

private theorem cover19 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 5) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell58 h n00 p
  · exact cell59 h n01 p
  · exact cell60 h n02 p
  · exact cell61 h n03 p

private theorem cover20 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 6) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell62 h n00 p
  · exact cell63 h n01 p
  · exact cell64 h n02 p
  · exact cell65 h n03 p

private theorem cover21 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 7) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell66 h n00 p
  · exact cell67 h n01 p
  · exact cell68 h n02 p
  · exact cell69 h n03 p

private theorem cover22 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 8) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell70 h n00 p
  · exact cell71 h n01 p
  · exact cell72 h n02 p
  · exact cell73 h n03 p

private theorem valid {r : Register} (h : Regular r false 0) (i : Fin 9) (j : Fin 4) :
    ((Piece r i.val).line r true 0 j).valid := by
  have a := h.scale
  have b := h.oddSize
  have c := h.evenSize
  have d := h.run
  have n := h.num
  have g := h.den
  fin_cases i <;> fin_cases j <;>
    norm_num [Piece,corrected,Shape.line,Shape.probe,Probe.line,Line.valid,orientation,
      Prod.smul_mk] at * <;> omega

private theorem inclusion0 {r : Register} (h : Hyp r) (yes : (Piece r 0).contains r true 0) :
    (Piece r 1).contains r true 0 ∨ (Piece r 2).contains r true 0 ∨ (Piece r 3).contains r true 0 ∨ (Piece r 4).contains r true 0 ∨ (Piece r 5).contains r true 0 ∨ (Piece r 6).contains r true 0 ∨ (Piece r 7).contains r true 0 ∨ (Piece r 8).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 0) r true 0 (valid h.regular 0) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover14 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 6 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

private theorem inclusion1 {r : Register} (h : Hyp r) (yes : (Piece r 1).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 1) r true 0 (valid h.regular 1) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover15 h (outside 0 (by tauto)) p

private theorem inclusion2 {r : Register} (h : Hyp r) (yes : (Piece r 2).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 2) r true 0 (valid h.regular 2) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover16 h (outside 0 (by tauto)) p

private theorem inclusion3 {r : Register} (h : Hyp r) (yes : (Piece r 3).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 3) r true 0 (valid h.regular 3) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover17 h (outside 0 (by tauto)) p

private theorem inclusion4 {r : Register} (h : Hyp r) (yes : (Piece r 4).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 4) r true 0 (valid h.regular 4) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover18 h (outside 0 (by tauto)) p

private theorem inclusion5 {r : Register} (h : Hyp r) (yes : (Piece r 5).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 5) r true 0 (valid h.regular 5) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover19 h (outside 0 (by tauto)) p

private theorem inclusion6 {r : Register} (h : Hyp r) (yes : (Piece r 6).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 6) r true 0 (valid h.regular 6) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover20 h (outside 0 (by tauto)) p

private theorem inclusion7 {r : Register} (h : Hyp r) (yes : (Piece r 7).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 7) r true 0 (valid h.regular 7) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover21 h (outside 0 (by tauto)) p

private theorem inclusion8 {r : Register} (h : Hyp r) (yes : (Piece r 8).contains r true 0) :
    (Piece r 0).contains r true 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 8) r true 0 (valid h.regular 8) yes
  have outside (i : Fin 9) (miss : ¬(Piece r i.val).contains r true 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover22 h (outside 0 (by tauto)) p

/-- At an admissible register the target and the union of the eight pieces contain the same site. -/
theorem coverage (r : Register) (regular : Regular r false 0) (multiple : r.M ∣ r.S)
    (lattice : ∀ i : Fin 9, (corrected r false 1 false i.val).lattice r 1 true 0) :
    ((corrected r false 1 false 0).contains r true 0) ↔ ∃ i : Fin 8, (corrected r false 1 false (i.val+1)).contains r true 0 := by
  let h : Hyp r := ⟨regular,multiple,lattice⟩
  constructor
  · intro p
    have hit := inclusion0 h p
    rcases hit with h | h | h | h | h | h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
    · exact ⟨4,h⟩
    · exact ⟨5,h⟩
    · exact ⟨6,h⟩
    · exact ⟨7,h⟩
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact inclusion1 h hi
    · exact inclusion2 h hi
    · exact inclusion3 h hi
    · exact inclusion4 h hi
    · exact inclusion5 h hi
    · exact inclusion6 h hi
    · exact inclusion7 h hi
    · exact inclusion8 h hi

end FLatticePaper.Tiles.CorrectedRegisterShortTwoReverseLowOdd
