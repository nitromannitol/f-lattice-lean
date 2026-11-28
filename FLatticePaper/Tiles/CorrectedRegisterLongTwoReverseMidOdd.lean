import FLatticePaper.Tiles.CorrectedRegisterDiagram
import Mathlib.Tactic.ClearExcept

/-! The elongated corrected diagram, with prefix letter 2, previous sign 1,
sector 1, and odd physical parity. -/

namespace FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseMidOdd

open FLatticePaper.Farey CorrectedLevelTests CorrectedRegisterDiagram Lean

private abbrev Piece (r : Register) (i : ℕ) := corrected r false 1 true i

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

private abbrev Pos (r : Register) (i : ℕ) := ∀ j, (Piece r i).bounds r true 1 j true
private abbrev Neg (r : Register) (i : ℕ) (j : Fin 4) := (Piece r i).bounds r true 1 j false
private abbrev Outside (r : Register) (i : ℕ) := Neg r i 0 ∨ Neg r i 1 ∨ Neg r i 2 ∨ Neg r i 3

private structure Hyp (r : Register) : Prop where
  regular : Regular r false 1
  multiple : r.M ∣ r.S
  lattice : ∀ i : Fin 10, (Piece r i.val).lattice r 1 true 1

private abbrev gap {r : Register} (h : Hyp r) (i : Fin 10) (j : Fin 4) (l a k : ℤ) :=
  Shape.gap (h.lattice i) (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j l a k

private abbrev gapS {r : Register} (h : Hyp r) (j k : ℤ) :=
  period_gap (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j k

private theorem cell0 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n20 0, n30 0, p 0 0, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 2 0, p 2 3]

private theorem cell1 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n20 0, n31 0]

private theorem cell2 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 3 0 0 0 0, n32 0, n50 6, n50 7, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 2 0, p 2 5]

private theorem cell3 {r : Register} (h : Hyp r) (n51 : Neg r 5 1) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n51 5, n51 6, n70 5, p 0 0, p 2 5]

private theorem cell4 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n52 : Neg r 5 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 7 2 0 0 0, n20 0, n52 6, n52 7, n70 0, n70 5, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 1 0, p 2 0, p 2 5]

private theorem cell5 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n53 : Neg r 5 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n32 0, n53 0, n53 5, n53 6, p 0 5]

private theorem cell6 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n71 : Neg r 7 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.2, h.regular.oddY, h.regular.run, h.regular.scale, n20 0, n32 0, n71 0, p 2 0]

private theorem cell7 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n32 0, n72 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 1 0, p 2 0, p 2 5]

private theorem cell8 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n32 0, n73 0]

private theorem cell9 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, p 1 0, p 3 4]

private theorem cell10 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n21 0, n21 3, n21 4, n21 5, p 0 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 6, p 3 0, p 3 4]

private theorem cell11 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n22 0, p 2 0]

private theorem cell12 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, h.regular.scaleParity, n23 0, n30 0, p 0 0, p 0 2, p 0 3, p 0 4, p 0 5, p 1 0, p 2 0, p 2 2, p 2 3, p 3 0]

private theorem cell13 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n31 0, n70 0]

private theorem cell14 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n40 0, n71 0]

private theorem cell15 {r : Register} (h : Hyp r) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n72 0, p 0 0, p 2 5]

private theorem cell16 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n73 : Neg r 7 3) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n31 0, n73 0, n80 5]

private theorem cell17 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n40 0, n81 0]

private theorem cell18 {r : Register} (h : Hyp r) (n73 : Neg r 7 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n73 0, n82 0]

private theorem cell19 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n31 : Neg r 3 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n10 0, n31 0]

private theorem cell20 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n40 0]

private theorem cell21 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n83 : Neg r 8 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, h.regular.run, n12 7, n31 0, n40 0, n83 0, p 2 0, p 3 0]

private theorem cell22 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 3 3 0 0 0, n13 5, n13 6, n31 0, n40 0, p 2 0, p 3 4]

private theorem cell23 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n41 0, p 1 0]

private theorem cell24 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n42 : Neg r 4 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n23 0, n42 0]

private theorem cell25 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n31 0, n43 0, n80 5]

private theorem cell26 {r : Register} (h : Hyp r) (n81 : Neg r 8 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n81 0, p 1 0]

private theorem cell27 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n43 0, n82 0]

private theorem cell28 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n43 : Neg r 4 3) (n83 : Neg r 8 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 7 1 0 0 0, n11 5, n11 6, n43 0, n83 0, p 1 0, p 1 4, p 2 0, p 3 4]

private theorem cell29 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n83 : Neg r 8 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n12 0, n12 6, n12 7, n31 0, n43 0, n83 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell30 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 3 3 0 0 0, n13 5, n13 6, n23 0, n31 0, n43 0, p 1 0, p 1 3, p 2 0, p 3 0, p 3 4]

private theorem cell31 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n50 : Neg r 5 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 3 0 0 0 0, n23 0, n23 6, n32 0, n40 0, n50 6, n50 7, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 2]

private theorem cell32 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n51 : Neg r 5 1) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n23 0, n23 6, n32 0, n51 0, n51 5, n51 6, n70 5, p 0 0, p 2 5, p 3 0]

private theorem cell33 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n52 : Neg r 5 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 7 2 0 0 0, n23 0, n23 6, n32 0, n40 0, n52 6, n52 7, n70 0, n70 5, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 2, p 2 5]

private theorem cell34 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n23 0, n32 0, n40 0, n72 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 5]

private theorem cell35 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n23 0, n32 0, n41 0, p 1 0]

private theorem cell36 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n42 : Neg r 4 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.2, h.regular.oddSector.2, h.regular.run, h.regular.scale, n23 0, n32 0, n42 0]

private theorem cell37 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n43 : Neg r 4 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n32 0, n43 0]

private theorem cell38 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n33 0, p 0 0, p 1 0, p 1 3, p 3 0, p 3 4]

private theorem cell39 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n10 0, n10 4, n10 5, n10 6, p 0 0, p 0 3, p 0 4, p 0 5, p 0 6, p 1 0, p 2 0, p 2 5, p 3 5]

private theorem cell40 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n11 0, n41 0, p 0 0, p 1 0, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell41 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n42 0, p 0 0, p 2 5]

private theorem cell42 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n43 : Neg r 4 3) (n80 : Neg r 8 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.2, h.regular.oddY, h.regular.run, h.regular.scale, n11 0, n43 0, n80 0, p 3 0]

private theorem cell43 {r : Register} (h : Hyp r) (n60 : Neg r 6 0) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n60 0, n81 6, p 1 0, p 3 4]

private theorem cell44 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 1 0 0 1, n43 0, n61 5, n61 6, p 1 0, p 1 4, p 3 0, p 3 4]

private theorem cell45 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n43 0, n62 0, n62 6, n62 7, p 1 4]

private theorem cell46 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n63 : Neg r 6 3) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, gap h 8 3 0 0 2, n11 0, n63 5, n63 6, n81 6, p 1 0, p 3 4]

private theorem cell47 {r : Register} (h : Hyp r) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n83 0, p 1 0, p 3 4]

private theorem cell48 {r : Register} (h : Hyp r) (n30 : Neg r 3 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n30 0, p 0 0]

private theorem cell49 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n21 0, n21 5, n21 6, n31 0, n40 0, p 2 5]

private theorem cell50 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 4 2 0 0 0, n22 6, n22 7, n31 0, n40 0, p 1 0, p 2 1, p 2 5, p 3 0]

private theorem cell51 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, h.regular.run, n23 6, n31 0, n40 0, n72 0, p 2 0, p 3 0]

private theorem cell52 {r : Register} (h : Hyp r) (n40 : Neg r 4 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n40 0, n81 0]

private theorem cell53 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n12 0, n31 0, n41 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 2]

private theorem cell54 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n42 0, p 2 5]

private theorem cell55 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n61 : Neg r 6 1) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 4 1 0 0 1, n12 0, n12 7, n31 0, n43 0, n61 5, n61 6, n81 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 4]

private theorem cell56 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n43 0, n62 0, n62 6, n62 7, p 1 4]

private theorem cell57 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n63 : Neg r 6 3) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 8 3 0 0 2, n12 0, n31 0, n43 0, n63 5, n63 6, n81 0, n81 6, p 1 0, p 1 1, p 1 2, p 1 3, p 3 4]

private theorem cell58 {r : Register} (h : Hyp r) (n70 : Neg r 7 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n70 0, p 0 0]

private theorem cell59 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n72 : Neg r 7 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, h.regular.scaleParity, gap h 1 0 0 (-1) 0, gap h 5 2 0 1 0, n20 6, n20 7, n32 0, n72 0, p 0 0, p 0 4, p 0 5, p 1 0, p 2 0, p 2 5, p 3 0]

private theorem cell60 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, h.regular.scale, n21 0, n21 5, n21 6, n32 0, n40 0, p 0 0, p 2 5]

private theorem cell61 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n22 : Neg r 2 2) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 4 2 0 0 0, n12 0, n22 6, n22 7, n40 0, p 0 0, p 0 4, p 1 0, p 2 0, p 2 5, p 3 0]

private theorem cell62 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n23 : Neg r 2 3) (n72 : Neg r 7 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n12 0, n23 0, n23 5, n23 6, n72 0, p 0 5]

private theorem cell63 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n32 0, n41 0, p 1 4]

private theorem cell64 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n42 : Neg r 4 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n32 0, n42 0, p 0 4, p 2 0, p 2 5]

private theorem cell65 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n33 : Neg r 3 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, h.regular.scaleParity, n12 0, n33 0, p 2 0, h.regular.num, h.regular.den, h.regular.scale, h.regular.oddX, h.regular.oddY, h.regular.oddDiff, h.regular.evenX, h.regular.evenY, h.regular.evenDiff, h.regular.oddSize, h.regular.evenNumParity]

private theorem cell66 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n13 0, p 3 0]

private theorem cell67 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n00 0, p 0 0]

private theorem cell68 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n01 0, n01 5, p 1 2, p 1 4, p 2 6, p 3 0, p 3 4]

private theorem cell69 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, p 2 0]

private theorem cell70 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n03 0, n03 5, p 0 5, p 1 3, p 3 0, p 3 4]

private theorem cell71 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n90 0, n90 6, p 0 0, p 0 5, p 2 5, p 3 5]

private theorem cell72 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n91 0, p 1 0]

private theorem cell73 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n92 0, n92 6, p 0 2, p 1 4, p 2 0, p 2 5]

private theorem cell74 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n93 0, p 3 0]

private theorem cell75 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, gap h 3 0 0 1 1, n00 6, n00 7, p 0 0, p 2 0, p 3 0]

private theorem cell76 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 3) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n01 0, p 1 0, p 2 0, p 3 0]

private theorem cell77 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 3) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n02 0, p 2 0]

private theorem cell78 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 3 0 0 1 1, gap h 3 3 0 (-1) 0, n03 5, n03 6, p 0 0, p 2 0, p 3 0]

private theorem cell79 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell80 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n90 : Neg r 9 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n01 0, n90 0, p 2 0, p 3 0]

private theorem cell81 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, gap h 4 1 0 (-1) 0, gap h 4 2 0 1 0, n91 5, n91 6, p 1 0, p 2 0, p 3 0]

private theorem cell82 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n92 : Neg r 9 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, h.regular.scaleParity, gap h 4 2 0 1 0, n01 6, n92 6, n92 7, p 0 0, p 1 0, p 2 0]

private theorem cell83 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 4) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n93 0, p 3 0]

private theorem cell84 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n90 0, p 0 0, p 2 0, p 3 0]

private theorem cell85 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (n92 : Neg r 9 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, gap h 4 2 0 1 0, n02 0, n92 6, n92 7, p 1 0, p 2 0]

private theorem cell86 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n03 0, p 2 0, p 3 0]

private theorem cell87 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n00 0, n00 6, p 0 0, p 0 5, p 2 5, p 3 5]

private theorem cell88 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 5) : False := by
  close_register [h.regular.run, h.regular.scale, n01 0, p 1 0]

private theorem cell89 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 5) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n02 0, n02 6, p 0 2, p 0 4, p 1 4, p 2 0, p 2 5]

private theorem cell90 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 5) : False := by
  close_register [h.regular.run, h.regular.scale, n03 0, p 3 0]

private theorem cell91 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 6) : False := by
  close_register [h.regular.run, h.regular.scale, n90 0, p 0 0]

private theorem cell92 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 6) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n91 0, n91 5, p 1 2, p 1 4, p 2 6, p 3 0, p 3 4]

private theorem cell93 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 6) : False := by
  close_register [h.regular.run, h.regular.scale, n92 0, p 2 0]

private theorem cell94 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 6) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, n93 0, n93 5, p 0 5, p 1 2, p 1 3, p 3 0, p 3 4]

private theorem cell95 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n00 0, p 0 0]

private theorem cell96 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n90 : Neg r 9 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n01 0, n90 0, p 2 0, p 3 0]

private theorem cell97 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (n90 : Neg r 9 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n02 0, n02 6, n90 0, n90 6, p 0 0, p 0 1, p 0 4, p 2 0, p 3 0]

private theorem cell98 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n03 0, p 2 0, p 3 0]

private theorem cell99 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 7) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n91 0, p 1 0, p 2 0, p 3 0, h.regular.num, h.regular.den, h.regular.scale, h.regular.run, h.regular.oddX, h.regular.oddY, h.regular.oddDiff, h.regular.evenX, h.regular.evenY, h.regular.evenDiff, h.regular.oddSize, h.regular.evenNumParity, h.regular.scaleParity]

private theorem cell100 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n92 0, p 2 0, p 3 0]

private theorem cell101 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 7) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n93 0, p 3 0]

private theorem cell102 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 8) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n00 0, p 0 0, p 2 0, p 3 0, h.regular.num, h.regular.den, h.regular.scale, h.regular.run, h.regular.oddX, h.regular.oddY, h.regular.oddDiff, h.regular.evenX, h.regular.evenY, h.regular.evenDiff, h.regular.oddSize, h.regular.evenNumParity, h.regular.scaleParity]

private theorem cell103 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n90 : Neg r 9 0) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n01 0, n90 0, p 2 0, p 3 0]

private theorem cell104 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 8) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n91 0, p 1 0]

private theorem cell105 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n92 0, p 2 0, p 3 0]

private theorem cell106 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n93 : Neg r 9 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n01 0, n01 5, n93 0, n93 5, p 1 0, p 1 1, p 1 4, p 1 5, p 2 0, p 3 0]

private theorem cell107 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n02 0, p 2 0]

private theorem cell108 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, n03 0, p 2 0, p 3 0]

private theorem cover0 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n70 : Neg r 7 0) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell2 h n32 n50 n70 p
  · exact cell3 h n51 n70 p
  · exact cell4 h n20 n52 n70 p
  · exact cell5 h n32 n53 p

private theorem cover1 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cover0 h n20 n32 n70 o5 p
  · exact cell6 h n20 n32 n71 p
  · exact cell7 h n32 n72 p
  · exact cell8 h n32 n73

private theorem cover2 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (o3 : Outside r 3) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell0 h n20 n30 p
  · exact cell1 h n20 n31
  · exact cover1 h n20 n32 o5 o7 p
  · exact cell9 h n33 p

private theorem cover3 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n83 : Neg r 8 3) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell19 h n10 n31
  · exact cell20 h n11 n40
  · exact cell21 h n12 n31 n40 n83 p
  · exact cell22 h n13 n31 n40 p

private theorem cover4 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n73 : Neg r 7 3) (o1 : Outside r 1) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell16 h n31 n73 n80
  · exact cell17 h n40 n81
  · exact cell18 h n73 n82
  · exact cover3 h n31 n40 n83 o1 p

private theorem cover5 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (o1 : Outside r 1) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell13 h n31 n70
  · exact cell14 h n40 n71
  · exact cell15 h n72 p
  · exact cover4 h n31 n40 n73 o1 o8 p

private theorem cover6 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n83 : Neg r 8 3) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell19 h n10 n31
  · exact cell28 h n11 n43 n83 p
  · exact cell29 h n12 n31 n43 n83 p
  · exact cell30 h n13 n23 n31 n43 p

private theorem cover7 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (o1 : Outside r 1) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell25 h n31 n43 n80
  · exact cell26 h n81 p
  · exact cell27 h n43 n82
  · exact cover6 h n23 n31 n43 n83 o1 p

private theorem cover8 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (o1 : Outside r 1) (o4 : Outside r 4) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover5 h n31 n40 o1 o7 o8 p
  · exact cell23 h n41 p
  · exact cell24 h n23 n42
  · exact cover7 h n23 n31 n43 o1 o8 p

private theorem cover9 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell31 h n23 n32 n40 n50 n70 p
  · exact cell32 h n23 n32 n51 n70 p
  · exact cell33 h n23 n32 n40 n52 n70 p
  · exact cell5 h n32 n53 p

private theorem cover10 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cover9 h n23 n32 n40 n70 o5 p
  · exact cell14 h n40 n71
  · exact cell34 h n23 n32 n40 n72 p
  · exact cell8 h n32 n73

private theorem cover11 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n32 : Neg r 3 2) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover10 h n23 n32 n40 o5 o7 p
  · exact cell35 h n23 n32 n41 p
  · exact cell36 h n23 n32 n42
  · exact cell37 h n32 n43

private theorem cover12 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (o1 : Outside r 1) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell12 h n23 n30 p
  · exact cover8 h n23 n31 o1 o4 o7 o8 p
  · exact cover11 h n23 n32 o4 o5 o7 p
  · exact cell38 h n33 p

private theorem cover13 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover2 h n20 o3 o5 o7 p
  · exact cell10 h n21 p
  · exact cell11 h n22 p
  · exact cover12 h n23 o1 o3 o4 o5 o7 o8 p

private theorem cover14 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n43 : Neg r 4 3) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell43 h n60 n81 p
  · exact cell44 h n43 n61 p
  · exact cell45 h n43 n62 p
  · exact cell46 h n11 n63 n81 p

private theorem cover15 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n43 : Neg r 4 3) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell42 h n11 n43 n80 p
  · exact cover14 h n11 n43 n81 o6 p
  · exact cell27 h n43 n82
  · exact cell47 h n83 p

private theorem cover16 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (o4 : Outside r 4) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell20 h n11 n40
  · exact cell40 h n11 n41 p
  · exact cell41 h n42 p
  · exact cover15 h n11 n43 o6 o8 p

private theorem cover17 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n73 : Neg r 7 3) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell16 h n31 n73 n80
  · exact cell52 h n40 n81
  · exact cell18 h n73 n82
  · exact cell47 h n83 p

private theorem cover18 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell13 h n31 n70
  · exact cell14 h n40 n71
  · exact cell51 h n23 n31 n40 n72 p
  · exact cover17 h n31 n40 n73 o8 p

private theorem cover19 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (o2 : Outside r 2) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell1 h n20 n31
  · exact cell49 h n21 n31 n40 p
  · exact cell50 h n22 n31 n40 p
  · exact cover18 h n23 n31 n40 o7 o8 p

private theorem cover20 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell43 h n60 n81 p
  · exact cell55 h n12 n31 n43 n61 n81 p
  · exact cell56 h n43 n62 p
  · exact cell57 h n12 n31 n43 n63 n81 p

private theorem cover21 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell25 h n31 n43 n80
  · exact cover20 h n12 n31 n43 n81 o6 p
  · exact cell27 h n43 n82
  · exact cell47 h n83 p

private theorem cover22 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n31 : Neg r 3 1) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover19 h n31 n40 o2 o7 o8 p
  · exact cell53 h n12 n31 n41 p
  · exact cell54 h n31 n42 p
  · exact cover21 h n12 n31 n43 o6 o8 p

private theorem cover23 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell59 h n20 n32 n72 p
  · exact cell60 h n21 n32 n40 p
  · exact cell61 h n12 n22 n40 p
  · exact cell62 h n12 n23 n72 p

private theorem cover24 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n32 : Neg r 3 2) (n40 : Neg r 4 0) (o2 : Outside r 2) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell58 h n70 p
  · exact cell14 h n40 n71
  · exact cover23 h n12 n32 n40 n72 o2 p
  · exact cell8 h n32 n73

private theorem cover25 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n32 : Neg r 3 2) (o2 : Outside r 2) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover24 h n12 n32 n40 o2 o7 p
  · exact cell63 h n32 n41 p
  · exact cell64 h n32 n42 p
  · exact cell37 h n32 n43

private theorem cover26 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell48 h n30 p
  · exact cover22 h n12 n31 o2 o4 o6 o7 o8 p
  · exact cover25 h n12 n32 o2 o4 o7 p
  · exact cell65 h n12 n33 p

private theorem cover27 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell39 h n10 p
  · exact cover16 h n11 o4 o6 o8 p
  · exact cover26 h n12 o2 o3 o4 o6 o7 o8 p
  · exact cell66 h n13 p

private theorem cover28 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 1) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell67 h n00 p
  · exact cell68 h n01 p
  · exact cell69 h n02 p
  · exact cell70 h n03 p

private theorem cover29 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 2) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell71 h n90 p
  · exact cell72 h n91 p
  · exact cell73 h n92 p
  · exact cell74 h n93 p

private theorem cover30 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 3) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell75 h n00 p
  · exact cell76 h n01 p
  · exact cell77 h n02 p
  · exact cell78 h n03 p

private theorem cover31 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell80 h n01 n90 p
  · exact cell81 h n91 p
  · exact cell82 h n01 n92 p
  · exact cell83 h n93 p

private theorem cover32 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell84 h n90 p
  · exact cell81 h n91 p
  · exact cell85 h n02 n92 p
  · exact cell83 h n93 p

private theorem cover33 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell79 h n00 p
  · exact cover31 h n01 o9 p
  · exact cover32 h n02 o9 p
  · exact cell86 h n03 p

private theorem cover34 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 5) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell87 h n00 p
  · exact cell88 h n01 p
  · exact cell89 h n02 p
  · exact cell90 h n03 p

private theorem cover35 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell91 h n90 p
  · exact cell92 h n91 p
  · exact cell93 h n92 p
  · exact cell94 h n93 p

private theorem cover36 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (o0 : Outside r 0) (p : Pos r 7) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell95 h n00 p
  · exact cell96 h n01 n90 p
  · exact cell97 h n02 n90 p
  · exact cell98 h n03 p

private theorem cover37 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 7) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cover36 h n90 o0 p
  · exact cell99 h n91 p
  · exact cell100 h n92 p
  · exact cell101 h n93 p

private theorem cover38 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (o9 : Outside r 9) (p : Pos r 8) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell103 h n01 n90 p
  · exact cell104 h n91 p
  · exact cell105 h n92 p
  · exact cell106 h n01 n93 p

private theorem cover39 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 8) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell102 h n00 p
  · exact cover38 h n01 o9 p
  · exact cell107 h n02 p
  · exact cell108 h n03 p

private theorem valid {r : Register} (h : Regular r false 1) (i : Fin 10) (j : Fin 4) :
    ((Piece r i.val).line r true 1 j).valid := by
  have a := h.scale
  have b := h.oddSize
  have c := h.evenSize
  have d := h.run
  have n := h.num
  have g := h.den
  fin_cases i <;> fin_cases j <;>
    norm_num [Piece,corrected,Shape.line,Shape.probe,Probe.line,Line.valid,orientation,
      Prod.smul_mk,Fin.ext_iff] at * <;> omega

private theorem inclusion0 {r : Register} (h : Hyp r) (yes : (Piece r 0).contains r true 1) :
    (Piece r 1).contains r true 1 ∨ (Piece r 2).contains r true 1 ∨ (Piece r 3).contains r true 1 ∨ (Piece r 4).contains r true 1 ∨ (Piece r 5).contains r true 1 ∨ (Piece r 6).contains r true 1 ∨ (Piece r 7).contains r true 1 ∨ (Piece r 8).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 0) r true 1 (valid h.regular 0) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover13 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

private theorem inclusion1 {r : Register} (h : Hyp r) (yes : (Piece r 1).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 1) r true 1 (valid h.regular 1) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover28 h (outside 0 (by tauto)) p

private theorem inclusion2 {r : Register} (h : Hyp r) (yes : (Piece r 2).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 2) r true 1 (valid h.regular 2) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover29 h (outside 9 (by tauto)) p

private theorem inclusion3 {r : Register} (h : Hyp r) (yes : (Piece r 3).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 3) r true 1 (valid h.regular 3) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover30 h (outside 0 (by tauto)) p

private theorem inclusion4 {r : Register} (h : Hyp r) (yes : (Piece r 4).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 4) r true 1 (valid h.regular 4) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover33 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion5 {r : Register} (h : Hyp r) (yes : (Piece r 5).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 5) r true 1 (valid h.regular 5) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover34 h (outside 0 (by tauto)) p

private theorem inclusion6 {r : Register} (h : Hyp r) (yes : (Piece r 6).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 6) r true 1 (valid h.regular 6) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover35 h (outside 9 (by tauto)) p

private theorem inclusion7 {r : Register} (h : Hyp r) (yes : (Piece r 7).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 7) r true 1 (valid h.regular 7) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover37 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion8 {r : Register} (h : Hyp r) (yes : (Piece r 8).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 8) r true 1 (valid h.regular 8) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover39 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion9 {r : Register} (h : Hyp r) (yes : (Piece r 9).contains r true 1) :
    (Piece r 1).contains r true 1 ∨ (Piece r 2).contains r true 1 ∨ (Piece r 3).contains r true 1 ∨ (Piece r 4).contains r true 1 ∨ (Piece r 5).contains r true 1 ∨ (Piece r 6).contains r true 1 ∨ (Piece r 7).contains r true 1 ∨ (Piece r 8).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 9) r true 1 (valid h.regular 9) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover27 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 6 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

/-- At an admissible register the target and the union of the component polygons contain the same site. -/
theorem coverage (r : Register) (regular : Regular r false 1) (multiple : r.M ∣ r.S)
    (lattice : ∀ i : Fin 10, (corrected r false 1 true i.val).lattice r 1 true 1) :
    ((corrected r false 1 true 0).contains r true 1 ∨ (corrected r false 1 true 9).contains r true 1) ↔ ∃ i : Fin 8, (corrected r false 1 true (i.val+1)).contains r true 1 := by
  let h : Hyp r := ⟨regular,multiple,lattice⟩
  constructor
  · intro p
    have hit := p.elim (inclusion0 h) (inclusion9 h)
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

end FLatticePaper.Tiles.CorrectedRegisterLongTwoReverseMidOdd
