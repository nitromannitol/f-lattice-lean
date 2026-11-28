import FLatticePaper.Tiles.CorrectedMixedDiagram
import Mathlib.Tactic.ClearExcept

/-! The odd mixed alternate diagram, with prefix letter 1, previous sign -1,
sector 1, and odd physical parity. -/

namespace FLatticePaper.Tiles.MixedRegisterOddOneDirectMidOdd

open FLatticePaper.Farey CorrectedLevelTests CorrectedRegisterDiagram CorrectedMixedDiagram Lean

private abbrev Piece (r : Register) (i : ℕ) := mixed r true (-1) false i

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

private abbrev Pos (r : Register) (i : ℕ) := ∀ j, (Piece r i).bounds r true 1 j true
private abbrev Neg (r : Register) (i : ℕ) (j : Fin 4) := (Piece r i).bounds r true 1 j false
private abbrev Outside (r : Register) (i : ℕ) := Neg r i 0 ∨ Neg r i 1 ∨ Neg r i 2 ∨ Neg r i 3

private structure Hyp (r : Register) : Prop where
  regular : Regular r true 1
  multiple : r.M ∣ r.S
  scaleRun : r.S=r.M
  lattice : ∀ i : Fin 10, (Piece r i.val).lattice r 1 true 1

private abbrev gap {r : Register} (h : Hyp r) (i : Fin 10) (j : Fin 4) (l a k : ℤ) :=
  Shape.gap (h.lattice i) (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j l a k

private abbrev gapS {r : Register} (h : Hyp r) (j k : ℤ) :=
  period_gap (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j k

private theorem cell0 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n20 0, n30 0, p 0 0, p 0 1, p 0 2, p 0 5, p 2 0, p 2 3]

private theorem cell1 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n40 0]

private theorem cell2 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n41 : Neg r 4 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n20 0, n41 0]

private theorem cell3 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n42 0, n70 0, n70 6, n70 7, p 0 0, p 2 5]

private theorem cell4 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n20 4, n20 5, n42 0, n71 0, n71 5]

private theorem cell5 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n31 : Neg r 3 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n10 0, n20 0, n31 0]

private theorem cell6 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n11 5, n11 6, n20 0, n31 0, n50 0, n72 0, p 2 4, p 2 5]

private theorem cell7 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 5 2 0 0 0, n12 6, n12 7, n20 0, n31 0, n50 0, n72 0, p 2 5, p 3 0]

private theorem cell8 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) : False := by
  close_register [h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, n13 5, n20 0, n31 0, n50 0, n72 0]

private theorem cell9 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n51 : Neg r 5 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n20 0, n51 0]

private theorem cell10 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n20 0, n31 0, n52 0, p 2 5]

private theorem cell11 {r : Register} (h : Hyp r) (n53 : Neg r 5 3) (n72 : Neg r 7 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n53 0, n72 0]

private theorem cell12 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.evenSector.2, h.regular.oddSector.2, n42 0, n73 0]

private theorem cell13 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n20 0, n31 0, n43 0, p 3 0]

private theorem cell14 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 3 0 0 0 0, n10 6, n10 7, n20 0, n32 0, n50 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0, p 2 5, p 3 0]

private theorem cell15 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n11 0, n11 5, n11 6, n20 0, n50 0, p 0 0, p 2 5]

private theorem cell16 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n20 : Neg r 2 0) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 5 2 0 0 0, n12 6, n12 7, n20 0, n50 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 2 5, p 3 0]

private theorem cell17 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n13 0, n13 6, n20 0, n32 0, n50 0, p 0 0, p 0 1, p 0 5]

private theorem cell18 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n51 : Neg r 5 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n20 0, n51 0]

private theorem cell19 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n32 0, n52 0, p 0 4, p 2 0, p 2 5]

private theorem cell20 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n53 : Neg r 5 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n32 0, n53 0]

private theorem cell21 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, p 1 0, p 3 4]

private theorem cell22 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n21 0, p 1 0]

private theorem cell23 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n30 : Neg r 3 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n22 0, n30 0, p 0 0, p 0 4, p 0 5, p 2 0, p 2 2, p 2 3]

private theorem cell24 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n50 : Neg r 5 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n50 0]

private theorem cell25 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n22 0, n31 0, n41 0, n51 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 2]

private theorem cell26 {r : Register} (h : Hyp r) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n52 0, p 0 0, p 2 5]

private theorem cell27 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n80 0]

private theorem cell28 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n53 0, n60 0, n81 0, n81 5, n81 6]

private theorem cell29 {r : Register} (h : Hyp r) (n53 : Neg r 5 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.2, h.regular.oddSector.2, n53 0, n82 0]

private theorem cell30 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n60 : Neg r 6 0) (n83 : Neg r 8 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n22 0, n31 0, n60 0, n83 0, p 2 0, p 3 2, p 3 3]

private theorem cell31 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n61 : Neg r 6 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n61 0, p 1 0]

private theorem cell32 {r : Register} (h : Hyp r) (n53 : Neg r 5 3) (n62 : Neg r 6 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n53 0, n62 0]

private theorem cell33 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n22 0, n31 0, n41 0, n53 0, n63 0, p 1 1, p 1 2, p 1 3, p 2 0, p 3 2, p 3 3]

private theorem cell34 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.scaleParity, n31 0, n42 0, n50 0, n70 6, n70 7, p 3 0]

private theorem cell35 {r : Register} (h : Hyp r) (n50 : Neg r 5 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n50 0, n71 0]

private theorem cell36 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n31 : Neg r 3 1) (n50 : Neg r 5 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n10 0, n31 0, n50 0]

private theorem cell37 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n11 5, n11 6, n22 0, n31 0, n50 0, n72 0, p 2 3, p 2 4, p 2 5]

private theorem cell38 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n22 : Neg r 2 2) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 5 2 0 0 0, n12 6, n12 7, n22 0, n50 0, n72 0, p 0 0, p 2 5, p 3 0]

private theorem cell39 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, h.regular.scaleParity, n13 0, n13 5, n22 0, n31 0, n50 0, n72 0, p 0 0]

private theorem cell40 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n51 : Neg r 5 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n42 0, n51 0, p 1 4]

private theorem cell41 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n60 : Neg r 6 0) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n42 0, n60 0, n70 0, n70 6, n70 7]

private theorem cell42 {r : Register} (h : Hyp r) (n71 : Neg r 7 1) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n71 0, n80 0]

private theorem cell43 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n42 0, n83 0]

private theorem cell44 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n42 0, n53 0, n61 0, p 1 0]

private theorem cell45 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n63 : Neg r 6 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n42 0, n63 0]

private theorem cell46 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n22 0, n43 0, p 2 0]

private theorem cell47 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n22 : Neg r 2 2) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 3 0 0 0 0, n10 6, n10 7, n22 0, n32 0, n50 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 0 5, p 2 0, p 2 5, p 3 0]

private theorem cell48 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n11 5, n11 6, n22 0, n50 0, p 0 0, p 2 5]

private theorem cell49 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n22 : Neg r 2 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 5 2 0 0 0, n12 6, n12 7, n22 0, n50 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 2 5, p 3 0]

private theorem cell50 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n22 : Neg r 2 2) (n32 : Neg r 3 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n13 0, n13 5, n13 6, n22 0, n32 0, p 0 5]

private theorem cell51 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n51 : Neg r 5 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n32 0, n51 0, p 1 4, p 2 0]

private theorem cell52 {r : Register} (h : Hyp r) (n32 : Neg r 3 2) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n32 0, n52 0, p 0 4, p 2 0, p 2 5]

private theorem cell53 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n33 : Neg r 3 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.scaleParity, n22 0, n33 0, p 0 6, p 1 0, p 1 1, p 1 2, p 1 3, p 3 4]

private theorem cell54 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n23 0, p 3 0]

private theorem cell55 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n10 0, p 0 0]

private theorem cell56 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n11 0, n40 0]

private theorem cell57 {r : Register} (h : Hyp r) (n51 : Neg r 5 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n51 0, n60 0]

private theorem cell58 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n51 0, n61 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell59 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n51 0, n62 0, p 1 5, p 2 5]

private theorem cell60 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 6 1 0 0 0, n21 5, n21 6, n41 0, n51 0, n63 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 1, p 3 4]

private theorem cell61 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n22 0, n22 6, n22 7, n41 0, n51 0, n63 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell62 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n23 5, n41 0, n51 0, n63 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 4]

private theorem cell63 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n52 : Neg r 5 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n11 0, n52 0, p 1 0, p 2 0]

private theorem cell64 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n80 0]

private theorem cell65 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n41 0, n53 0, n60 0, n81 5, n81 6]

private theorem cell66 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n21 0, n41 0, n60 0]

private theorem cell67 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n41 : Neg r 4 1) (n60 : Neg r 6 0) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.2, n22 6, n41 0, n60 0, n83 0, p 1 0]

private theorem cell68 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 3 0 0 0, n11 0, n23 5, n23 6, n41 0, n83 0, p 1 0, p 2 0, p 3 4]

private theorem cell69 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n41 0, n53 0, n61 0, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell70 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 6 1 0 0 0, n11 0, n21 5, n21 6, n53 0, n63 0, p 1 2, p 1 3, p 1 4, p 3 0, p 3 4]

private theorem cell71 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n11 0, n22 0, n22 6, n22 7, n41 0, n53 0, n63 0, p 1 3, p 1 4, p 3 0]

private theorem cell72 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 3 0 0 0, n11 0, n23 5, n23 6, n41 0, n53 0, p 1 3, p 2 0, p 3 0, p 3 4]

private theorem cell73 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n50 : Neg r 5 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n11 4, n11 5, n50 0, p 0 0, p 2 5]

private theorem cell74 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n52 : Neg r 5 2) (n60 : Neg r 6 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n11 0, n52 0, n60 0, p 2 0]

private theorem cell75 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n53 : Neg r 5 3) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n11 4, n53 0, n80 0]

private theorem cell76 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n42 0, n53 0, n60 0, n81 0, n81 5, n81 6]

private theorem cell77 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n42 : Neg r 4 2) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n11 0, n42 0, n61 0, p 1 3, p 1 4, p 2 0]

private theorem cell78 {r : Register} (h : Hyp r) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n62 0, p 0 0, p 2 5]

private theorem cell79 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n43 0, p 1 0, p 3 4]

private theorem cell80 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n12 0, p 2 0]

private theorem cell81 {r : Register} (h : Hyp r) (n30 : Neg r 3 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n30 0, p 0 0, p 1 0]

private theorem cell82 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n41 0, n51 0, n61 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell83 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n13 0, n31 0, n41 0, n51 0, n62 0, p 1 0, p 1 1, p 1 2, p 1 3, p 2 5]

private theorem cell84 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 6 1 0 0 0, n21 5, n21 6, n41 0, n51 0, n63 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 1, p 3 4]

private theorem cell85 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n23 5, n41 0, n51 0, n63 0, p 1 1, p 1 2, p 1 3, p 3 0, p 3 4]

private theorem cell86 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n52 : Neg r 5 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n13 0, n31 0, n52 0, p 1 0]

private theorem cell87 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n21 0, n41 0, n60 0]

private theorem cell88 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 3 0 0 0, n23 5, n23 6, n31 0, n41 0, n83 0, p 1 0, p 2 0, p 3 4]

private theorem cell89 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.scaleParity, n31 0, n53 0, n61 0, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell90 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n31 : Neg r 3 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 6 1 0 0 0, n21 5, n21 6, n31 0, n53 0, n63 0, p 1 2, p 1 3, p 1 4, p 3 0, p 3 4]

private theorem cell91 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n13 0, n22 0, n22 7, n31 0, n41 0, n63 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0]

private theorem cell92 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 3 0 0 0, n23 5, n23 6, n31 0, n41 0, n53 0, p 1 3, p 2 0, p 3 0, p 3 4]

private theorem cell93 {r : Register} (h : Hyp r) (n50 : Neg r 5 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n50 0, n71 0]

private theorem cell94 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n52 : Neg r 5 2) (n60 : Neg r 6 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n13 0, n52 0, n60 0, n71 0]

private theorem cell95 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n60 : Neg r 6 0) (n72 : Neg r 7 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n60 0, n72 0, p 1 0, p 2 2, p 2 3, p 2 4, p 3 0]

private theorem cell96 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n13 0, n31 0, n42 0, n61 0, p 1 1, p 1 2, p 1 3, p 1 4]

private theorem cell97 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, n31 0, n62 0, p 2 5]

private theorem cell98 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n32 : Neg r 3 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n13 0, n32 0, p 0 1, p 2 4]

private theorem cell99 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, n40 0, p 0 5, p 3 0]

private theorem cell100 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n60 : Neg r 6 0) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n21 0, n41 0, n60 0]

private theorem cell101 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n41 : Neg r 4 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, n41 0, n61 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 2]

private theorem cell102 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n62 : Neg r 6 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, n62 0, p 3 0]

private theorem cell103 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n21 : Neg r 2 1) (n41 : Neg r 4 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 6 1 0 0 0, n13 0, n21 5, n21 6, n41 0, n63 0, p 1 1, p 1 2, p 1 3, p 1 4, p 3 0, p 3 4]

private theorem cell104 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n33 : Neg r 3 3) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n22 0, n22 6, n22 7, n33 0, n41 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4]

private theorem cell105 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n23 : Neg r 2 3) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, gap h 4 3 0 0 0, n13 0, n23 5, n23 6, n41 0, p 1 0, p 1 1, p 1 2, p 1 3, p 2 0, p 3 0, p 3 4]

private theorem cell106 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n42 : Neg r 4 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, n42 0]

private theorem cell107 {r : Register} (h : Hyp r) (n33 : Neg r 3 3) (n43 : Neg r 4 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n33 0, n43 0, p 1 3, p 3 0, p 3 4]

private theorem cell108 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n00 0, n00 6, p 0 4, p 0 5, p 2 0, p 2 5, p 3 5]

private theorem cell109 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n01 0, p 1 0]

private theorem cell110 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, n02 6, p 0 4, p 1 4, p 2 0, p 2 5]

private theorem cell111 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 1) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n03 0, p 3 0]

private theorem cell112 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n90 0, p 0 0]

private theorem cell113 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.scaleParity, n91 0, n91 5, p 1 0, p 1 3, p 1 4, p 2 6, p 3 0, p 3 1, p 3 4]

private theorem cell114 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n92 0, p 2 0]

private theorem cell115 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 2) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n93 0, n93 5, p 0 5, p 1 2, p 1 3, p 3 0, p 3 4]

private theorem cell116 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 3) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, gap h 3 0 0 0 1, n00 6, n00 7, p 0 0, p 2 0, p 3 0]

private theorem cell117 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 3) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n01 0, p 1 0, p 2 0, p 3 0]

private theorem cell118 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 3) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, p 2 0, p 3 0]

private theorem cell119 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 3) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 3 0 0 0 1, gap h 3 3 0 0 (-1), n03 5, n03 6, p 0 0, p 1 0, p 3 0]

private theorem cell120 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n00 0, p 0 0]

private theorem cell121 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n01 0, p 1 0]

private theorem cell122 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, p 2 0, p 3 0]

private theorem cell123 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n90 : Neg r 9 0) (p : Pos r 4) : False := by
  close_register [h.scaleRun, h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.run, h.regular.scaleParity, gap h 4 0 0 0 1, n03 0, n03 5, n90 6, n90 7, p 0 0, p 3 0]

private theorem cell124 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n91 0, p 1 0, p 2 0, p 3 0]

private theorem cell125 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n92 : Neg r 9 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n03 0, n92 0, p 3 0]

private theorem cell126 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n93 : Neg r 9 3) (p : Pos r 4) : False := by
  close_register [h.scaleRun, h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, h.regular.run, gap h 4 0 0 0 1, gap h 4 3 0 0 (-1), n03 0, n93 5, n93 6, p 0 0, p 1 0, p 3 0]

private theorem cell127 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n90 0, p 0 0]

private theorem cell128 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 5) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n91 0, p 1 0]

private theorem cell129 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell130 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n92 : Neg r 9 2) (p : Pos r 5) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.run, h.regular.scaleParity, gap h 5 1 0 0 (-1), gap h 5 2 0 0 1, n01 5, n01 6, n92 0, n92 6, p 1 0, p 2 0, p 3 0]

private theorem cell131 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 5) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, gap h 5 2 0 0 1, n02 6, n02 7, p 0 0, p 1 0, p 2 0]

private theorem cell132 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n92 : Neg r 9 2) (p : Pos r 5) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n03 0, n92 0, p 2 0]

private theorem cell133 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 5) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n93 0, p 2 0, p 3 0]

private theorem cell134 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 6) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell135 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 6) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n90 0, p 0 0, p 2 0, p 3 0]

private theorem cell136 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 6) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, gap h 6 1 0 0 (-1), gap h 6 2 0 0 1, n91 5, n91 6, p 0 0, p 1 0, p 2 0]

private theorem cell137 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 6) : False := by
  close_register [h.scaleRun, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, h.regular.run, gap h 6 2 0 0 1, n92 6, n92 7, p 0 0, p 1 0, p 2 0]

private theorem cell138 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 6) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n93 0, p 2 0, p 3 0]

private theorem cell139 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 6) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, p 2 0, p 3 0]

private theorem cell140 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n91 : Neg r 9 1) (p : Pos r 6) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSize, n03 4, n91 0, p 0 0, p 3 0]

private theorem cell141 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n92 : Neg r 9 2) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n03 0, n92 0]

private theorem cell142 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell143 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 7) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n01 0, p 1 0]

private theorem cell144 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n02 0, p 2 0]

private theorem cell145 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 7) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n03 0, p 3 0]

private theorem cell146 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 8) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n90 0, p 0 0]

private theorem cell147 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 8) : False := by
  close_register [h.regular.evenDenParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSector.2, n91 0, p 1 0, p 2 0, p 3 0]

private theorem cell148 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, n92 0, p 2 0]

private theorem cell149 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSector.2, h.regular.evenSize, h.regular.oddSector.1, h.regular.oddSector.2, h.regular.oddSize, n93 0, p 3 0]

private theorem cover0 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell5 h n10 n20 n31
  · exact cell6 h n11 n20 n31 n50 n72 p
  · exact cell7 h n12 n20 n31 n50 n72 p
  · exact cell8 h n13 n20 n31 n50 n72

private theorem cover1 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n72 : Neg r 7 2) (o1 : Outside r 1) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cover0 h n20 n31 n50 n72 o1 p
  · exact cell9 h n20 n51
  · exact cell10 h n20 n31 n52 p
  · exact cell11 h n53 n72

private theorem cover2 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (o1 : Outside r 1) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell3 h n31 n42 n70 p
  · exact cell4 h n20 n42 n71
  · exact cover1 h n20 n31 n72 o1 o5 p
  · exact cell12 h n42 n73

private theorem cover3 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (o1 : Outside r 1) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell1 h n31 n40
  · exact cell2 h n20 n41
  · exact cover2 h n20 n31 n42 o1 o5 o7 p
  · exact cell13 h n20 n31 n43 p

private theorem cover4 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell14 h n10 n20 n32 n50 p
  · exact cell15 h n11 n20 n50 p
  · exact cell16 h n12 n20 n50 p
  · exact cell17 h n13 n20 n32 n50 p

private theorem cover5 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n32 : Neg r 3 2) (o1 : Outside r 1) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cover4 h n20 n32 n50 o1 p
  · exact cell18 h n20 n51
  · exact cell19 h n32 n52 p
  · exact cell20 h n32 n53

private theorem cover6 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (o1 : Outside r 1) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell0 h n20 n30 p
  · exact cover3 h n20 n31 o1 o4 o5 o7 p
  · exact cover5 h n20 n32 o1 o5 p
  · exact cell21 h n33 p

private theorem cover7 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell27 h n41 n80
  · exact cell28 h n31 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cell30 h n22 n31 n60 n83 p

private theorem cover8 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover7 h n22 n31 n41 n53 n60 o8 p
  · exact cell31 h n41 n61 p
  · exact cell32 h n53 n62
  · exact cell33 h n22 n31 n41 n53 n63 p

private theorem cover9 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (o5 : Outside r 5) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell24 h n41 n50
  · exact cell25 h n22 n31 n41 n51 p
  · exact cell26 h n52 p
  · exact cover8 h n22 n31 n41 n53 o6 o8 p

private theorem cover10 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n50 : Neg r 5 0) (n72 : Neg r 7 2) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell36 h n10 n31 n50
  · exact cell37 h n11 n22 n31 n50 n72 p
  · exact cell38 h n12 n22 n50 n72 p
  · exact cell39 h n13 n22 n31 n50 n72 p

private theorem cover11 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n50 : Neg r 5 0) (o1 : Outside r 1) (o7 : Outside r 7) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell34 h n31 n42 n50 n70 p
  · exact cell35 h n50 n71
  · exact cover10 h n22 n31 n50 n72 o1 p
  · exact cell12 h n42 n73

private theorem cover12 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n71 : Neg r 7 1) (o8 : Outside r 8) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell42 h n71 n80
  · exact cell28 h n31 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cell43 h n42 n83

private theorem cover13 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (o7 : Outside r 7) (o8 : Outside r 8) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell41 h n31 n42 n60 n70
  · exact cover12 h n31 n42 n53 n60 n71 o8
  · exact cell11 h n53 n72
  · exact cell12 h n42 n73

private theorem cover14 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover13 h n31 n42 n53 n60 o7 o8
  · exact cell44 h n42 n53 n61 p
  · exact cell32 h n53 n62
  · exact cell45 h n42 n63

private theorem cover15 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (o1 : Outside r 1) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cover11 h n22 n31 n42 n50 o1 o7 p
  · exact cell40 h n42 n51 p
  · exact cell26 h n52 p
  · exact cover14 h n31 n42 n53 o6 o7 o8 p

private theorem cover16 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n31 : Neg r 3 1) (o1 : Outside r 1) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell1 h n31 n40
  · exact cover9 h n22 n31 n41 o5 o6 o8 p
  · exact cover15 h n22 n31 n42 o1 o5 o6 o7 o8 p
  · exact cell46 h n22 n43 p

private theorem cover17 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n32 : Neg r 3 2) (n50 : Neg r 5 0) (o1 : Outside r 1) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell47 h n10 n22 n32 n50 p
  · exact cell48 h n11 n22 n50 p
  · exact cell49 h n12 n22 n50 p
  · exact cell50 h n13 n22 n32 p

private theorem cover18 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n32 : Neg r 3 2) (o1 : Outside r 1) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cover17 h n22 n32 n50 o1 p
  · exact cell51 h n32 n51 p
  · exact cell52 h n32 n52 p
  · exact cell20 h n32 n53

private theorem cover19 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (o1 : Outside r 1) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell23 h n22 n30 p
  · exact cover16 h n22 n31 o1 o4 o5 o6 o7 o8 p
  · exact cover18 h n22 n32 o1 o5 p
  · exact cell53 h n22 n33 p

private theorem cover20 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover6 h n20 o1 o3 o4 o5 o7 p
  · exact cell22 h n21 p
  · exact cover19 h n22 o1 o3 o4 o5 o6 o7 o8 p
  · exact cell54 h n23 p

private theorem cover21 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell60 h n21 n41 n51 n63 p
  · exact cell61 h n22 n41 n51 n63 p
  · exact cell62 h n23 n41 n51 n63 p

private theorem cover22 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell57 h n51 n60
  · exact cell58 h n41 n51 n61 p
  · exact cell59 h n41 n51 n62 p
  · exact cover21 h n41 n51 n63 o2 p

private theorem cover23 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n60 : Neg r 6 0) (n83 : Neg r 8 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell66 h n21 n41 n60
  · exact cell67 h n22 n41 n60 n83 p
  · exact cell68 h n11 n23 n41 n83 p

private theorem cover24 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (o2 : Outside r 2) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell64 h n41 n80
  · exact cell65 h n11 n41 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cover23 h n11 n41 n60 n83 o2 p

private theorem cover25 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell70 h n11 n21 n53 n63 p
  · exact cell71 h n11 n22 n41 n53 n63 p
  · exact cell72 h n11 n23 n41 n53 p

private theorem cover26 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o2 : Outside r 2) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover24 h n11 n41 n53 n60 o2 o8 p
  · exact cell69 h n11 n41 n53 n61 p
  · exact cell32 h n53 n62
  · exact cover25 h n11 n41 n53 n63 o2 p

private theorem cover27 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n41 : Neg r 4 1) (o2 : Outside r 2) (o5 : Outside r 5) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell24 h n41 n50
  · exact cover22 h n41 n51 o2 o6 p
  · exact cell63 h n11 n52 p
  · exact cover26 h n11 n41 n53 o2 o6 o8 p

private theorem cover28 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (o8 : Outside r 8) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell75 h n11 n53 n80
  · exact cell76 h n11 n42 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cell43 h n42 n83

private theorem cover29 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n42 : Neg r 4 2) (n60 : Neg r 6 0) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell73 h n11 n50 p
  · exact cell57 h n51 n60
  · exact cell74 h n11 n52 n60 p
  · exact cover28 h n11 n42 n53 n60 o8

private theorem cover30 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n42 : Neg r 4 2) (o5 : Outside r 5) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover29 h n11 n42 n60 o5 o8 p
  · exact cell77 h n11 n42 n61 p
  · exact cell78 h n62 p
  · exact cell45 h n42 n63

private theorem cover31 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell56 h n11 n40
  · exact cover27 h n11 n41 o2 o5 o6 o8 p
  · exact cover30 h n11 n42 o5 o6 o8 p
  · exact cell79 h n43 p

private theorem cover32 {r : Register} (h : Hyp r) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (n63 : Neg r 6 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell84 h n21 n41 n51 n63 p
  · exact cell61 h n22 n41 n51 n63 p
  · exact cell85 h n23 n41 n51 n63 p

private theorem cover33 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n51 : Neg r 5 1) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell57 h n51 n60
  · exact cell82 h n41 n51 n61 p
  · exact cell83 h n13 n31 n41 n51 n62 p
  · exact cover32 h n41 n51 n63 o2 p

private theorem cover34 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n60 : Neg r 6 0) (n83 : Neg r 8 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell87 h n21 n41 n60
  · exact cell67 h n22 n41 n60 n83 p
  · exact cell88 h n23 n31 n41 n83 p

private theorem cover35 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (o2 : Outside r 2) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell27 h n41 n80
  · exact cell28 h n31 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cover34 h n31 n41 n60 n83 o2 p

private theorem cover36 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (n63 : Neg r 6 3) (o2 : Outside r 2) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cell90 h n21 n31 n53 n63 p
  · exact cell91 h n13 n22 n31 n41 n63 p
  · exact cell92 h n23 n31 n41 n53 p

private theorem cover37 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (n53 : Neg r 5 3) (o2 : Outside r 2) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover35 h n31 n41 n53 n60 o2 o8 p
  · exact cell89 h n31 n53 n61 p
  · exact cell32 h n53 n62
  · exact cover36 h n13 n31 n41 n53 n63 o2 p

private theorem cover38 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n41 : Neg r 4 1) (o2 : Outside r 2) (o5 : Outside r 5) (o6 : Outside r 6) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell24 h n41 n50
  · exact cover33 h n13 n31 n41 n51 o2 o6 p
  · exact cell86 h n13 n31 n52 p
  · exact cover37 h n13 n31 n41 n53 o2 o6 o8 p

private theorem cover39 {r : Register} (h : Hyp r) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n71 : Neg r 7 1) (o8 : Outside r 8) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell42 h n71 n80
  · exact cell28 h n31 n53 n60 n81
  · exact cell29 h n53 n82
  · exact cell43 h n42 n83

private theorem cover40 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n60 : Neg r 6 0) (n71 : Neg r 7 1) (o5 : Outside r 5) (o8 : Outside r 8) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell93 h n50 n71
  · exact cell57 h n51 n60
  · exact cell94 h n13 n52 n60 n71
  · exact cover39 h n31 n42 n53 n60 n71 o8

private theorem cover41 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (n60 : Neg r 6 0) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell41 h n31 n42 n60 n70
  · exact cover40 h n13 n31 n42 n60 n71 o5 o8
  · exact cell95 h n31 n60 n72 p
  · exact cell12 h n42 n73

private theorem cover42 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n42 : Neg r 4 2) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cover41 h n13 n31 n42 n60 o5 o7 o8 p
  · exact cell96 h n13 n31 n42 n61 p
  · exact cell97 h n31 n62 p
  · exact cell45 h n42 n63

private theorem cover43 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell1 h n31 n40
  · exact cover38 h n13 n31 n41 o2 o5 o6 o8 p
  · exact cover42 h n13 n31 n42 o5 o6 o7 o8 p
  · exact cell79 h n43 p

private theorem cover44 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n21 : Neg r 2 1) (n33 : Neg r 3 3) (n41 : Neg r 4 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell100 h n21 n41 n60
  · exact cell101 h n33 n41 n61 p
  · exact cell102 h n33 n62 p
  · exact cell103 h n13 n21 n41 n63 p

private theorem cover45 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n33 : Neg r 3 3) (n41 : Neg r 4 1) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell2 h n20 n41
  · exact cover44 h n13 n21 n33 n41 o6 p
  · exact cell104 h n22 n33 n41 p
  · exact cell105 h n13 n23 n41 p

private theorem cover46 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n33 : Neg r 3 3) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell99 h n33 n40 p
  · exact cover45 h n13 n33 n41 o2 o6 p
  · exact cell106 h n33 n42
  · exact cell107 h n33 n43 p

private theorem cover47 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell81 h n30 p
  · exact cover43 h n13 n31 o2 o4 o5 o6 o7 o8 p
  · exact cell98 h n13 n32 p
  · exact cover46 h n13 n33 o2 o4 o6 p

private theorem cover48 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell55 h n10 p
  · exact cover31 h n11 o2 o4 o5 o6 o8 p
  · exact cell80 h n12 p
  · exact cover47 h n13 o2 o3 o4 o5 o6 o7 o8 p

private theorem cover49 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 1) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell108 h n00 p
  · exact cell109 h n01 p
  · exact cell110 h n02 p
  · exact cell111 h n03 p

private theorem cover50 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 2) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell112 h n90 p
  · exact cell113 h n91 p
  · exact cell114 h n92 p
  · exact cell115 h n93 p

private theorem cover51 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 3) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell116 h n00 p
  · exact cell117 h n01 p
  · exact cell118 h n02 p
  · exact cell119 h n03 p

private theorem cover52 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell123 h n03 n90 p
  · exact cell124 h n91 p
  · exact cell125 h n03 n92 p
  · exact cell126 h n03 n93 p

private theorem cover53 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell120 h n00 p
  · exact cell121 h n01 p
  · exact cell122 h n02 p
  · exact cover52 h n03 o9 p

private theorem cover54 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (o0 : Outside r 0) (p : Pos r 5) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell129 h n00 p
  · exact cell130 h n01 n92 p
  · exact cell131 h n02 p
  · exact cell132 h n03 n92 p

private theorem cover55 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 5) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell127 h n90 p
  · exact cell128 h n91 p
  · exact cover54 h n92 o0 p
  · exact cell133 h n93 p

private theorem cover56 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell135 h n90 p
  · exact cell136 h n91 p
  · exact cell137 h n92 p
  · exact cell138 h n93 p

private theorem cover57 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell135 h n90 p
  · exact cell140 h n03 n91 p
  · exact cell141 h n03 n92
  · exact cell138 h n93 p

private theorem cover58 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell134 h n00 p
  · exact cover56 h o9 p
  · exact cell139 h n02 p
  · exact cover57 h n03 o9 p

private theorem cover59 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 7) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell142 h n00 p
  · exact cell143 h n01 p
  · exact cell144 h n02 p
  · exact cell145 h n03 p

private theorem cover60 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 8) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell146 h n90 p
  · exact cell147 h n91 p
  · exact cell148 h n92 p
  · exact cell149 h n93 p

private theorem valid {r : Register} (h : Regular r true 1) (i : Fin 10) (j : Fin 4) :
    ((Piece r i.val).line r true 1 j).valid := by
  have a := h.scale
  have b := h.oddSize
  have c := h.evenSize
  have d := h.run
  have n := h.num
  have g := h.den
  fin_cases i <;> fin_cases j <;>
    norm_num [Piece,mixed,Shape.line,Shape.probe,Probe.line,Line.valid,orientation,
      Prod.smul_mk,Fin.ext_iff] at * <;> omega

private theorem inclusion0 {r : Register} (h : Hyp r) (yes : (Piece r 0).contains r true 1) :
    (Piece r 1).contains r true 1 ∨ (Piece r 2).contains r true 1 ∨ (Piece r 3).contains r true 1 ∨ (Piece r 4).contains r true 1 ∨ (Piece r 5).contains r true 1 ∨ (Piece r 6).contains r true 1 ∨ (Piece r 7).contains r true 1 ∨ (Piece r 8).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 0) r true 1 (valid h.regular 0) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover20 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 6 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

private theorem inclusion1 {r : Register} (h : Hyp r) (yes : (Piece r 1).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 1) r true 1 (valid h.regular 1) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover49 h (outside 0 (by tauto)) p

private theorem inclusion2 {r : Register} (h : Hyp r) (yes : (Piece r 2).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 2) r true 1 (valid h.regular 2) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover50 h (outside 9 (by tauto)) p

private theorem inclusion3 {r : Register} (h : Hyp r) (yes : (Piece r 3).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 3) r true 1 (valid h.regular 3) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover51 h (outside 0 (by tauto)) p

private theorem inclusion4 {r : Register} (h : Hyp r) (yes : (Piece r 4).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 4) r true 1 (valid h.regular 4) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover53 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion5 {r : Register} (h : Hyp r) (yes : (Piece r 5).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 5) r true 1 (valid h.regular 5) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover55 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion6 {r : Register} (h : Hyp r) (yes : (Piece r 6).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 6) r true 1 (valid h.regular 6) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover58 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion7 {r : Register} (h : Hyp r) (yes : (Piece r 7).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 7) r true 1 (valid h.regular 7) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover59 h (outside 0 (by tauto)) p

private theorem inclusion8 {r : Register} (h : Hyp r) (yes : (Piece r 8).contains r true 1) :
    (Piece r 0).contains r true 1 ∨ (Piece r 9).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 8) r true 1 (valid h.regular 8) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover60 h (outside 9 (by tauto)) p

private theorem inclusion9 {r : Register} (h : Hyp r) (yes : (Piece r 9).contains r true 1) :
    (Piece r 1).contains r true 1 ∨ (Piece r 2).contains r true 1 ∨ (Piece r 3).contains r true 1 ∨ (Piece r 4).contains r true 1 ∨ (Piece r 5).contains r true 1 ∨ (Piece r 6).contains r true 1 ∨ (Piece r 7).contains r true 1 ∨ (Piece r 8).contains r true 1 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 9) r true 1 (valid h.regular 9) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r true 1) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover48 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 6 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

/-- At an admissible register the target and the union of the component polygons contain the same site. -/
theorem coverage (r : Register) (regular : Regular r true 1) (multiple : r.M ∣ r.S) (scaleRun : r.S=r.M)
    (lattice : ∀ i : Fin 10, (mixed r true (-1) false i.val).lattice r 1 true 1) :
    ((mixed r true (-1) false 0).contains r true 1 ∨ (mixed r true (-1) false 9).contains r true 1) ↔ ∃ i : Fin 8, (mixed r true (-1) false (i.val+1)).contains r true 1 := by
  let h : Hyp r := ⟨regular,multiple,scaleRun,lattice⟩
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

end FLatticePaper.Tiles.MixedRegisterOddOneDirectMidOdd
