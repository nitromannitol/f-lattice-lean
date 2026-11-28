import FLatticePaper.Tiles.CorrectedMixedDiagram
import Mathlib.Tactic.ClearExcept

/-! The even mixed alternate diagram, with prefix letter 2, previous sign -1,
sector 0, and even physical parity. -/

namespace FLatticePaper.Tiles.MixedRegisterEvenTwoDirectLowEven

open FLatticePaper.Farey CorrectedLevelTests CorrectedRegisterDiagram CorrectedMixedDiagram Lean

private abbrev Piece (r : Register) (i : ℕ) := mixed r false (-1) true i

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

private abbrev Pos (r : Register) (i : ℕ) := ∀ j, (Piece r i).bounds r false 0 j true
private abbrev Neg (r : Register) (i : ℕ) (j : Fin 4) := (Piece r i).bounds r false 0 j false
private abbrev Outside (r : Register) (i : ℕ) := Neg r i 0 ∨ Neg r i 1 ∨ Neg r i 2 ∨ Neg r i 3

private structure Hyp (r : Register) : Prop where
  regular : Regular r false 0
  multiple : r.M ∣ r.S
  scaleRun : r.S=r.M
  lattice : ∀ i : Fin 10, (Piece r i.val).lattice r (-1) false 0

private abbrev gap {r : Register} (h : Hyp r) (i : Fin 10) (j : Fin 4) (l a k : ℤ) :=
  Shape.gap (h.lattice i) (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j l a k

private abbrev gapS {r : Register} (h : Hyp r) (j k : ℤ) :=
  period_gap (show 0 ≤ r.M by have := h.regular.scale; omega) h.multiple j k

private theorem cell0 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n30 4, n40 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 3 0]

private theorem cell1 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n31 : Neg r 3 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n10 0, n31 0, n70 0]

private theorem cell2 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n32 : Neg r 3 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n10 0, n32 0, p 0 4]

private theorem cell3 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n33 6, n40 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 3 0, p 3 5]

private theorem cell4 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n11 0, n40 0, n70 0]

private theorem cell5 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n20 : Neg r 2 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenX, h.regular.oddDiff, h.regular.oddY, n12 0, n20 0, p 1 0, p 2 4]

private theorem cell6 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n13 0, n20 0, n30 4, n30 5, n40 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 3 0]

private theorem cell7 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n31 : Neg r 3 1) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenX, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n13 0, n20 0, n31 0, n31 6, n40 0, n70 0, n70 7, p 0 0, p 3 1, p 3 2, p 3 3, p 3 4, p 3 5]

private theorem cell8 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n32 : Neg r 3 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, n13 0, n32 0, n32 5, n32 6, p 0 4]

private theorem cell9 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n33 : Neg r 3 3) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, gap h 7 3 0 0 0, n20 0, n33 6, n33 7, n40 0, n70 0, n70 7, p 0 0, p 0 1, p 0 2, p 0 3, p 3 0, p 3 5]

private theorem cell10 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n20 0, n40 0, n71 0]

private theorem cell11 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n40 0, n72 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 3 0]

private theorem cell12 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (n80 : Neg r 8 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.oddParity, h.regular.oddSector.1, n11 0, n20 0, n40 8, n72 0, n80 6, p 2 4]

private theorem cell13 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n11 0, n20 0, n40 0, n81 0]

private theorem cell14 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddY, n11 0, n20 0, n50 5, p 1 0, p 2 4]

private theorem cell15 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) (n51 : Neg r 5 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n11 0, n40 0, n51 0]

private theorem cell16 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n52 : Neg r 5 2) (n72 : Neg r 7 2) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 1 2 0 0 0, n11 0, n20 0, n40 0, n52 6, n72 0, n82 0, p 1 0, p 2 4]

private theorem cell17 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n53 : Neg r 5 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, n11 0, n20 0, n40 0, n53 6, n82 0]

private theorem cell18 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n11 0, n40 0, n72 0, n83 0]

private theorem cell19 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n72 : Neg r 7 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n72 0]

private theorem cell20 {r : Register} (h : Hyp r) (n73 : Neg r 7 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n73 0, p 0 3, p 3 0, p 3 5]

private theorem cell21 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n41 : Neg r 4 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, n20 0, n41 0, n41 5, p 3 6]

private theorem cell22 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n30 : Neg r 3 0) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenY, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n30 4, n42 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 0 4, p 3 0]

private theorem cell23 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n33 : Neg r 3 3) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n33 6, n42 0, n70 0, p 0 0, p 0 1, p 0 2, p 0 3, p 3 0, p 3 5]

private theorem cell24 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n11 0, n70 0]

private theorem cell25 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n30 : Neg r 3 0) (n42 : Neg r 4 2) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n30 4, n30 5, n42 0, p 0 3, p 0 4]

private theorem cell26 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n31 : Neg r 3 1) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n13 0, n31 0, n31 6, n70 0, n70 7, p 0 0, p 3 3, p 3 4, p 3 5]

private theorem cell27 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n33 : Neg r 3 3) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 7 3 0 0 0, n13 0, n33 6, n33 7, n42 0, n70 7, p 0 3, p 3 5]

private theorem cell28 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n71 : Neg r 7 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenY, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, n20 0, n71 0, n71 7, p 0 0, p 2 1]

private theorem cell29 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n72 : Neg r 7 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenY, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n10 0, n20 0, n72 0, p 0 1, p 0 2, p 0 3, p 0 4, p 2 0, p 3 0]

private theorem cell30 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n72 : Neg r 7 2) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, n11 0, n72 0, n80 0, n80 6]

private theorem cell31 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n20 0, n81 0]

private theorem cell32 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddY, n20 0, n51 0, n51 6, n82 0]

private theorem cell33 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n52 : Neg r 5 2) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 1 2 0 0 0, n11 0, n20 0, n52 5, n52 6, n82 0, p 1 0, p 2 4]

private theorem cell34 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n53 : Neg r 5 3) (n82 : Neg r 8 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.num, h.regular.oddSector.1, n11 0, n20 0, n53 0, n53 6, n53 7, n82 0]

private theorem cell35 {r : Register} (h : Hyp r) (n72 : Neg r 7 2) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n72 0, n83 0]

private theorem cell36 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n73 : Neg r 7 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n42 0, n73 0, p 0 3, p 3 5]

private theorem cell37 {r : Register} (h : Hyp r) (n43 : Neg r 4 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n43 0, p 3 0]

private theorem cell38 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (p : Pos r 0) : False := by
  close_register [h.regular.scale, n21 0, p 1 0]

private theorem cell39 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n22 : Neg r 2 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n10 0, n22 0, p 0 4, p 2 0]

private theorem cell40 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, n11 0, n22 0, n80 0, n80 6]

private theorem cell41 {r : Register} (h : Hyp r) (n81 : Neg r 8 1) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n81 0, p 1 0]

private theorem cell42 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n50 : Neg r 5 0) (p : Pos r 0) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n11 0, n22 0, n50 0, n50 5, p 2 0, p 2 1, p 2 2, p 2 3, p 2 4]

private theorem cell43 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n51 : Neg r 5 1) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n22 0, n51 5, n51 6, n82 0, p 1 4, p 1 5, p 2 0]

private theorem cell44 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n52 : Neg r 5 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 1 2 0 0 0, n11 0, n22 0, n52 5, n52 6, p 1 4, p 2 0, p 2 4]

private theorem cell45 {r : Register} (h : Hyp r) (n53 : Neg r 5 3) (n82 : Neg r 8 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, n53 0, n53 6, n53 7, n82 0, p 1 5]

private theorem cell46 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n22 0, n83 0]

private theorem cell47 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (n22 : Neg r 2 2) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n12 0, n22 0, p 0 1, p 0 4, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell48 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n22 : Neg r 2 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n22 0]

private theorem cell49 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (p : Pos r 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n23 0, p 3 0]

private theorem cell50 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (p : Pos r 9) : False := by
  close_register [h.regular.scale, n10 0, p 0 0]

private theorem cell51 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n50 : Neg r 5 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n11 0, n50 0, n50 4, p 2 4]

private theorem cell52 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (n80 : Neg r 8 0) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n11 0, n51 0, n80 0]

private theorem cell53 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n20 0, n51 0, n81 0]

private theorem cell54 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n60 : Neg r 6 0) (n81 : Neg r 8 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n21 0, n60 0, n81 0]

private theorem cell55 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n51 0, n61 5, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0]

private theorem cell56 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n62 : Neg r 6 2) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n51 0, n62 5, n81 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell57 {r : Register} (h : Hyp r) (n21 : Neg r 2 1) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n21 0, n63 0, p 1 5]

private theorem cell58 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n51 : Neg r 5 1) (n60 : Neg r 6 0) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n11 0, n22 0, n51 0, n60 0, n60 5, n81 6, p 2 0, p 2 1, p 2 2, p 2 3, p 2 4]

private theorem cell59 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n51 : Neg r 5 1) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n22 0, n51 0, n61 5, n61 6, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0]

private theorem cell60 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (n62 : Neg r 6 2) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, gap h 8 2 0 0 0, n11 0, n51 0, n62 5, n62 6, n81 6, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell61 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n63 : Neg r 6 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, n22 0, n63 0, n63 6, n63 7, p 1 5]

private theorem cell62 {r : Register} (h : Hyp r) (n23 : Neg r 2 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenY, h.regular.oddY, n23 0, p 0 0, p 3 5]

private theorem cell63 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (n82 : Neg r 8 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n51 0, n82 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell64 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n70 : Neg r 7 0) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n11 0, n20 0, n51 0, n70 0]

private theorem cell65 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n71 : Neg r 7 1) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, n11 0, n20 0, n51 9, n71 5, n83 0, p 0 0, p 3 5]

private theorem cell66 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n72 : Neg r 7 2) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenDiff, h.regular.oddDiff, h.regular.oddSize, n20 0, n51 0, n72 0, n83 0]

private theorem cell67 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n51 : Neg r 5 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSize, h.regular.oddDiff, n20 0, n40 0, n51 0]

private theorem cell68 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n41 : Neg r 4 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddY, n11 0, n20 0, n41 6, p 0 0, p 3 5]

private theorem cell69 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (n51 : Neg r 5 1) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.oddSector.1, n11 0, n20 0, n42 5, n51 0, n73 0]

private theorem cell70 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n43 : Neg r 4 3) (n51 : Neg r 5 1) (n73 : Neg r 7 3) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, gap h 2 3 0 0 0, n11 0, n20 0, n43 7, n51 0, n73 0, n83 0, p 0 0, p 3 0, p 3 1, p 3 5]

private theorem cell71 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n51 0, n83 0, p 0 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0]

private theorem cell72 {r : Register} (h : Hyp r) (n52 : Neg r 5 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n52 0, p 2 0]

private theorem cell73 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n80 : Neg r 8 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, n11 0, n80 0, n80 8, p 3 0]

private theorem cell74 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n53 0, n61 5, n81 0, p 0 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0]

private theorem cell75 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n62 : Neg r 6 2) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddDiff, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n53 0, n62 5, n81 0, p 0 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell76 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (n53 : Neg r 5 3) (n60 : Neg r 6 0) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.num, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n22 0, n53 0, n60 0, n60 5, n81 0, n81 6, p 1 0, p 2 3, p 2 4]

private theorem cell77 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n53 : Neg r 5 3) (n61 : Neg r 6 1) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n22 0, n53 0, n61 5, n61 6, p 0 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0]

private theorem cell78 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n53 : Neg r 5 3) (n62 : Neg r 6 2) (n81 : Neg r 8 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, gap h 8 2 0 0 0, n11 0, n22 0, n53 0, n62 5, n62 6, n81 6, p 0 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell79 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n53 : Neg r 5 3) (n82 : Neg r 8 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenNumParity, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n53 0, n82 0, p 1 0, p 1 1, p 1 2, p 1 3, p 1 4, p 2 0, p 2 4]

private theorem cell80 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n71 : Neg r 7 1) (n83 : Neg r 8 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, n20 0, n71 0, n71 5, n83 0]

private theorem cell81 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n40 : Neg r 4 0) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddY, n11 0, n40 0, n40 5, n73 0]

private theorem cell82 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (n73 : Neg r 7 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, n11 0, n20 0, n42 0, n42 5, n42 6, n73 0]

private theorem cell83 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n43 : Neg r 4 3) (n73 : Neg r 7 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 2 3 0 0 0, n11 0, n20 0, n43 6, n43 7, n73 0, p 0 0, p 3 5]

private theorem cell84 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n83 : Neg r 8 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scaleParity, n11 0, n21 0, n53 0, n83 0, p 0 0, p 1 1, p 1 2, p 1 3, p 1 4, p 1 5, p 2 0, p 3 0]

private theorem cell85 {r : Register} (h : Hyp r) (n12 : Neg r 1 2) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n12 0, p 2 0]

private theorem cell86 {r : Register} (h : Hyp r) (n70 : Neg r 7 0) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n70 0, p 0 0]

private theorem cell87 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n71 : Neg r 7 1) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, n13 0, n20 0, n71 0, n71 5]

private theorem cell88 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n40 : Neg r 4 0) (n73 : Neg r 7 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenX, h.regular.evenY, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n40 4, n40 5, n73 0, p 0 3, p 0 4, p 3 0]

private theorem cell89 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n41 : Neg r 4 1) (n73 : Neg r 7 3) (p : Pos r 9) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenX, h.regular.oddDiff, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, h.regular.scale, n13 0, n20 0, n41 0, n41 6, n73 0, p 3 0, p 3 1, p 3 2, p 3 3, p 3 4, p 3 5]

private theorem cell90 {r : Register} (h : Hyp r) (n42 : Neg r 4 2) (n73 : Neg r 7 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, n42 0, n42 5, n42 6, n73 0, p 0 4]

private theorem cell91 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n43 : Neg r 4 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, gap h 2 3 0 0 0, n13 0, n20 0, n43 6, n43 7, p 0 3, p 3 0, p 3 5]

private theorem cell92 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n21 : Neg r 2 1) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n21 0, p 1 5, p 3 0]

private theorem cell93 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n23 : Neg r 2 3) (p : Pos r 9) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n13 0, n23 0, p 0 3, p 3 0, p 3 5]

private theorem cell94 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.num, h.regular.oddSector.1, n00 5, p 0 0, p 2 0]

private theorem cell95 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n01 0, p 1 0]

private theorem cell96 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 1) : False := by
  close_register [h.scaleRun, h.regular.evenSize, h.regular.evenY, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 1 2 0 0 (-1), n02 5, n02 6, p 0 0, p 1 0, p 2 0, p 3 0]

private theorem cell97 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 1) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n03 0, p 3 0]

private theorem cell98 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n90 0, p 0 0]

private theorem cell99 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.num, h.regular.oddSector.1, n91 6, p 1 0, p 3 0]

private theorem cell100 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 2) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n92 0, p 2 0]

private theorem cell101 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 2) : False := by
  close_register [h.scaleRun, h.regular.evenSize, h.regular.evenY, h.regular.oddSize, h.regular.oddY, h.regular.run, gap h 2 3 0 0 1, n93 6, n93 7, p 0 0, p 1 0, p 2 0, p 3 0]

private theorem cell102 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 3) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, h.regular.scale, n00 0, n00 4, n00 5, p 0 3, p 0 4, p 2 5, p 3 0]

private theorem cell103 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n01 0, p 0 0, p 1 0]

private theorem cell104 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 3) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n02 0, p 0 0, p 1 0, p 2 0]

private theorem cell105 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 3) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n03 6, p 0 0, p 0 3, p 1 0, p 3 0, p 3 5]

private theorem cell106 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 4) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddParity, h.regular.oddSector.1, h.regular.oddY, h.regular.scale, n90 0, n90 4, n90 5, p 0 3, p 0 4, p 2 5, p 3 0]

private theorem cell107 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n91 0, p 0 0, p 1 0]

private theorem cell108 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 4) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n92 0, p 0 0, p 1 0, p 2 0]

private theorem cell109 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 4) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n93 6, p 0 0, p 0 3, p 1 0, p 3 0, p 3 5]

private theorem cell110 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 5) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n00 0, p 0 0, p 1 0]

private theorem cell111 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 5) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, h.regular.scale, n01 0, n01 5, n01 6, p 1 4, p 1 5, p 2 0, p 3 6]

private theorem cell112 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 5) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n02 0, n02 5, p 0 4, p 1 0, p 1 1, p 1 4, p 2 0, p 2 4]

private theorem cell113 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 5) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n03 0, p 0 0, p 1 0, p 3 0]

private theorem cell114 {r : Register} (h : Hyp r) (n90 : Neg r 9 0) (p : Pos r 6) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n90 0, p 0 0, p 1 0]

private theorem cell115 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 6) : False := by
  close_register [h.regular.den, h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, h.regular.scale, n91 0, n91 5, n91 6, p 1 4, p 1 5, p 2 0, p 3 6]

private theorem cell116 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 6) : False := by
  close_register [h.regular.evenDiff, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n92 0, n92 5, p 0 4, p 1 0, p 1 1, p 1 4, p 2 0, p 2 4]

private theorem cell117 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 6) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenY, h.regular.oddSector.1, h.regular.oddSize, h.regular.oddY, n93 0, p 0 0, p 1 0, p 3 0]

private theorem cell118 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n00 0, p 0 0]

private theorem cell119 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (p : Pos r 7) : False := by
  close_register [h.regular.den, h.regular.num, n01 6, p 1 4, p 3 0]

private theorem cell120 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n02 0, p 2 0]

private theorem cell121 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (n90 : Neg r 9 0) (p : Pos r 7) : False := by
  close_register [h.regular.evenSize, h.regular.evenY, h.regular.oddParity, h.regular.oddY, n03 6, n90 0, p 1 0, p 3 0]

private theorem cell122 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n91 0, p 1 0, p 2 0, p 3 0]

private theorem cell123 {r : Register} (h : Hyp r) (n92 : Neg r 9 2) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n92 0, p 2 0]

private theorem cell124 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 7) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n93 0, p 3 0]

private theorem cell125 {r : Register} (h : Hyp r) (n00 : Neg r 0 0) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n00 0, p 0 0, p 2 0, p 3 0]

private theorem cell126 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n90 : Neg r 9 0) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n01 0, n90 0]

private theorem cell127 {r : Register} (h : Hyp r) (n91 : Neg r 9 1) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n91 0, p 1 0]

private theorem cell128 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (n92 : Neg r 9 2) (p : Pos r 8) : False := by
  close_register [h.regular.den, h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.num, h.regular.oddSector.1, h.regular.oddY, h.regular.scale, n01 6, n92 0, n92 5, p 2 0]

private theorem cell129 {r : Register} (h : Hyp r) (n93 : Neg r 9 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n93 0, p 3 0]

private theorem cell130 {r : Register} (h : Hyp r) (n02 : Neg r 0 2) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n02 0, p 2 0]

private theorem cell131 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (p : Pos r 8) : False := by
  close_register [h.regular.evenSector.1, h.regular.evenSize, h.regular.evenY, h.regular.oddSector.1, h.regular.oddY, n03 0, p 3 0]

private theorem cover0 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell0 h n10 n20 n30 n40 n70 p
  · exact cell1 h n10 n31 n70
  · exact cell2 h n10 n32 p
  · exact cell3 h n10 n20 n33 n40 n70 p

private theorem cover1 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell6 h n13 n20 n30 n40 n70 p
  · exact cell7 h n13 n20 n31 n40 n70 p
  · exact cell8 h n13 n32 p
  · exact cell9 h n20 n33 n40 n70 p

private theorem cover2 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n70 : Neg r 7 0) (o1 : Outside r 1) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cover0 h n10 n20 n40 n70 o3 p
  · exact cell4 h n11 n40 n70
  · exact cell5 h n12 n20 p
  · exact cover1 h n13 n20 n40 n70 o3 p

private theorem cover3 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (n82 : Neg r 8 2) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell14 h n11 n20 n50 p
  · exact cell15 h n11 n40 n51
  · exact cell16 h n11 n20 n40 n52 n72 n82 p
  · exact cell17 h n11 n20 n40 n53 n82

private theorem cover4 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell12 h n11 n20 n40 n72 n80 p
  · exact cell13 h n11 n20 n40 n81
  · exact cover3 h n11 n20 n40 n72 n82 o5 p
  · exact cell18 h n11 n40 n72 n83

private theorem cover5 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (n72 : Neg r 7 2) (o1 : Outside r 1) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell11 h n10 n20 n40 n72 p
  · exact cover4 h n11 n20 n40 n72 o5 o8 p
  · exact cell5 h n12 n20 p
  · exact cell19 h n13 n72

private theorem cover6 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n40 : Neg r 4 0) (o1 : Outside r 1) (o3 : Outside r 3) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cover2 h n20 n40 n70 o1 o3 p
  · exact cell10 h n20 n40 n71
  · exact cover5 h n20 n40 n72 o1 o5 o8 p
  · exact cell20 h n73 p

private theorem cover7 {r : Register} (h : Hyp r) (n10 : Neg r 1 0) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell22 h n10 n20 n30 n42 n70 p
  · exact cell1 h n10 n31 n70
  · exact cell2 h n10 n32 p
  · exact cell23 h n10 n20 n33 n42 n70 p

private theorem cover8 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o3 with n30 | n31 | n32 | n33
  · exact cell25 h n13 n30 n42 p
  · exact cell26 h n13 n31 n70 p
  · exact cell8 h n13 n32 p
  · exact cell27 h n13 n33 n42 n70 p

private theorem cover9 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (n70 : Neg r 7 0) (o1 : Outside r 1) (o3 : Outside r 3) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cover7 h n10 n20 n42 n70 o3 p
  · exact cell24 h n11 n70
  · exact cell5 h n12 n20 p
  · exact cover8 h n13 n42 n70 o3 p

private theorem cover10 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n82 : Neg r 8 2) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell14 h n11 n20 n50 p
  · exact cell32 h n20 n51 n82
  · exact cell33 h n11 n20 n52 n82 p
  · exact cell34 h n11 n20 n53 n82

private theorem cover11 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n72 : Neg r 7 2) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell30 h n11 n72 n80
  · exact cell31 h n20 n81
  · exact cover10 h n11 n20 n82 o5 p
  · exact cell35 h n72 n83

private theorem cover12 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n72 : Neg r 7 2) (o1 : Outside r 1) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell29 h n10 n20 n72 p
  · exact cover11 h n11 n20 n72 o5 o8 p
  · exact cell5 h n12 n20 p
  · exact cell19 h n13 n72

private theorem cover13 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (n42 : Neg r 4 2) (o1 : Outside r 1) (o3 : Outside r 3) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cover9 h n20 n42 n70 o1 o3 p
  · exact cell28 h n20 n71 p
  · exact cover12 h n20 n72 o1 o5 o8 p
  · exact cell36 h n42 n73 p

private theorem cover14 {r : Register} (h : Hyp r) (n20 : Neg r 2 0) (o1 : Outside r 1) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cover6 h n20 n40 o1 o3 o5 o7 o8 p
  · exact cell21 h n20 n41 p
  · exact cover13 h n20 n42 o1 o3 o5 o7 o8 p
  · exact cell37 h n43 p

private theorem cover15 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n82 : Neg r 8 2) (o5 : Outside r 5) (p : Pos r 0) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell42 h n11 n22 n50 p
  · exact cell43 h n22 n51 n82 p
  · exact cell44 h n11 n22 n52 p
  · exact cell45 h n53 n82 p

private theorem cover16 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell40 h n11 n22 n80
  · exact cell41 h n81 p
  · exact cover15 h n11 n22 n82 o5 p
  · exact cell46 h n22 n83

private theorem cover17 {r : Register} (h : Hyp r) (n22 : Neg r 2 2) (o1 : Outside r 1) (o5 : Outside r 5) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell39 h n10 n22 p
  · exact cover16 h n11 n22 o5 o8 p
  · exact cell47 h n12 n22 p
  · exact cell48 h n13 n22

private theorem cover18 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o3 : Outside r 3) (o4 : Outside r 4) (o5 : Outside r 5) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 0) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover14 h n20 o1 o3 o4 o5 o7 o8 p
  · exact cell38 h n21 p
  · exact cover17 h n22 o1 o5 o8 p
  · exact cell49 h n23 p

private theorem cover19 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n51 : Neg r 5 1) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell54 h n21 n60 n81
  · exact cell55 h n11 n21 n51 n61 p
  · exact cell56 h n11 n21 n51 n62 n81 p
  · exact cell57 h n21 n63 p

private theorem cover20 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n51 : Neg r 5 1) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell58 h n11 n22 n51 n60 n81 p
  · exact cell59 h n11 n22 n51 n61 p
  · exact cell60 h n11 n51 n62 n81 p
  · exact cell61 h n22 n63 p

private theorem cover21 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (n81 : Neg r 8 1) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell53 h n20 n51 n81
  · exact cover19 h n11 n21 n51 n81 o6 p
  · exact cover20 h n11 n22 n51 n81 o6 p
  · exact cell62 h n23 p

private theorem cover22 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n73 : Neg r 7 3) (n83 : Neg r 8 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell67 h n20 n40 n51
  · exact cell68 h n11 n20 n41 p
  · exact cell69 h n11 n20 n42 n51 n73
  · exact cell70 h n11 n20 n43 n51 n73 n83 p

private theorem cover23 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n51 : Neg r 5 1) (n83 : Neg r 8 3) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell64 h n11 n20 n51 n70
  · exact cell65 h n11 n20 n51 n71 n83 p
  · exact cell66 h n20 n51 n72 n83
  · exact cover22 h n11 n20 n51 n73 n83 o4 p

private theorem cover24 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (n83 : Neg r 8 3) (o2 : Outside r 2) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover23 h n11 n20 n51 n83 o4 o7 p
  · exact cell71 h n11 n21 n51 n83 p
  · exact cell46 h n22 n83
  · exact cell62 h n23 p

private theorem cover25 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n51 : Neg r 5 1) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell52 h n11 n51 n80
  · exact cover21 h n11 n51 n81 o2 o6 p
  · exact cell63 h n11 n51 n82 p
  · exact cover24 h n11 n51 n83 o2 o4 o7 p

private theorem cover26 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n21 : Neg r 2 1) (n53 : Neg r 5 3) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell54 h n21 n60 n81
  · exact cell74 h n11 n21 n53 n61 n81 p
  · exact cell75 h n11 n21 n53 n62 n81 p
  · exact cell57 h n21 n63 p

private theorem cover27 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n22 : Neg r 2 2) (n53 : Neg r 5 3) (n81 : Neg r 8 1) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o6 with n60 | n61 | n62 | n63
  · exact cell76 h n22 n53 n60 n81 p
  · exact cell77 h n11 n22 n53 n61 p
  · exact cell78 h n11 n22 n53 n62 n81 p
  · exact cell61 h n22 n63 p

private theorem cover28 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n53 : Neg r 5 3) (n81 : Neg r 8 1) (o2 : Outside r 2) (o6 : Outside r 6) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cell31 h n20 n81
  · exact cover26 h n11 n21 n53 n81 o6 p
  · exact cover27 h n11 n22 n53 n81 o6 p
  · exact cell62 h n23 p

private theorem cover29 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n73 : Neg r 7 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell81 h n11 n40 n73
  · exact cell68 h n11 n20 n41 p
  · exact cell82 h n11 n20 n42 n73
  · exact cell83 h n11 n20 n43 n73 p

private theorem cover30 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n20 : Neg r 2 0) (n83 : Neg r 8 3) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell24 h n11 n70
  · exact cell80 h n20 n71 n83
  · exact cell35 h n72 n83
  · exact cover29 h n11 n20 n73 o4 p

private theorem cover31 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n53 : Neg r 5 3) (n83 : Neg r 8 3) (o2 : Outside r 2) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover30 h n11 n20 n83 o4 o7 p
  · exact cell84 h n11 n21 n53 n83 p
  · exact cell46 h n22 n83
  · exact cell62 h n23 p

private theorem cover32 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (n53 : Neg r 5 3) (o2 : Outside r 2) (o4 : Outside r 4) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o8 with n80 | n81 | n82 | n83
  · exact cell73 h n11 n80 p
  · exact cover28 h n11 n53 n81 o2 o6 p
  · exact cell79 h n11 n53 n82 p
  · exact cover31 h n11 n53 n83 o2 o4 o7 p

private theorem cover33 {r : Register} (h : Hyp r) (n11 : Neg r 1 1) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o5 with n50 | n51 | n52 | n53
  · exact cell51 h n11 n50 p
  · exact cover25 h n11 n51 o2 o4 o6 o7 o8 p
  · exact cell72 h n52 p
  · exact cover32 h n11 n53 o2 o4 o6 o7 o8 p

private theorem cover34 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (n73 : Neg r 7 3) (o4 : Outside r 4) (p : Pos r 9) : False := by
  rcases o4 with n40 | n41 | n42 | n43
  · exact cell88 h n13 n40 n73 p
  · exact cell89 h n13 n20 n41 n73 p
  · exact cell90 h n42 n73 p
  · exact cell91 h n13 n20 n43 p

private theorem cover35 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (n20 : Neg r 2 0) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o7 with n70 | n71 | n72 | n73
  · exact cell86 h n70 p
  · exact cell87 h n13 n20 n71
  · exact cell19 h n13 n72
  · exact cover34 h n13 n20 n73 o4 p

private theorem cover36 {r : Register} (h : Hyp r) (n13 : Neg r 1 3) (o2 : Outside r 2) (o4 : Outside r 4) (o7 : Outside r 7) (p : Pos r 9) : False := by
  rcases o2 with n20 | n21 | n22 | n23
  · exact cover35 h n13 n20 o4 o7 p
  · exact cell92 h n13 n21 p
  · exact cell48 h n13 n22
  · exact cell93 h n13 n23 p

private theorem cover37 {r : Register} (h : Hyp r) (o1 : Outside r 1) (o2 : Outside r 2) (o4 : Outside r 4) (o5 : Outside r 5) (o6 : Outside r 6) (o7 : Outside r 7) (o8 : Outside r 8) (p : Pos r 9) : False := by
  rcases o1 with n10 | n11 | n12 | n13
  · exact cell50 h n10 p
  · exact cover33 h n11 o2 o4 o5 o6 o7 o8 p
  · exact cell85 h n12 p
  · exact cover36 h n13 o2 o4 o7 p

private theorem cover38 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 1) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell94 h n00 p
  · exact cell95 h n01 p
  · exact cell96 h n02 p
  · exact cell97 h n03 p

private theorem cover39 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 2) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell98 h n90 p
  · exact cell99 h n91 p
  · exact cell100 h n92 p
  · exact cell101 h n93 p

private theorem cover40 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 3) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell102 h n00 p
  · exact cell103 h n01 p
  · exact cell104 h n02 p
  · exact cell105 h n03 p

private theorem cover41 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 4) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell106 h n90 p
  · exact cell107 h n91 p
  · exact cell108 h n92 p
  · exact cell109 h n93 p

private theorem cover42 {r : Register} (h : Hyp r) (o0 : Outside r 0) (p : Pos r 5) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell110 h n00 p
  · exact cell111 h n01 p
  · exact cell112 h n02 p
  · exact cell113 h n03 p

private theorem cover43 {r : Register} (h : Hyp r) (o9 : Outside r 9) (p : Pos r 6) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell114 h n90 p
  · exact cell115 h n91 p
  · exact cell116 h n92 p
  · exact cell117 h n93 p

private theorem cover44 {r : Register} (h : Hyp r) (n03 : Neg r 0 3) (o9 : Outside r 9) (p : Pos r 7) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell121 h n03 n90 p
  · exact cell122 h n91 p
  · exact cell123 h n92 p
  · exact cell124 h n93 p

private theorem cover45 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 7) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell118 h n00 p
  · exact cell119 h n01 p
  · exact cell120 h n02 p
  · exact cover44 h n03 o9 p

private theorem cover46 {r : Register} (h : Hyp r) (n01 : Neg r 0 1) (o9 : Outside r 9) (p : Pos r 8) : False := by
  rcases o9 with n90 | n91 | n92 | n93
  · exact cell126 h n01 n90
  · exact cell127 h n91 p
  · exact cell128 h n01 n92 p
  · exact cell129 h n93 p

private theorem cover47 {r : Register} (h : Hyp r) (o0 : Outside r 0) (o9 : Outside r 9) (p : Pos r 8) : False := by
  rcases o0 with n00 | n01 | n02 | n03
  · exact cell125 h n00 p
  · exact cover46 h n01 o9 p
  · exact cell130 h n02 p
  · exact cell131 h n03 p

private theorem valid {r : Register} (h : Regular r false 0) (i : Fin 10) (j : Fin 4) :
    ((Piece r i.val).line r false 0 j).valid := by
  have a := h.scale
  have b := h.oddSize
  have c := h.evenSize
  have d := h.run
  have n := h.num
  have g := h.den
  fin_cases i <;> fin_cases j <;>
    norm_num [Piece,mixed,Shape.line,Shape.probe,Probe.line,Line.valid,orientation,
      Prod.smul_mk,Fin.ext_iff] at * <;> omega

private theorem inclusion0 {r : Register} (h : Hyp r) (yes : (Piece r 0).contains r false 0) :
    (Piece r 1).contains r false 0 ∨ (Piece r 2).contains r false 0 ∨ (Piece r 3).contains r false 0 ∨ (Piece r 4).contains r false 0 ∨ (Piece r 5).contains r false 0 ∨ (Piece r 6).contains r false 0 ∨ (Piece r 7).contains r false 0 ∨ (Piece r 8).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 0) r false 0 (valid h.regular 0) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover18 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 3 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

private theorem inclusion1 {r : Register} (h : Hyp r) (yes : (Piece r 1).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 1) r false 0 (valid h.regular 1) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover38 h (outside 0 (by tauto)) p

private theorem inclusion2 {r : Register} (h : Hyp r) (yes : (Piece r 2).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 2) r false 0 (valid h.regular 2) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover39 h (outside 9 (by tauto)) p

private theorem inclusion3 {r : Register} (h : Hyp r) (yes : (Piece r 3).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 3) r false 0 (valid h.regular 3) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover40 h (outside 0 (by tauto)) p

private theorem inclusion4 {r : Register} (h : Hyp r) (yes : (Piece r 4).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 4) r false 0 (valid h.regular 4) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover41 h (outside 9 (by tauto)) p

private theorem inclusion5 {r : Register} (h : Hyp r) (yes : (Piece r 5).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 5) r false 0 (valid h.regular 5) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover42 h (outside 0 (by tauto)) p

private theorem inclusion6 {r : Register} (h : Hyp r) (yes : (Piece r 6).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 6) r false 0 (valid h.regular 6) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover43 h (outside 9 (by tauto)) p

private theorem inclusion7 {r : Register} (h : Hyp r) (yes : (Piece r 7).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 7) r false 0 (valid h.regular 7) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover45 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion8 {r : Register} (h : Hyp r) (yes : (Piece r 8).contains r false 0) :
    (Piece r 0).contains r false 0 ∨ (Piece r 9).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 8) r false 0 (valid h.regular 8) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover47 h (outside 0 (by tauto)) (outside 9 (by tauto)) p

private theorem inclusion9 {r : Register} (h : Hyp r) (yes : (Piece r 9).contains r false 0) :
    (Piece r 1).contains r false 0 ∨ (Piece r 2).contains r false 0 ∨ (Piece r 3).contains r false 0 ∨ (Piece r 4).contains r false 0 ∨ (Piece r 5).contains r false 0 ∨ (Piece r 6).contains r false 0 ∨ (Piece r 7).contains r false 0 ∨ (Piece r 8).contains r false 0 := by
  by_contra no
  have p := Shape.inside_bounds (Piece r 9) r false 0 (valid h.regular 9) yes
  have outside (i : Fin 10) (miss : ¬(Piece r i.val).contains r false 0) : Outside r i.val :=
    Shape.outside_bounds _ _ _ _ (valid h.regular i) miss
  exact cover37 h (outside 1 (by tauto)) (outside 2 (by tauto)) (outside 4 (by tauto)) (outside 5 (by tauto)) (outside 6 (by tauto)) (outside 7 (by tauto)) (outside 8 (by tauto)) p

/-- At an admissible register the target and the union of the component polygons contain the same site. -/
theorem coverage (r : Register) (regular : Regular r false 0) (multiple : r.M ∣ r.S) (scaleRun : r.S=r.M)
    (lattice : ∀ i : Fin 10, (mixed r false (-1) true i.val).lattice r (-1) false 0) :
    ((mixed r false (-1) true 0).contains r false 0 ∨ (mixed r false (-1) true 9).contains r false 0) ↔ ∃ i : Fin 8, (mixed r false (-1) true (i.val+1)).contains r false 0 := by
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

end FLatticePaper.Tiles.MixedRegisterEvenTwoDirectLowEven
