import FLatticePaper.Plane.Induction.W1NonfreeOut

/-! # Task 91 (2): the sheet square with its output pointer and corner data

`sheet_squareOut_of_parent` transports `ParentSquareOut` (W1NonfreeOut) at the parent point `zTurn (c − lv)` to the sheet square at `c` for the
relation `sheetQ Q lv`, as `sheet_square_of_parent` does, and adds: the rejected output `o' = lv + zTurnInv o` of `c` is outside the sheet square,
the unique `sheetQ`-retained input of `c`, and each sheet corner's laplacian (read in parent coordinates) is `−1`, or `0` with its unique
retained input in the square. -/

namespace FLatticePaper.W1NonfreeSheet

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1SheetSquare FLatticePaper.W1PrivateSquare FLatticePaper.W1NonfreeOut

theorem zTurn_sheet_point (lv q : Site) : zTurn (lv + zTurnInv q - lv) = q := by
  rw [add_sub_cancel_left, zTurn_zTurnInv]

/-- A sheet point is determined by its parent image. -/
theorem eq_sheet_of_zTurn (lv j q : Site) (e : zTurn (j - lv) = q) : j = lv + zTurnInv q := by
  rw [← e, zTurnInv_zTurn]
  abel

/-- **The sheet square with output and corner data** (task 91 (2)). -/
theorem sheet_squareOut_of_parent {G : Field} {Q : Site → Site → Prop} {lv : Site} (hlv : EvenSite lv) (c : Site)
    (h : ParentSquareOut G Q (zTurn (c - lv))) :
    ∃ p0 p1 p2 o' : Site, ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
      p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
      ¬ sheetQ Q lv c p0 ∧ Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
      sheetQ Q lv p0 p1 ∧ sheetQ Q lv p1 p2 ∧ sheetQ Q lv p2 c ∧
      (o' = incomingNeg c ∨ o' = incomingPos c) ∧ o' ∉ squareCorners a b ∧ sheetQ Q lv c o' ∧
      (∀ j, sheetQ Q lv c j → j = o') ∧
      (laplacian G (zTurn (p0 - lv)) = -1 ∨
        (laplacian G (zTurn (p0 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p0 j → j = p1)) ∧
      (laplacian G (zTurn (p1 - lv)) = -1 ∨
        (laplacian G (zTurn (p1 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p1 j → j = p2)) ∧
      (laplacian G (zTurn (p2 - lv)) = -1 ∨
        (laplacian G (zTurn (p2 - lv)) = 0 ∧ ∀ j, sheetQ Q lv p2 j → j = c)) := by
  obtain ⟨q0, q1, q2, o, a, b, hz, hq0, hq1, hq2, hcov, hne01, hne12, hne02, hin, hrej, hE1, hE2, hE3,
    hR0, hR1, hR2, ho, hout, hRo, hun, hL0, hL1, hL2⟩ := h
  have hp : ∀ q : Site, zTurn (lv + zTurnInv q - lv) = q := zTurn_sheet_point lv
  refine ⟨lv + zTurnInv q0, lv + zTurnInv q1, lv + zTurnInv q2, lv + zTurnInv o, lv.1 + b + 1, lv.2 - a - 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_square_parent lv c a b).2 hz
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq0)
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq1)
  · exact (mem_square_parent lv _ a b).2 (by rw [hp]; exact hq2)
  · intro c' hc' hne
    have h' := (mem_square_parent lv c' a b).1 hc'
    have hne' : zTurn (c' - lv) ≠ zTurn (c - lv) := fun e => hne (sub_left_inj.mp ((zTurn_eq_iff _ _).1 e))
    rcases hcov (zTurn (c' - lv)) h' hne' with e | e | e
    · left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; left
      rw [← e, zTurnInv_zTurn]
      abel
    · right; right
      rw [← e, zTurnInv_zTurn]
      abel
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q1) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne01 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q1) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne12 h2
  · intro e
    have h2 : zTurn ((lv + zTurnInv q0) - lv) = zTurn ((lv + zTurnInv q2) - lv) := by rw [e]
    rw [hp, hp] at h2
    exact hne02 h2
  · exact (input_zTurn_iff lv c _ hlv).2 (by rw [hp]; exact hin)
  · unfold sheetQ
    rw [hp]
    exact hrej
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE1)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp, hp]; exact hE2)
  · exact (edge_zTurn_iff lv _ _ hlv).2 (by rw [hp]; exact hE3)
  · unfold sheetQ
    rw [hp, hp]
    exact hR0
  · unfold sheetQ
    rw [hp, hp]
    exact hR1
  · unfold sheetQ
    rw [hp]
    exact hR2
  · exact (input_zTurn_iff lv c _ hlv).2 (by rw [hp]; exact ho)
  · intro hm
    have hm' := (mem_square_parent lv _ a b).1 hm
    rw [hp] at hm'
    exact hout hm'
  · unfold sheetQ
    rw [hp]
    exact hRo
  · intro j hj
    have hj' : Q (zTurn (c - lv)) (zTurn (j - lv)) := hj
    exact eq_sheet_of_zTurn lv j o (hun _ hj')
  · rw [hp]
    rcases hL0 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q0 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      exact eq_sheet_of_zTurn lv j q1 (u _ hj')
  · rw [hp]
    rcases hL1 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q1 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      exact eq_sheet_of_zTurn lv j q2 (u _ hj')
  · rw [hp]
    rcases hL2 with e | ⟨e, u⟩
    · exact Or.inl e
    · refine Or.inr ⟨e, fun j hj => ?_⟩
      have hj' : Q (zTurn (lv + zTurnInv q2 - lv)) (zTurn (j - lv)) := hj
      rw [hp] at hj'
      have hcz : c = lv + zTurnInv (zTurn (c - lv)) := by
        rw [zTurnInv_zTurn]
        abel
      rw [hcz]
      exact eq_sheet_of_zTurn lv j _ (u _ hj')

end FLatticePaper.W1NonfreeSheet
