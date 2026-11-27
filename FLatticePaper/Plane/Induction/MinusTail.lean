import FLatticePaper.Plane.Induction.MinusRowH
import FLatticePaper.Plane.Induction.HardVFanBlocks
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.RowVEasy
import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.FreeRows

/-! # The minus tail of the hard V block (Q41 section 4, block 2): positions and the translated fan map

The minus tail `V_{-1}, …, V_{r+1-L}` follows the H block. Its entry `V_m` sits at position `r + d − m` of the minus row. The fan of a
tail entry is taken in the physical map `Y q = Zs q − V` (the translation by the deck vector `V`, an even shift), so the input
correspondence, the laplacian and the nonfreeness transfer by the even shift `V`. -/

namespace FLatticePaper.MinusTail

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows FLatticePaper.MinusRowWiring FLatticePaper.RefuteTree
  FLatticePaper.RotatedCap FLatticePaper.HardVFanBlocks

theorem minusRow_get_Vtail (r L d m : ℤ) (hr : 0 ≤ r) (hd : 1 ≤ d) (hm1 : r + 1 - L ≤ m) (hm2 : m ≤ -1) :
    (minusRow r L d)[(r + d - m).toNat]? = some (FreeLabel.V m) := by
  unfold minusRow
  rw [List.getElem?_append_right (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  have hsub : (r + d - m).toNat - ((((List.range r.toNat).map fun i : ℕ => FreeLabel.V (r - (i : ℤ))) ++
      [FreeLabel.H 0, FreeLabel.V 0]) ++ ((List.range (d - 1).toNat).map fun i : ℕ => FreeLabel.H (-1 - (i : ℤ)))).length =
      (-1 - m).toNat := by
    simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
    omega
  rw [hsub, List.getElem?_map, List.getElem?_range (by omega)]
  have e : (-1 - ((-1 - m).toNat : ℤ)) = m := by omega
  simp only [Option.map_some, e]

/-- The minus-row position of the tail entry `V_m`, as a site. -/
theorem minusSites_Vtail (frame : ChildFrame) (r m : ℤ) (hr : 0 ≤ r) (hm1 : r + 1 - (frame.child.den + frame.child.num) ≤ m)
    (hm2 : m ≤ -1) :
    (minusSites frame r)[(r + frame.child.den - m).toNat]? = some (RowAt.vAt frame m) := by
  unfold minusSites rowSites
  have hd : 1 ≤ frame.child.den := by
    obtain ⟨-, hlt, -, -, -⟩ := frame.child_facts
    omega
  rw [List.getElem?_map, minusRow_get_Vtail r _ _ m hr hd hm1 hm2]
  simp [labelSite]

/-- The incoming sites commute with the even shift `−V`. -/
theorem incoming_sub_V (frame : ChildFrame) (x : Site) :
    incomingNeg (x - RowAt.Vvec frame) = incomingNeg x - RowAt.Vvec frame ∧
      incomingPos (x - RowAt.Vvec frame) = incomingPos x - RowAt.Vvec frame := by
  have hV : EvenSite (-RowAt.Vvec frame) := by
    unfold EvenSite RowAt.Vvec
    simp only [Prod.fst_neg, Prod.snd_neg]
    omega
  constructor
  · rw [sub_eq_add_neg, sub_eq_add_neg, ForcedArrows.incomingNeg_add_even hV]
  · rw [sub_eq_add_neg, sub_eq_add_neg, ForcedArrows.incomingPos_add_even hV]

/-- The input correspondence of the translated map `Y q = Zs q − V`. -/
theorem tail_inputs (frame : ChildFrame) (q : Site) :
    (Zs (incomingNeg q) - RowAt.Vvec frame = incomingNeg (Zs q - RowAt.Vvec frame) ∧
        Zs (incomingPos q) - RowAt.Vvec frame = incomingPos (Zs q - RowAt.Vvec frame)) ∨
    (Zs (incomingNeg q) - RowAt.Vvec frame = incomingPos (Zs q - RowAt.Vvec frame) ∧
        Zs (incomingPos q) - RowAt.Vvec frame = incomingNeg (Zs q - RowAt.Vvec frame)) := by
  rcases zs_inputs q with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [h1, h2]
    exact ⟨(incoming_sub_V frame (Zs q)).1.symm, (incoming_sub_V frame (Zs q)).2.symm⟩
  · right
    rw [h1, h2]
    exact ⟨(incoming_sub_V frame (Zs q)).2.symm, (incoming_sub_V frame (Zs q)).1.symm⟩

end FLatticePaper.MinusTail
