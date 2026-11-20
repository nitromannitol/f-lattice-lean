import FLattice.Auxiliary.PlusOddActiveRegion
import FLattice.Auxiliary.PlusOddPredecessors
import FLattice.Auxiliary.DirectionalRank
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Physical incoming selections in the smaller odd contact region

The active region contains diagonal-period translates only. Each selected
edge is given an actual lift with horizontal period index zero. The count
uses the displayed cell deficit table, whose physical identification is
proved separately. No periodicity or bound on an unknown comparison gap is
assumed here.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile DirectionalRank

private theorem point_at_cell {m : Parameter} (c : Cell m) (i : Fin 2) :
    incomingPoint c.x c.y i =
      if ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) % 2 = 0 then
        (c.x + (if i = 0 then -1 else 1), c.y)
      else (c.x, c.y + (if i = 0 then -1 else 1)) := by
  have h : c.x + c.y + 1 =
      2 * (m.val * c.r + c.s) + ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) := by
    unfold Cell.x Cell.y
    ring
  have hp : (c.x + c.y + 1) % 2 =
      ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) % 2 := by rw [h]; omega
  simp only [incomingPoint, hp]

private theorem active_input_of_lift {m : Parameter} (c : Cell m) (i : Fin 2)
    (d : Cell m) (hd : cellActive d) (k : ℤ)
    (hx : (incomingPoint c.x c.y i).1 = d.x + 2 * m.val * k)
    (hy : (incomingPoint c.x c.y i).2 = 2 * k + d.y) :
    activePoint m (incomingPoint c.x c.y i).1 (incomingPoint c.x c.y i).2 :=
  ⟨d, hd, k, hx, hy⟩

private theorem active_00_down {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hc : cellActive c)
    (hSide : c.r = 0 ∨ c.r ≤ c.s) :
    activePoint m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 := by
  have hm := m.property
  have hs0 := c.hs0
  have hsm := c.hsm
  have hr0 := c.hr0
  have ha := hc
  norm_num [cellActive, he, hv] at ha
  obtain ⟨hr, hs, ee, vv⟩ := incomingCell_00_down_inner c he hv (by omega) (by omega)
  refine active_input_of_lift c 0 (incomingCell c 0) ?_ (-1) ?_ ?_
  · norm_num [cellActive, hr, hs, ee, vv]
    omega
  · rw [point_at_cell]
    norm_num [Cell.x, he, hv, hr, hs, ee, vv]
    ring
  · rw [point_at_cell]
    norm_num [Cell.y, he, hv, ee]

private theorem active_00_up {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 0) (hc : cellActive c) (hRow : 1 ≤ c.r) :
    activePoint m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 := by
  have ha := hc
  norm_num [cellActive, he, hv] at ha
  obtain ⟨hr, hs, ee, vv⟩ := incomingCell_00_up c he hv
  refine active_input_of_lift c 1 (incomingCell c 1) ?_ 0 ?_ ?_
  · norm_num [cellActive, hr, hs, ee, vv]
    omega
  · rw [point_at_cell]
    norm_num [Cell.x, he, hv, hr, hs, ee, vv]
  · rw [point_at_cell]
    norm_num [Cell.y, he, hv, ee]

private theorem active_01_left {m : Parameter} (c : Cell m)
    (he : c.e = 0) (hv : c.v = 1) (hc : cellActive c) :
    activePoint m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 := by
  obtain ⟨hr, hs, ee, vv⟩ := incomingCell_01_left c he hv
  refine active_input_of_lift c 0 (incomingCell c 0) ?_ 0 ?_ ?_
  · simpa [cellActive, hr, hs, ee, vv, he, hv] using hc
  · rw [point_at_cell]
    norm_num [Cell.x, he, hv, hr, hs, ee, vv]
  · rw [point_at_cell]
    norm_num [Cell.y, he, hv, ee]

private theorem active_10_left {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 0) (hc : cellActive c) :
    activePoint m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 := by
  have hm := m.property
  have hs0 := c.hs0
  have hsm := c.hsm
  have ha := hc
  norm_num [cellActive, he, hv] at ha
  by_cases hz : c.s = 0
  · have hRow : c.r = 1 := by omega
    obtain ⟨hr, hs, ee, vv⟩ := incomingCell_10_left_of_zero c he hv hz (by omega)
    refine active_input_of_lift c 0 (incomingCell c 0) ?_ 0 ?_ ?_
    · norm_num [cellActive, hr, hs, ee, vv, hRow]
    · rw [point_at_cell]
      norm_num [Cell.x, he, hv, hr, hs, ee, vv, hz, hRow]
      ring
    · rw [point_at_cell]
      norm_num [Cell.y, he, hv, ee]
  · obtain ⟨hr, hs, ee, vv⟩ := incomingCell_10_left_of_pos c he hv (by omega)
    refine active_input_of_lift c 0 (incomingCell c 0) ?_ 0 ?_ ?_
    · norm_num [cellActive, hr, hs, ee, vv]
      omega
    · rw [point_at_cell]
      norm_num [Cell.x, he, hv, hr, hs, ee, vv]
      ring
    · rw [point_at_cell]
      norm_num [Cell.y, he, hv, ee]

private theorem active_11_down {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hc : cellActive c)
    (hSide : c.r = 0 ∨ c.r - 1 ≤ c.s) :
    activePoint m (incomingPoint c.x c.y 0).1 (incomingPoint c.x c.y 0).2 := by
  have ha := hc
  norm_num [cellActive, he, hv] at ha
  obtain ⟨hr, hs, ee, vv⟩ := incomingCell_11_down c he hv
  refine active_input_of_lift c 0 (incomingCell c 0) ?_ 0 ?_ ?_
  · norm_num [cellActive, hr, hs, ee, vv]
    omega
  · rw [point_at_cell]
    norm_num [Cell.x, he, hv, hr, hs, ee, vv]
  · rw [point_at_cell]
    norm_num [Cell.y, he, hv, ee]

private theorem active_11_up {m : Parameter} (c : Cell m)
    (he : c.e = 1) (hv : c.v = 1) (hc : cellActive c) (hRow : 1 ≤ c.r) :
    activePoint m (incomingPoint c.x c.y 1).1 (incomingPoint c.x c.y 1).2 := by
  have ha := hc
  norm_num [cellActive, he, hv] at ha
  obtain ⟨hr, hs, ee, vv⟩ := incomingCell_11_up_of_pos c he hv hRow
  refine active_input_of_lift c 1 (incomingCell c 1) ?_ 1 ?_ ?_
  · norm_num [cellActive, hr, hs, ee, vv]
    omega
  · rw [point_at_cell]
    norm_num [Cell.x, he, hv, hr, hs, ee, vv]
    ring
  · rw [point_at_cell]
    norm_num [Cell.y, he, hv, ee]

private def goodInput {m : Parameter} (c : Cell m) (i : Fin 2) : Prop :=
  activePoint m (incomingPoint c.x c.y i).1 (incomingPoint c.x c.y i).2 ∧
    (c.e = c.v ∨ i = 0)

private theorem active_inputs {m : Parameter} (c : Cell m) (hc : cellActive c) :
    (goodInput c 0 ∨ goodInput c 1) ∧
    (cellDeficitTable c = 1 → goodInput c 0 ∧ goodInput c 1) := by
  have hm := m.property
  have hr0 := c.hr0
  have hs0 := c.hs0
  have hsm := c.hsm
  rcases (show c.e = 0 ∨ c.e = 1 by omega) with he | he <;>
    rcases (show c.v = 0 ∨ c.v = 1 by omega) with hv | hv
  · have ha := hc
    norm_num [cellActive, he, hv] at ha
    constructor
    · by_cases hz : c.r = 0
      · exact Or.inl ⟨active_00_down c he hv hc (Or.inl hz), Or.inl (he.trans hv.symm)⟩
      · exact Or.inr ⟨active_00_up c he hv hc (by omega), Or.inl (he.trans hv.symm)⟩
    · intro hBlack
      have hRow : 1 ≤ c.r := by
        norm_num [cellDeficitTable, he, hv] at hBlack
        omega
      have hSide : c.r ≤ c.s := by
        norm_num [cellDeficitTable, he, hv] at hBlack
        omega
      exact ⟨⟨active_00_down c he hv hc (Or.inr hSide), Or.inl (he.trans hv.symm)⟩,
        ⟨active_00_up c he hv hc hRow, Or.inl (he.trans hv.symm)⟩⟩
  · refine ⟨Or.inl ⟨active_01_left c he hv hc, Or.inr rfl⟩, ?_⟩
    intro hBlack
    norm_num [cellActive, he, hv] at hc
    norm_num [cellDeficitTable, he, hv] at hBlack
    omega
  · refine ⟨Or.inl ⟨active_10_left c he hv hc, Or.inr rfl⟩, ?_⟩
    intro hBlack
    norm_num [cellActive, he, hv] at hc
    norm_num [cellDeficitTable, he, hv] at hBlack
    omega
  · have ha := hc
    norm_num [cellActive, he, hv] at ha
    constructor
    · by_cases hz : c.r = 0
      · exact Or.inl ⟨active_11_down c he hv hc (Or.inl hz), Or.inl (he.trans hv.symm)⟩
      · exact Or.inr ⟨active_11_up c he hv hc (by omega), Or.inl (he.trans hv.symm)⟩
    · intro hBlack
      have hRow : 1 ≤ c.r := by
        norm_num [cellDeficitTable, he, hv] at hBlack
        omega
      have hSide : c.r - 1 ≤ c.s := by
        norm_num [cellDeficitTable, he, hv] at hBlack
        omega
      exact ⟨⟨active_11_down c he hv hc (Or.inr hSide), Or.inl (he.trans hv.symm)⟩,
        ⟨active_11_up c he hv hc hRow, Or.inl (he.trans hv.symm)⟩⟩

private theorem active_representative_selected {m : Parameter} (c : Cell m)
    (hc : cellActive c) :
    ∃ S : Finset (Fin 2), cellDeficitTable c < (S.card : ℤ) ∧
      ∀ i ∈ S, goodInput c i := by
  obtain ⟨hOne, hBoth⟩ := active_inputs c hc
  rcases cellDeficitTable_zero_or_one c (cellActive_not_prescribed c hc) with hz | hu
  · rcases hOne with hLeft | hRight
    · refine ⟨{0}, ?_, ?_⟩
      · norm_num [hz]
      · intro i hi
        simpa only [Finset.mem_singleton.mp hi] using hLeft
    · refine ⟨{1}, ?_, ?_⟩
      · norm_num [hz]
      · intro i hi
        simpa only [Finset.mem_singleton.mp hi] using hRight
  · obtain ⟨hLeft, hRight⟩ := hBoth hu
    refine ⟨Finset.univ, ?_, ?_⟩
    · norm_num [hu]
    · intro i _
      fin_cases i
      · exact hLeft
      · exact hRight

private theorem incoming_rank_drop (x y : ℤ) (i : Fin 2)
    (hDirection : (x + y + 1) % 2 ≠ 0 ∨ i = 0) :
    leftRank (incomingPoint x y i).1 ((incomingPoint x y i).2 + 1) <
      leftRank x (y + 1) := by
  by_cases hp : (x + y + 1) % 2 = 0
  · have hi : i = 0 := hDirection.resolve_left (not_not.mpr hp)
    subst i
    norm_num [incomingPoint, hp, leftRank]
    omega
  · fin_cases i <;> norm_num [incomingPoint, hp, leftRank] <;> omega

private theorem representative_rank_drop {m : Parameter} (c : Cell m) (i : Fin 2)
    (hDirection : c.e = c.v ∨ i = 0) :
    leftRank (incomingPoint c.x c.y i).1 ((incomingPoint c.x c.y i).2 + 1) <
      leftRank c.x (c.y + 1) := by
  apply incoming_rank_drop
  rcases hDirection with hEqual | hi
  · left
    have he := c.e.isLt
    have hv := c.v.isLt
    have h : c.x + c.y + 1 = 2 * (m.val * c.r + c.s) +
        ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) := by
      unfold Cell.x Cell.y
      ring
    rw [h, hEqual]
    omega
  · exact Or.inr hi

private theorem activePoint_add_diagonal (m : Parameter) (x y k : ℤ)
    (hActive : activePoint m x y) :
    activePoint m (x + 2 * m.val * k) (y + 2 * k) := by
  obtain ⟨c, hc, j, hx, hy⟩ := hActive
  refine ⟨c, hc, j + k, ?_, ?_⟩
  · rw [hx]
    ring
  · rw [hy]
    ring

/-- A physical incoming selection stays in the diagonal-period active region,
contains more indices than the displayed deficit, and strictly lowers the
physical left rank. This statement does not use a physical deficit identity. -/
theorem activePoint_selected (m : Parameter) (x y : ℤ)
    (hActive : activePoint m x y) :
    ∃ S : Finset (Fin 2), cellDeficitTable (cellOf m x y) < (S.card : ℤ) ∧
      ∀ i ∈ S,
        activePoint m (incomingPoint x y i).1 (incomingPoint x y i).2 ∧
        leftRank (incomingPoint x y i).1 ((incomingPoint x y i).2 + 1) <
          leftRank x (y + 1) := by
  obtain ⟨c, hc, k, hx, hy⟩ := hActive
  obtain ⟨S, hCount, hSelected⟩ := active_representative_selected c hc
  have hDecode := cellOf_lifted_cell m c k 0
  simp only [mul_zero, add_zero] at hDecode
  rw [← hx, ← hy] at hDecode
  refine ⟨S, by simpa only [hDecode] using hCount, ?_⟩
  have hEven : (2 * m.val * k + 2 * k) % 2 = 0 := by
    have h : 2 * m.val * k + 2 * k = 2 * (m.val * k + k) := by ring
    rw [h]
    omega
  intro i hi
  obtain ⟨hInput, hDirection⟩ := hSelected i hi
  have hPoint := incomingPoint_add_of_even c.x c.y (2 * m.val * k) (2 * k) i hEven
  have hy' : y = c.y + 2 * k := by omega
  rw [← hx, ← hy'] at hPoint
  constructor
  · rw [hPoint]
    exact activePoint_add_diagonal m _ _ k hInput
  · have hRank := representative_rank_drop c i hDirection
    rw [hPoint]
    change leftRank ((incomingPoint c.x c.y i).1 + 2 * m.val * k)
      ((incomingPoint c.x c.y i).2 + 2 * k + 1) < leftRank x (y + 1)
    rw [show (incomingPoint c.x c.y i).2 + 2 * k + 1 =
      ((incomingPoint c.x c.y i).2 + 1) + 2 * k by ring]
    rw [leftRank_add_of_even _ _ _ _ hEven, hx, hy']
    rw [show c.y + 2 * k + 1 = (c.y + 1) + 2 * k by ring,
      leftRank_add_of_even _ _ _ _ hEven]
    omega

end FLattice.Auxiliary.PlusOddProfile
