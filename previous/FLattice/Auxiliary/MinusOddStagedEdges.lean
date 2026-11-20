import FLattice.Auxiliary.MinusOddRegionEdges
import FLattice.Auxiliary.DirectionalRank

/-!
# Three-region ordering on actual odd-minus incoming edges

The cell stages are A, B, C, followed by the prescribed class. The physical
rank is left-moving on B and right-moving on the other stages. It may be
unbounded on the plane. The final selection counts actual incoming indices
and allows prescribed exits, with no periodicity premise on any unknown.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusProfile

open PlusEvenProfile PlusOddProfile DirectionalRank

/-- The complete source partition: A=0, B=1, C=2, prescribed=3. -/
noncomputable def oddCellStage {m : Parameter} (c : Cell m) : ℕ := by
  classical
  exact if oddRegionA c then 0 else if oddRegionB c then 1 else
    if oddCellPrescribed c then 3 else 2

theorem oddCellStage_of_A {m : Parameter} (c : Cell m) (h : oddRegionA c) :
    oddCellStage c = 0 := by simp [oddCellStage, h]

theorem oddCellStage_of_B {m : Parameter} (c : Cell m) (h : oddRegionB c) :
    oddCellStage c = 1 := by
  have ha : ¬oddRegionA c := fun ha => oddRegionA_not_B c ha h
  simp [oddCellStage, ha, h]

theorem oddCellStage_of_C {m : Parameter} (c : Cell m) (h : oddRegionC c) :
    oddCellStage c = 2 := by simp [oddCellStage, h.1, h.2.1, h.2.2]

theorem oddCellStage_of_prescribed {m : Parameter} (c : Cell m)
    (h : oddCellPrescribed c) : oddCellStage c = 3 := by
  have ha : ¬oddRegionA c := fun ha => oddRegionA_not_prescribed c ha h
  have hb : ¬oddRegionB c := fun hb => oddRegionB_not_prescribed c hb h
  simp [oddCellStage, ha, hb, h]

/-- No stage fallback hides an unclassified cell. -/
theorem oddCellStage_cases {m : Parameter} (c : Cell m) :
    (oddCellStage c = 0 ∧ oddRegionA c) ∨
    (oddCellStage c = 1 ∧ oddRegionB c) ∨
    (oddCellStage c = 2 ∧ oddRegionC c) ∨
    (oddCellStage c = 3 ∧ oddCellPrescribed c) := by
  rcases odd_region_cover c with hp | ha | hb | hc
  · exact Or.inr (Or.inr (Or.inr ⟨oddCellStage_of_prescribed c hp, hp⟩))
  · exact Or.inl ⟨oddCellStage_of_A c ha, ha⟩
  · exact Or.inr (Or.inl ⟨oddCellStage_of_B c hb, hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨oddCellStage_of_C c hc, hc⟩))

/-- Selected cell edges enter a pin, enter an earlier region, or use the
appropriate physical direction within the same region. -/
theorem odd_cell_selected {m : Parameter} (c : Cell m) (hNotPin : ¬oddCellPrescribed c) :
    ∃ S : Finset (Fin 2), oddCellDeficit c < (S.card : ℤ) ∧ ∀ i ∈ S,
      oddCellPrescribed (incomingCell c i) ∨
      oddCellStage (incomingCell c i) < oddCellStage c ∨
      (oddCellStage (incomingCell c i) = oddCellStage c ∧
        (c.e = c.v ∨ i = (if oddCellStage c = 1 then 0 else 1))) := by
  rcases odd_region_cover c with hp | ha | hb | hc
  · exact False.elim (hNotPin hp)
  · obtain ⟨S, hCount, hMove⟩ := oddRegionA_selected c ha
    have hs := oddCellStage_of_A c ha
    refine ⟨S, hCount, ?_⟩
    intro i hi
    rcases hMove i hi with hp | ⟨hd, hDir⟩
    · exact Or.inl hp
    · have hds := oddCellStage_of_A (incomingCell c i) hd
      exact Or.inr (Or.inr ⟨by omega, by simpa [hs] using hDir⟩)
  · obtain ⟨S, hCount, hMove⟩ := oddRegionB_selected c hb
    have hs := oddCellStage_of_B c hb
    refine ⟨S, hCount, ?_⟩
    intro i hi
    rcases hMove i hi with hp | ha | ⟨hd, hDir⟩
    · exact Or.inl hp
    · have hds := oddCellStage_of_A (incomingCell c i) ha
      exact Or.inr (Or.inl (by omega))
    · have hds := oddCellStage_of_B (incomingCell c i) hd
      exact Or.inr (Or.inr ⟨by omega, by simpa [hs] using hDir⟩)
  · obtain ⟨S, hCount, hMove⟩ := oddRegionC_selected c hc
    have hs := oddCellStage_of_C c hc
    refine ⟨S, hCount, ?_⟩
    intro i hi
    rcases hMove i hi with hp | ha | hb | ⟨hd, hDir⟩
    · exact Or.inl hp
    · have hds := oddCellStage_of_A (incomingCell c i) ha
      exact Or.inr (Or.inl (by omega))
    · have hds := oddCellStage_of_B (incomingCell c i) hb
      exact Or.inr (Or.inl (by omega))
    · have hds := oddCellStage_of_C (incomingCell c i) hd
      exact Or.inr (Or.inr ⟨by omega, by simpa [hs] using hDir⟩)

/-- Decoding commutes with an actual incoming step at every signed physical point. -/
theorem odd_cellOf_incomingPoint (m : Parameter) (x y : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2 =
      incomingCell (cellOf m x y) i := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := cellOf_incomingPoint_lifted_cell m (cellOf m x y) k q i
  rw [← hx, ← hy] at h
  exact h

private theorem physical_vertical_of_equal (m : Parameter) (x y : ℤ)
    (hEqual : (cellOf m x y).e = (cellOf m x y).v) :
    (x + y + 1) % 2 = 1 := by
  let c := cellOf m x y
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h : x + y + 1 =
      2 * (m.val * c.r + c.s + m.val * k + halfPeriod m * q + k) +
        ((c.e.val : ℤ) + (c.v.val : ℤ) + 1) := by
    calc
      _ = (c.x + 2 * m.val * k + 2 * halfPeriod m * q) + (2 * k + c.y) + 1 := by
        rw [← hx, ← hy]
      _ = _ := by unfold Cell.x Cell.y; ring
  have he := c.e.isLt
  have hv := c.v.isLt
  have heq : (c.e.val : ℤ) = (c.v.val : ℤ) := by rw [hEqual]
  rw [h]
  omega

/-- The source rank is left-moving on B and right-moving on A and C. -/
noncomputable def oddPhysicalRank (m : Parameter) (x y : ℤ) : ℤ :=
  if oddCellStage (cellOf m x y) = 1 then leftRank x (y + 1) else rightRank x (y + 1)

/-- A permitted same-stage incoming edge strictly lowers the actual physical rank. -/
theorem oddPhysicalRank_incoming (m : Parameter) (x y : ℤ) (i : Fin 2)
    (hSame : oddCellStage (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) =
      oddCellStage (cellOf m x y))
    (hDirection : (cellOf m x y).e = (cellOf m x y).v ∨
      i = (if oddCellStage (cellOf m x y) = 1 then 0 else 1)) :
    oddPhysicalRank m (incomingPoint x y i).1 (incomingPoint x y i).2 <
      oddPhysicalRank m x y := by
  have hd : (x + y + 1) % 2 = 1 ∨
      i = (if oddCellStage (cellOf m x y) = 1 then 0 else 1) := by
    rcases hDirection with he | hi
    · exact Or.inl (physical_vertical_of_equal m x y he)
    · exact Or.inr hi
  unfold oddPhysicalRank
  rw [hSame]
  split_ifs with hs
  · simp only [if_pos hs] at hd
    unfold incomingPoint leftRank
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      split_ifs <;> norm_num at * <;> omega
  · simp only [if_neg hs] at hd
    unfold incomingPoint rightRank
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      split_ifs <;> norm_num at * <;> omega

/-- The complete physical count/rank obligation, with prescribed exits allowed. -/
theorem odd_physical_selected (m : Parameter) (x y : ℤ)
    (hNotPin : ¬oddCellPrescribed (cellOf m x y)) :
    ∃ S : Finset (Fin 2), incomingDeficit m 1 x y < (S.card : ℤ) ∧ ∀ i ∈ S,
      oddCellPrescribed (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) ∨
      oddCellStage (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) <
        oddCellStage (cellOf m x y) ∨
      (oddCellStage (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) =
        oddCellStage (cellOf m x y) ∧
        oddPhysicalRank m (incomingPoint x y i).1 (incomingPoint x y i).2 <
          oddPhysicalRank m x y) := by
  obtain ⟨S, hCount, hMove⟩ := odd_cell_selected (cellOf m x y) hNotPin
  refine ⟨S, ?_, ?_⟩
  · rw [odd_incomingDeficit_eq_cellTable]
    exact hCount
  · intro i hi
    have hDecode := odd_cellOf_incomingPoint m x y i
    rcases hMove i hi with hp | he | ⟨hs, hd⟩
    · exact Or.inl (hDecode.symm ▸ hp)
    · exact Or.inr (Or.inl (hDecode.symm ▸ he))
    · have hSame : oddCellStage (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) =
          oddCellStage (cellOf m x y) := hDecode.symm ▸ hs
      exact Or.inr (Or.inr ⟨hSame, oddPhysicalRank_incoming m x y i hSame hd⟩)

end FLattice.Auxiliary.MinusProfile
