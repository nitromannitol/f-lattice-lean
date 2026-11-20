import FLattice.Auxiliary.PlusEvenCellCoset
import FLattice.Auxiliary.PlusEvenPredecessors
import FLattice.Auxiliary.DirectionalRank

/-!
# Physical edges, ranks and the first-region collar

The decoded cell labels below describe actual incoming points on the full
lattice. Their use imposes no periodicity assumption on a compared function.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

open DirectionalRank

/-- Taking an incoming edge and then decoding agrees with the representative edge. -/
theorem cellOf_incomingPoint (m : Parameter) (x y : ℤ) (i : Fin 2) :
    cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2 =
      incomingCell (cellOf m x y) i := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h := cellOf_incomingPoint_lifted_cell m (cellOf m x y) k q i
  rw [← hx, ← hy] at h
  exact h

/-- Cell states retain the literal parity of the physical point. -/
theorem cellOf_parity (m : Parameter) (x y : ℤ) :
    (x + y) % 2 =
      (((cellOf m x y).e.val : ℤ) + ((cellOf m x y).v.val : ℤ)) % 2 := by
  obtain ⟨k, q, hx, hy⟩ := exists_lifted_cell m x y
  have h : x + y = 2 * (m.val * (cellOf m x y).r + (cellOf m x y).s +
      m.val * k + halfPeriod m * q + k) +
      (((cellOf m x y).e.val : ℤ) + ((cellOf m x y).v.val : ℤ)) := by
    calc
      _ = ((cellOf m x y).x + 2 * m.val * k + 2 * halfPeriod m * q) +
          (2 * k + (cellOf m x y).y) := by rw [← hx, ← hy]
      _ = _ := by unfold Cell.x Cell.y; ring
  rw [h]
  omega

private theorem physical_direction (m : Parameter) (x y : ℤ) (i d : Fin 2)
    (hDirection : (cellOf m x y).e ≠ (cellOf m x y).v ∨ i = d) :
    (x + y) % 2 = 1 ∨ i = d := by
  rcases hDirection with h | h
  · left
    have hParity := cellOf_parity m x y
    have he := (cellOf m x y).e.isLt
    have hv := (cellOf m x y).v.isLt
    have hne : (cellOf m x y).e.val ≠ (cellOf m x y).v.val := by
      intro hEq
      exact h (Fin.ext hEq)
    omega
  · exact Or.inr h

/-- Every selected left or vertical edge strictly decreases the physical left rank. -/
theorem leftRank_incoming (m : Parameter) (x y : ℤ) (i : Fin 2)
    (hDirection : (cellOf m x y).e ≠ (cellOf m x y).v ∨ i = 0) :
    leftRank (incomingPoint x y i).1 (incomingPoint x y i).2 =
      leftRank x y - 1 := by
  have h := physical_direction m x y i 0 hDirection
  unfold incomingPoint leftRank
  fin_cases i <;> split_ifs <;> norm_num at * <;> omega

/-- Every selected right or vertical edge strictly decreases the physical right rank. -/
theorem rightRank_incoming (m : Parameter) (x y : ℤ) (i : Fin 2)
    (hDirection : (cellOf m x y).e ≠ (cellOf m x y).v ∨ i = 1) :
    rightRank (incomingPoint x y i).1 (incomingPoint x y i).2 =
      rightRank x y - 1 := by
  have h := physical_direction m x y i 1 hDirection
  unfold incomingPoint rightRank
  fin_cases i <;> split_ifs <;> norm_num at * <;> omega

/-- Only two representative edges lead to a prescribed site. -/
theorem incomingCell_prescribed_iff {m : Parameter} (c : Cell m) (i : Fin 2) :
    cellPrescribed (incomingCell c i) ↔
      (c.e = 1 ∧ c.v = 1 ∧ c.r = 0 ∧ c.s = 0 ∧ i = 0) ∨
      (c.e = 1 ∧ c.v = 1 ∧ c.r = m.val + 1 ∧ c.s = m.val - 2 ∧ i = 1) := by
  have hm := m.property
  rcases c with ⟨r, s, e, v, hr0, hrm, hs0, hsm, hMissing⟩
  fin_cases e <;> fin_cases v <;> fin_cases i <;> dsimp only at *
  · by_cases hs : 1 ≤ s
    · have h := incomingCell_00_left_of_pos
        (⟨r, s, 0, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hs
      simp [cellPrescribed, h]
    · by_cases hr : 1 ≤ r
      · have h := incomingCell_00_left_of_zero
          (⟨r, s, 0, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) hr
        simp [cellPrescribed, h]
      · have h := incomingCell_00_left_origin
          (⟨r, s, 0, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        simp [cellPrescribed, h]
  · have h := incomingCell_00_right
      (⟨r, s, 0, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl
    simp [cellPrescribed, h]
  · by_cases hr : r = m.val + 1
    · have h := incomingCell_01_down_top
        (⟨r, s, 0, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hr
      simp [cellPrescribed, h]
    · by_cases hEnd : r = m.val ∧ s = m.val - 1
      · have h := incomingCell_01_down_penultimate
          (⟨r, s, 0, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hEnd.1 hEnd.2
        simp [cellPrescribed, h]
      · have h := incomingCell_01_down_inner
          (⟨r, s, 0, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) hEnd
        simp [cellPrescribed, h]
  · have h := incomingCell_01_up
      (⟨r, s, 0, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl
    simp [cellPrescribed, h]
  · have h := incomingCell_10_down
      (⟨r, s, 1, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl
    simp [cellPrescribed, h]
  · by_cases hr : 1 ≤ r
    · have h := incomingCell_10_up_of_pos
        (⟨r, s, 1, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hr
      simp [cellPrescribed, h]
    · by_cases hs : s = 0
      · have h := incomingCell_10_up_origin
          (⟨r, s, 1, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) hs
        simp [cellPrescribed, h]
      · have h := incomingCell_10_up_row_zero
          (⟨r, s, 1, 0, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) (by dsimp only; omega)
        simp [cellPrescribed, h]
  · have h := incomingCell_11_left
      (⟨r, s, 1, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl
    simp [cellPrescribed, h]
  · by_cases hEnd : r = m.val + 1 ∧ s = m.val - 2
    · have h := incomingCell_11_right_top_endpoint
        (⟨r, s, 1, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hEnd.1 hEnd.2
      constructor
      · intro _
        exact Or.inr ⟨rfl, rfl, hEnd.1, hEnd.2, rfl⟩
      · intro _
        exact h
    · by_cases hs : s = m.val - 1
      · have h := incomingCell_11_right_last
          (⟨r, s, 1, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl hs
        simp [cellPrescribed, h]
        omega
      · have h := incomingCell_11_right_inner
          (⟨r, s, 1, 1, hr0, hrm, hs0, hsm, hMissing⟩ : Cell m) rfl rfl (by dsimp only; omega) hEnd
        simp [cellPrescribed, h]
        omega

/-- No actual incoming cell of the first region is prescribed. -/
theorem regionI_incoming_not_prescribed {m : Parameter} (c : Cell m)
    (hc : regionI c) (i : Fin 2) : ¬cellPrescribed (incomingCell c i) := by
  intro h
  rcases (incomingCell_prescribed_iff c i).mp h with h | h
  · rcases h with ⟨he, hv, hr, hs, _⟩
    simp [regionI, he, hv, hr, hs] at hc
  · rcases h with ⟨he, hv, hr, hs, _⟩
    have hm := m.property
    simp [regionI, he, hv, hr, hs] at hc
    omega

/-- The whole incoming collar of the physical first region avoids the source coset. -/
theorem regionI_physical_incoming_not_prescribed (m : Parameter) (x y : ℤ)
    (hc : regionI (cellOf m x y)) (i : Fin 2) :
    ¬cellPrescribed (cellOf m (incomingPoint x y i).1 (incomingPoint x y i).2) := by
  rw [cellOf_incomingPoint]
  exact regionI_incoming_not_prescribed (cellOf m x y) hc i

end FLattice.Auxiliary.PlusEvenProfile
