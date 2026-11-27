import FLatticePaper.Plane.Induction.FreeCover
import FLatticePaper.Plane.Induction.FinalCoverMinus
import FLatticePaper.Plane.Induction.PlusRowWiring

/-! # The plus row covers the free classes (the covering of the plus fort argument)

`plusVIdx` is a complete residue system modulo the period `L` (one label per class), so every free V site is a plus row
label up to the deck vector `V`; every free H site is a plus row H label up to `U` (the H labels of the plus row are those of the
minus row). -/

namespace FLatticePaper.PlusCover

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows FLatticePaper.FreeCover FLatticePaper.FreeEnum

/-- The plus V indices are a complete residue system modulo `L`. -/
theorem plusVIdx_residue (r L j : ℤ) (hr : 0 ≤ r) (hrL : r + 2 ≤ L) :
    ∃ k : ℤ, k ∈ plusVIdx r L ∧ ∃ m : ℤ, j = k + m * L := by
  obtain ⟨k, hk1, hk2, m, hm⟩ := block_residue (-r - 1) L j (by omega)
  exact ⟨k, (plusVIdx_mem r L k hr hrL).2 ⟨by omega, by omega⟩, m, hm⟩

/-- **The plus V covering**: a free V site is a plus V label up to a multiple of `Vdeck` (`minus_row_covers` for `plusVIdx`). -/
theorem plus_row_covers (frame : ChildFrame) (hcut : CutOnePerOrdinate frame) (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < period frame → (base r) ∈ frame.freeV ∧ (base r).2 = r)
    {z : Site} (hz : z ∈ frame.freeV) (hord : 0 ≤ z.2 ∧ z.2 < period frame)
    (r : ℤ) (hr : 0 ≤ r) (hrL : r + 2 ≤ period frame) :
    ∃ k : ℤ, k ∈ plusVIdx r (period frame) ∧ ∃ m : ℤ,
      vAt frame base k = (z.1 + (-m) * (Vdeck frame).1, z.2 + (-m) * (Vdeck frame).2) := by
  obtain ⟨k, hk, m, hm⟩ := plusVIdx_residue r (period frame) z.2 hr hrL
  refine ⟨k, hk, m, ?_⟩
  have hz' : z = base z.2 := freeV_eq_base frame hcut base hbase hz hord
  have hk' : k = z.2 + (-m) * period frame := by linarith
  have hvk : vAt frame base k = vAt frame base (z.2 + (-m) * period frame) := by rw [hk']
  rw [hvk, vAt_add_mul_period, vAt_eq_base frame base z.2 hord]
  rw [← hz']

/-- The plus H labels are those of the minus row: `H 0` and `H (-1-i)`, `i < d − 1`. -/
theorem H_mem_plusRow (r L d : ℤ) (j : ℤ) (hd : 1 ≤ d) (hj : j = 0 ∨ (1 - d ≤ j ∧ j ≤ -1)) :
    FreeLabel.H j ∈ plusRow r L d := by
  unfold plusRow
  rcases hj with rfl | ⟨h1, h2⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · refine List.mem_append_right _ ?_
    rw [List.mem_map]
    refine ⟨((-1 - j).toNat), ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · congr 1
      omega

/-- The plus V labels: `V k` for `k ∈ plusVIdx r L`. -/
theorem V_mem_plusRow (r L d : ℤ) (k : ℤ) (hk : k ∈ plusVIdx r L) : FreeLabel.V k ∈ plusRow r L d := by
  unfold plusVIdx at hk
  unfold plusRow
  rcases List.mem_append.mp hk with h1 | h2
  · rcases List.mem_append.mp h1 with hA | hO
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i, hi, rfl⟩)))
    · have h0 : k = 0 := by simpa using hO
      subst h0
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩))

end FLatticePaper.PlusCover
