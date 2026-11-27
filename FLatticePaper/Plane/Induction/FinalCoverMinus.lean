import FLatticePaper.Plane.Induction.FreeCover
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.ListPrefix
import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.MinusRowWiring
import FLatticePaper.Plane.Induction.FreeEnum

/-! # Every free site of the minus row's classes is a row label up to the period lattice (the covering of `FinalAssembly`)

* the span of the deck is `{i U + j V}` (`U = Uvec`, `V = Vvec = transverse`);
* a free H site is `hAt j + i U` with `H j` a label of the minus row (`j = 0`, or `1 − d ≤ j ≤ −1`);
* a free V site is `vAt k + j V` with `V k` a label of the minus row (`k ∈ minusVIdx`, from `minus_row_covers`). -/

namespace FLatticePaper.FinalCoverMinus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeRows

/-- The span of the modified deck is the set of integer combinations of `U` and `V`. -/
theorem span_eq_UV (frame : ChildFrame) {t : Site} (ht : t ∈ frame.child.modifiedDeck.span) :
    ∃ i j : ℤ, t = i • RowAt.Uvec frame + j • RowAt.Vvec frame := by
  obtain ⟨i, j, rfl⟩ := ht
  refine ⟨i, j, ?_⟩
  unfold PeriodDeck.combine
  rw [frame.child_modifiedDeck_kernel, EndpointDeck.transverse_eq_Vdeck]
  unfold RowAt.Uvec RowAt.Vvec FLatticePaper.Induction.Vdeck
  ext <;> simp

/-- The H label `H j` is a label of the minus row, for `j = 0` and for `1 − d ≤ j ≤ −1`. -/
theorem H_mem_minusRow (r L d : ℤ) (j : ℤ) (hd : 1 ≤ d) (hj : j = 0 ∨ (1 - d ≤ j ∧ j ≤ -1)) :
    FreeLabel.H j ∈ minusRow r L d := by
  unfold minusRow
  rcases hj with rfl | ⟨h1, h2⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · refine List.mem_append_left _ (List.mem_append_right _ ?_)
    rw [List.mem_map]
    refine ⟨((-1 - j).toNat), ?_, ?_⟩
    · rw [List.mem_range]
      omega
    · congr 1
      omega

/-- The V label `V k` is a label of the minus row for `k ∈ minusVIdx r L`. -/
theorem V_mem_minusRow (r L d : ℤ) (k : ℤ) (hk : k ∈ FreeCover.minusVIdx r L) : FreeLabel.V k ∈ minusRow r L d := by
  unfold FreeCover.minusVIdx at hk
  unfold minusRow
  rcases List.mem_append.mp hk with h1 | h2
  · rcases List.mem_append.mp h1 with hA | hO
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i, hi, rfl⟩)))
    · have h0 : k = 0 := by simpa using hO
      subst h0
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
    exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)

/-- **The H covering.** A free H site is `hAt j + i U` for a label `H j` of the minus row. -/
theorem freeH_cover (frame : ChildFrame) {g : Site} (hg : g ∈ frame.freeH) :
    ∃ j : ℤ, (j = 0 ∨ (1 - frame.child.den ≤ j ∧ j ≤ -1)) ∧
      ∃ i : ℤ, g = RowAt.hAt frame j + i • RowAt.Uvec frame := by
  obtain ⟨k, hk, rfl⟩ := HChain.freeH_eq_hpath_of_mem frame hg
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · refine ⟨0, Or.inl rfl, 0, ?_⟩
    rw [RowAt.hAt_zero frame]
    simp
  · refine ⟨(k : ℤ) - frame.child.den, Or.inr ⟨by omega, by omega⟩, 1, ?_⟩
    rw [EasyHRank.hAt_sub_den frame hk, one_smul]
    abel

/-- **The V covering.** A free V site is `vAt k + j V` for a label `V k` of the minus row (from `minus_row_covers`). -/
theorem freeV_cover (frame : ChildFrame) (hcut : FreeEnum.CutOnePerOrdinate frame) {g : Site} (hg : g ∈ frame.freeV)
    (r : ℤ) (hr : 0 ≤ r) (hrL : r < FreeEnum.period frame) :
    ∃ k : ℤ, k ∈ FreeCover.minusVIdx r (FreeEnum.period frame) ∧ ∃ j : ℤ, g = RowAt.vAt frame k + j • RowAt.Vvec frame := by
  obtain ⟨m, hm, rfl⟩ := VChain.freeV_eq_vpath_of_mem frame hg
  have hord : 0 ≤ (VChain.vpath frame m).2 ∧ (VChain.vpath frame m).2 < FreeEnum.period frame := by
    rw [VChain.vpath_ord]
    unfold FreeEnum.period
    constructor <;> omega
  have hbase : ∀ r' : ℤ, 0 ≤ r' → r' < FreeEnum.period frame →
      (fun x : ℤ => VChain.vpath frame x.toNat) r' ∈ frame.freeV ∧ ((fun x : ℤ => VChain.vpath frame x.toNat) r').2 = r' := by
    intro r' h0 h1
    refine ⟨ListPrefix.vpath_freeV_all frame r'.toNat (by unfold FreeEnum.period at h1; omega), ?_⟩
    rw [VChain.vpath_ord]
    omega
  obtain ⟨k, hk, n, hn⟩ := FreeCover.minus_row_covers frame hcut (fun x : ℤ => VChain.vpath frame x.toNat) hbase
    hg hord r hr hrL
  refine ⟨k, hk, n, ?_⟩
  have hv : RowAt.vAt frame k = FreeEnum.vAt frame (fun x : ℤ => VChain.vpath frame x.toNat) k := by
    unfold RowAt.vAt FreeEnum.vAt FreeEnum.period
    ext <;> simp [RowAt.Vvec, FLatticePaper.Induction.Vdeck]
  rw [hv, hn]
  ext <;> simp [RowAt.Vvec, FLatticePaper.Induction.Vdeck]

end FLatticePaper.FinalCoverMinus
