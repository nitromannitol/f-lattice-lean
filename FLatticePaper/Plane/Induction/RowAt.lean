import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.FreeRows

/-! # The deck enumeration of the free classes and the (c₀,0)-representatives of the V cut

`hAt j = hpath (j mod d) + (j div d) U` and `vAt j = vpath (j mod L) + (j div L) V`, with `U = (d, n)`, `V = (n − d, n + d)`,
`L = d + n`. The H window `[1 − d, 0]` contains a representative of every free H class. On the V cut, with a cut `c` such that
`J(vpath k) = 0` for `k ≤ c` and `J(vpath k) = η` for `k > c`, the window `[c + 1 − L, c]` contains, for every V class, a
representative with `J = 0` (the window is the V part of the rows: `c = r` for `η = −1`, `c = L − r − 2` for `η = +1`). -/

namespace FLatticePaper.RowAt

open Farey FLatticePaper FLatticePaper.Induction

/-- The H deck vector `U = (d, n)`. -/
def Uvec (frame : ChildFrame) : Site := (frame.child.den, frame.child.num)

/-- The V deck vector `V = (n − d, n + d)`. -/
def Vvec (frame : ChildFrame) : Site := (frame.child.num - frame.child.den, frame.child.num + frame.child.den)

/-- The H enumeration with deck extension. -/
noncomputable def hAt (frame : ChildFrame) (j : ℤ) : Site :=
  HChain.hpath frame (j % frame.child.den).toNat + (j / frame.child.den) • Uvec frame

/-- The V enumeration with deck extension (period `L = d + n`). -/
noncomputable def vAt (frame : ChildFrame) (j : ℤ) : Site :=
  VChain.vpath frame (j % (frame.child.den + frame.child.num)).toNat +
    (j / (frame.child.den + frame.child.num)) • Vvec frame

theorem den_pos (frame : ChildFrame) : (0 : ℤ) < frame.child.den := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  omega

theorem len_pos (frame : ChildFrame) : (0 : ℤ) < frame.child.den + frame.child.num := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  omega

theorem hAt_add_den (frame : ChildFrame) (j : ℤ) :
    hAt frame (j + frame.child.den) = hAt frame j + Uvec frame := by
  have hd : frame.child.den ≠ 0 := ne_of_gt (den_pos frame)
  have hdiv : (j + frame.child.den) / frame.child.den = j / frame.child.den + 1 := by
    have h := Int.add_mul_ediv_right j 1 hd
    rwa [one_mul] at h
  have hmod : (j + frame.child.den) % frame.child.den = j % frame.child.den := by
    rw [Int.emod_def, Int.emod_def, hdiv]
    ring
  unfold hAt
  rw [hmod, hdiv, add_one_zsmul]
  abel

theorem vAt_add_len (frame : ChildFrame) (j : ℤ) :
    vAt frame (j + (frame.child.den + frame.child.num)) = vAt frame j + Vvec frame := by
  have hL : frame.child.den + frame.child.num ≠ 0 := ne_of_gt (len_pos frame)
  have hdiv : (j + (frame.child.den + frame.child.num)) / (frame.child.den + frame.child.num) =
      j / (frame.child.den + frame.child.num) + 1 := by
    have h := Int.add_mul_ediv_right j 1 hL
    rwa [one_mul] at h
  have hmod : (j + (frame.child.den + frame.child.num)) % (frame.child.den + frame.child.num) =
      j % (frame.child.den + frame.child.num) := by
    rw [Int.emod_def, Int.emod_def, hdiv]
    ring
  unfold vAt
  rw [hmod, hdiv, add_one_zsmul]
  abel

theorem hAt_zero (frame : ChildFrame) : hAt frame 0 = HChain.hpath frame 0 := by
  unfold hAt
  simp

theorem hAt_nat (frame : ChildFrame) (k : ℕ) (hk : (k : ℤ) < frame.child.den) :
    hAt frame k = HChain.hpath frame k := by
  unfold hAt
  rw [Int.emod_eq_of_lt (by positivity) hk, Int.ediv_eq_zero_of_lt (by positivity) hk]
  simp

theorem vAt_nat (frame : ChildFrame) (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num) :
    vAt frame k = VChain.vpath frame k := by
  unfold vAt
  rw [Int.emod_eq_of_lt (by positivity) hk, Int.ediv_eq_zero_of_lt (by positivity) hk]
  simp

/-- **H window.** Every free H site is `hAt j + m U` with `j ∈ [1 − d, 0]`. -/
theorem freeH_window (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    ∃ j : ℤ, 1 - frame.child.den ≤ j ∧ j ≤ 0 ∧ ∃ m : ℤ, z = hAt frame j + m • Uvec frame := by
  obtain ⟨k, hk, rfl⟩ := HChain.freeH_eq_hpath_of_mem frame hz
  by_cases h0 : k = 0
  · subst h0
    refine ⟨0, by have := den_pos frame; omega, le_refl _, 0, ?_⟩
    rw [hAt_zero, zero_zsmul, add_zero]
  · refine ⟨(k : ℤ) - frame.child.den, by omega, by omega, 1, ?_⟩
    have e := hAt_add_den frame ((k : ℤ) - frame.child.den)
    rw [sub_add_cancel] at e
    rw [one_zsmul, ← e, hAt_nat frame k hk]

/-- **V representative.** With the J pattern `J(vpath k) = if k ≤ c then 0 else η` and `P = c₀` on the free V cut, every V class
has a representative `vAt j` in the window `[c + 1 − L, c]` with `J = 0`, and `vpath k` is that representative up to `m V`. -/
theorem freeV_rep (frame : ChildFrame) (J P : Site → ℤ) (η c0 c : ℤ)
    (hJV : ∀ z, J (z + Vvec frame) = J z + η) (hPV : ∀ z, P (z + Vvec frame) = P z)
    (hc0 : 0 ≤ c) (hc1 : c ≤ frame.child.den + frame.child.num - 1)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      J (VChain.vpath frame k) = if (k : ℤ) ≤ c then 0 else η)
    (hPc : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → P (VChain.vpath frame k) = c0)
    (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num) :
    ∃ j : ℤ, c + 1 - (frame.child.den + frame.child.num) ≤ j ∧ j ≤ c ∧
      ∃ m : ℤ, VChain.vpath frame k = vAt frame j + m • Vvec frame ∧
        J (vAt frame j) = 0 ∧ P (vAt frame j) = c0 := by
  by_cases hkc : (k : ℤ) ≤ c
  · refine ⟨k, by omega, hkc, 0, ?_, ?_, ?_⟩
    · rw [vAt_nat frame k hk, zero_zsmul, add_zero]
    · rw [vAt_nat frame k hk, hpat k hk, if_pos hkc]
    · rw [vAt_nat frame k hk, hPc k hk]
  · have e := vAt_add_len frame ((k : ℤ) - (frame.child.den + frame.child.num))
    rw [sub_add_cancel, vAt_nat frame k hk] at e
    refine ⟨(k : ℤ) - (frame.child.den + frame.child.num), by omega, by omega, 1, ?_, ?_, ?_⟩
    · rw [one_zsmul, ← e]
    · have h1 := hJV (vAt frame ((k : ℤ) - (frame.child.den + frame.child.num)))
      rw [← e, hpat k hk, if_neg hkc] at h1
      linarith
    · have h2 := hPV (vAt frame ((k : ℤ) - (frame.child.den + frame.child.num)))
      rw [← e, hPc k hk] at h2
      exact h2.symm

/-! ## The labels of the rows contain the windows -/

theorem V_mem_minusRow (r L d j : ℤ) (hr : 0 ≤ r) (hrL : r ≤ L - 1)
    (hj1 : r + 1 - L ≤ j) (hj2 : j ≤ r) :
    FreeRows.FreeLabel.V j ∈ FreeRows.minusRow r L d := by
  unfold FreeRows.minusRow
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hmem : FreeRows.FreeLabel.V j ∈
        (List.range (L - r - 1).toNat).map (fun i : ℕ => FreeRows.FreeLabel.V (-1 - (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(-1 - j).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_right _ hmem
  · subst hzero
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · have hmem : FreeRows.FreeLabel.V j ∈
        (List.range r.toNat).map (fun i : ℕ => FreeRows.FreeLabel.V (r - (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(r - j).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))

theorem V_mem_plusRow (r L d j : ℤ) (hr : 0 ≤ r) (hr2 : r ≤ L - 2)
    (hj1 : -r - 1 ≤ j) (hj2 : j ≤ L - r - 2) :
    FreeRows.FreeLabel.V j ∈ FreeRows.plusRow r L d := by
  unfold FreeRows.plusRow
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hmem : FreeRows.FreeLabel.V j ∈
        (List.range (r + 1).toNat).map (fun i : ℕ => FreeRows.FreeLabel.V (-r - 1 + (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(j + r + 1).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hmem))
  · subst hzero
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · have hmem : FreeRows.FreeLabel.V j ∈
        (List.range (L - r - 2).toNat).map (fun i : ℕ => FreeRows.FreeLabel.V (1 + (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(j - 1).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_left _ (List.mem_append_right _ hmem)

theorem H_mem_minusRow (r L d j : ℤ) (hj1 : 1 - d ≤ j) (hj2 : j ≤ 0) :
    FreeRows.FreeLabel.H j ∈ FreeRows.minusRow r L d := by
  unfold FreeRows.minusRow
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hmem : FreeRows.FreeLabel.H j ∈
        (List.range (d - 1).toNat).map (fun i : ℕ => FreeRows.FreeLabel.H (-1 - (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(-1 - j).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_left _ (List.mem_append_right _ hmem)
  · subst hzero
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exfalso
    omega

theorem H_mem_plusRow (r L d j : ℤ) (hj1 : 1 - d ≤ j) (hj2 : j ≤ 0) :
    FreeRows.FreeLabel.H j ∈ FreeRows.plusRow r L d := by
  unfold FreeRows.plusRow
  rcases lt_trichotomy j 0 with hneg | hzero | hpos
  · have hmem : FreeRows.FreeLabel.H j ∈
        (List.range (d - 1).toNat).map (fun i : ℕ => FreeRows.FreeLabel.H (-1 - (i : ℤ))) := by
      refine List.mem_map.mpr ⟨(-1 - j).toNat, List.mem_range.mpr (by omega), ?_⟩
      congr 1
      omega
    exact List.mem_append_right _ hmem
  · subst hzero
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exfalso
    omega

/-! ## The cover theorems -/

/-- **H cover.** Every free H class is represented by a label of the minus row (and of the plus row) with the same H part. -/
theorem freeH_cover (frame : ChildFrame) (r : ℤ) {z : Site} (hz : z ∈ frame.freeH) :
    ∃ j : ℤ, FreeRows.FreeLabel.H j ∈ FreeRows.minusRow r (frame.child.den + frame.child.num) frame.child.den ∧
      FreeRows.FreeLabel.H j ∈ FreeRows.plusRow r (frame.child.den + frame.child.num) frame.child.den ∧
      ∃ m : ℤ, z = FreeRows.labelSite (vAt frame) (hAt frame) (FreeRows.FreeLabel.H j) + m • Uvec frame := by
  obtain ⟨j, hj1, hj2, m, hm⟩ := freeH_window frame hz
  exact ⟨j, H_mem_minusRow r _ _ j hj1 hj2, H_mem_plusRow r _ _ j hj1 hj2, m, hm⟩

/-- **V cover, minus row (`η = −1`, cut `c = r`).** Every free V class has a minus-row label whose site is its representative
with `J = 0` and `P = c₀`, up to `m V`. -/
theorem minus_cover_V (frame : ChildFrame) (J P : Site → ℤ) (r c0 : ℤ)
    (hJV : ∀ z, J (z + Vvec frame) = J z + (-1)) (hPV : ∀ z, P (z + Vvec frame) = P z)
    (hr0 : 0 ≤ r) (hrL : r ≤ frame.child.den + frame.child.num - 1)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      J (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (hPc : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → P (VChain.vpath frame k) = c0)
    (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num) :
    ∃ ℓ : FreeRows.FreeLabel, ℓ ∈ FreeRows.minusRow r (frame.child.den + frame.child.num) frame.child.den ∧
      ∃ m : ℤ, VChain.vpath frame k = FreeRows.labelSite (vAt frame) (hAt frame) ℓ + m • Vvec frame ∧
        J (FreeRows.labelSite (vAt frame) (hAt frame) ℓ) = 0 ∧
        P (FreeRows.labelSite (vAt frame) (hAt frame) ℓ) = c0 := by
  obtain ⟨j, hj1, hj2, m, hm, hJ, hP⟩ := freeV_rep frame J P (-1) c0 r hJV hPV hr0 hrL hpat hPc k hk
  exact ⟨FreeRows.FreeLabel.V j, V_mem_minusRow r _ _ j hr0 hrL hj1 hj2, m, hm, hJ, hP⟩

/-- **V cover, plus row (`η = +1`, cut `c = L − r − 2`).** -/
theorem plus_cover_V (frame : ChildFrame) (J P : Site → ℤ) (r c0 : ℤ)
    (hJV : ∀ z, J (z + Vvec frame) = J z + 1) (hPV : ∀ z, P (z + Vvec frame) = P z)
    (hr0 : 0 ≤ r) (hr2 : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      J (VChain.vpath frame k) = if (k : ℤ) ≤ (frame.child.den + frame.child.num) - r - 2 then 0 else 1)
    (hPc : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → P (VChain.vpath frame k) = c0)
    (k : ℕ) (hk : (k : ℤ) < frame.child.den + frame.child.num) :
    ∃ ℓ : FreeRows.FreeLabel, ℓ ∈ FreeRows.plusRow r (frame.child.den + frame.child.num) frame.child.den ∧
      ∃ m : ℤ, VChain.vpath frame k = FreeRows.labelSite (vAt frame) (hAt frame) ℓ + m • Vvec frame ∧
        J (FreeRows.labelSite (vAt frame) (hAt frame) ℓ) = 0 ∧
        P (FreeRows.labelSite (vAt frame) (hAt frame) ℓ) = c0 := by
  have hc1 : (frame.child.den + frame.child.num) - r - 2 ≤ frame.child.den + frame.child.num - 1 := by omega
  have hc0 : 0 ≤ (frame.child.den + frame.child.num) - r - 2 := by omega
  obtain ⟨j, hj1, hj2, m, hm, hJ, hP⟩ :=
    freeV_rep frame J P 1 c0 ((frame.child.den + frame.child.num) - r - 2) hJV hPV hc0 hc1 hpat hPc k hk
  exact ⟨FreeRows.FreeLabel.V j, V_mem_plusRow r _ _ j hr0 hr2 (by omega) (by omega), m, hm, hJ, hP⟩

end FLatticePaper.RowAt
