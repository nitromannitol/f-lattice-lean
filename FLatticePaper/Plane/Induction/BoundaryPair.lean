import FLatticePaper.Plane.Induction.BoundarySite
import FLatticePaper.Plane.Induction.ExteriorNbr
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.FreeCutExist
import FLatticePaper.Plane.Induction.CapRay
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.HPaidInputs
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.RowAt

/-! # The boundary of the closed polygon lies on the four arcs (site level)

A closed non-strict site `z` (a boundary site of `E`) lies on one of the four arcs: `freeH z`, `freeV z`, `freeV (z − K)` (with `K = (d, n)`),
or `freeH (z − V)` (with `V = (n − d, n + d)`). This is `BoundarySite.spectrum_site_even/odd` (grade level, in the child's coordinates),
transferred to `ChildFrame.freeH` / `freeV` by the grade identities and `mem_freeH_iff` / `mem_freeV_iff`. -/

namespace FLatticePaper.BoundaryPair

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem freeH_iff_freeHn (frame : ChildFrame) (z : Site) :
    frame.freeH z ↔ FLatticePaper.W1OffCollar.freeHn frame.child.num frame.child.den z := by
  have h := FreeCutSucc.mem_freeH_iff frame z
  rw [FreeCutExist.tGrade_eq_w1t] at h
  unfold ChildFrame.hSpectrum at h
  unfold FLatticePaper.W1OffCollar.freeHn FLatticePaper.W1OffCollar.hSp
  exact h

theorem freeV_iff_freeVn (frame : ChildFrame) (z : Site) :
    frame.freeV z ↔ FLatticePaper.W1OffCollar.freeVn frame.child.num frame.child.den z := by
  have h := FreeCutSucc.mem_freeV_iff frame z
  rw [FreeCutExist.sGrade_eq_w1s] at h
  unfold ChildFrame.vSpectrum at h
  unfold FLatticePaper.W1OffCollar.freeVn FLatticePaper.W1OffCollar.vSp
  exact h

/-- The period bound `2(d + n) < T` for a child with `n + 2 ≤ d`. -/
theorem period_bound (frame : ChildFrame) :
    2 * (frame.child.den + frame.child.num) < FLatticePaper.W1.w1T frame.child.num frame.child.den := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  unfold FLatticePaper.W1.w1T
  have h1 : 0 ≤ (frame.child.den - frame.child.num - 2) * (frame.child.den + frame.child.num) :=
    mul_nonneg (by omega) (by omega)
  have h2 : 0 < frame.child.den * frame.child.num := mul_pos (by omega) hn0
  nlinarith

/-- **The four arcs of a boundary site.** A closed site outside the open rectangle lies on one of the four arcs. -/
theorem boundary_arc (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) (hnot : ¬ frame.openRect z) :
    frame.freeH z ∨ frame.freeV z ∨ frame.freeV (z.1 - frame.child.den, z.2 - frame.child.num) ∨
      frame.freeH (z.1 - (frame.child.num - frame.child.den), z.2 - (frame.child.num + frame.child.den)) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨α, β, hα, hβ⟩ := CapRay.child_num_den_odd frame
  have hn : frame.child.num % 2 = 1 := by omega
  have hd : frame.child.den % 2 = 1 := by omega
  have hC : FLatticePaper.W1.closedRect frame.child.num frame.child.den z := by
    rw [FLatticePaper.W1.closedPolygon_eq_closedRect] at hz
    exact hz
  have hNS : ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z :=
    fun h => hnot ((FLatticePaper.W1Exit.openRect_iff frame z).mpr h)
  have hX := FLatticePaper.ExteriorNbr.exterior_nbr hn hd (by omega) z hNS
  have hTL := period_bound frame
  rcases Int.emod_two_eq_zero_or_one (FLatticePaper.W1.w1t frame.child.num frame.child.den z) with ht | ht
  · rcases FLatticePaper.BoundarySite.spectrum_site_even hn hd (by omega) (by omega) hTL z ht hC hX with
        h | h | h | h
    · exact Or.inl ((freeH_iff_freeHn frame z).mpr h)
    · exact Or.inr (Or.inl ((freeV_iff_freeVn frame z).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((freeV_iff_freeVn frame _).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((freeH_iff_freeHn frame _).mpr h)))
  · rcases FLatticePaper.BoundarySite.spectrum_site_odd hn hd (by omega) (by omega) hTL z ht hC hX with
        h | h | h | h
    · exact Or.inl ((freeH_iff_freeHn frame z).mpr h)
    · exact Or.inr (Or.inl ((freeV_iff_freeVn frame z).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((freeV_iff_freeVn frame _).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((freeH_iff_freeHn frame _).mpr h)))

/-- **Minus set.** With `P` at a free H site at most `c₀` and equal to `c₀` only at `H_0`, and `J = 0` on free H, the boundary sites of `E`
with `K = P + J ≥ c₀` (for `η = −1`) are `H_0` and the V iterates `vpath k` with `k ≤ r`. -/
theorem minus_boundary_K (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (z : Site) (hz : z ∈ frame.closedPolygon) (hnot : ¬ frame.openRect z)
    (hK : frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) :
    z = FLatticePaper.Induction.hFirst ∨
      ∃ k : ℕ, (k : ℤ) ≤ r ∧ (k : ℤ) < frame.child.den + frame.child.num ∧ z = VChain.vpath frame k := by
  rcases boundary_arc frame hz hnot with hH | hV | hVK | hHV
  · have hJz := hJH z hH
    have hPz := hPH z hH
    rw [hJz] at hK
    left
    exact hPz.2 (le_antisymm hPz.1 (by linarith))
  · obtain ⟨k, hk, hzk⟩ := VChain.freeV_eq_vpath_of_mem frame hV
    right
    refine ⟨k, ?_, hk, hzk⟩
    have hPz : frame.price F z = frame.cutPrice := PriceDeck.price_on_freeV frame F hP.strips hV
    have hJk := hpat k hk
    rw [← hzk] at hJk
    by_contra hcon
    rw [if_neg hcon] at hJk
    rw [hPz, hJk] at hK
    linarith
  · have hPz : frame.price F z = frame.price F (z.1 - frame.child.den, z.2 - frame.child.num) + (-1) := by
      have h1 := HPaidInputs.price_U frame F hP (z.1 - frame.child.den, z.2 - frame.child.num)
      have hvU : (z.1 - frame.child.den, z.2 - frame.child.num) + ((frame.child.den, frame.child.num) : Site) = z := by
        ext <;> simp
      rw [hvU] at h1
      linarith
    have hPv := PriceDeck.price_on_freeV frame F hP.strips hVK
    have hJz : frame.roundedSlip F (-1) z = frame.roundedSlip F (-1) (z.1 - frame.child.den, z.2 - frame.child.num) := by
      have h1 := HPaidInputs.roundedSlip_U frame F hP (-1) (z.1 - frame.child.den, z.2 - frame.child.num)
      have hvU : (z.1 - frame.child.den, z.2 - frame.child.num) + ((frame.child.den, frame.child.num) : Site) = z := by
        ext <;> simp
      rw [hvU] at h1
      exact h1
    obtain ⟨k', hk', hvk⟩ := VChain.freeV_eq_vpath_of_mem frame hVK
    have hJv := hpat k' hk'
    rw [← hvk] at hJv
    have hle : frame.roundedSlip F (-1) (z.1 - frame.child.den, z.2 - frame.child.num) ≤ 0 := by
      rw [hJv]
      split_ifs <;> norm_num
    exfalso
    rw [hPz, hJz] at hK
    linarith
  · have hhV : (z.1 - (frame.child.num - frame.child.den), z.2 - (frame.child.num + frame.child.den)) +
        ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site) = z := by
      ext <;> simp
    have hPh := hPH _ hHV
    have hPz : frame.price F z = frame.price F (z.1 - (frame.child.num - frame.child.den), z.2 - (frame.child.num + frame.child.den)) := by
      have h1 := HPaidInputs.price_V frame F hP (z.1 - (frame.child.num - frame.child.den), z.2 - (frame.child.num + frame.child.den))
      rw [hhV] at h1
      exact h1
    have hJz : frame.roundedSlip F (-1) z = -1 := by
      have h1 := HPaidInputs.roundedSlip_V frame F hP (-1) (z.1 - (frame.child.num - frame.child.den), z.2 - (frame.child.num + frame.child.den))
      rw [hhV, hJH _ hHV] at h1
      linarith
    exfalso
    rw [hPz, hJz] at hK
    linarith [hPh.1]

/-- **Plus set.** On the domain `E − V` (the site `z` with `w = z + V` on the boundary of `E`), with `η = +1`, `P` at a free H site at
most `c₀` and equal to `c₀` only at `H_0`, `J = 0` on free H, and the V pattern `J (vpath k) = 0` for `k ≤ L − r − 2`, `= 1` above: the
boundary sites of `E − V` with `K ≥ c₀` are `H_0` and the sites `vAt j` with `−r − 1 ≤ j ≤ −1`. -/
theorem plus_boundary_K (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F 1 h = 0)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (z : Site)
    (hw : (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) ∈
      frame.closedPolygon)
    (hnot : ¬ frame.openRect (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)))
    (hK : frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z) :
    z = FLatticePaper.Induction.hFirst ∨
      ∃ j : ℤ, -r - 1 ≤ j ∧ j ≤ -1 ∧ z = RowAt.vAt frame j := by
  obtain ⟨w, hwdef⟩ : ∃ w : Site,
      w = (z.1 + (frame.child.num - frame.child.den), z.2 + (frame.child.num + frame.child.den)) := ⟨_, rfl⟩
  have hzVw : w = z + ((frame.child.num - frame.child.den, frame.child.num + frame.child.den) : Site) := by
    rw [hwdef]
    ext <;> simp
  rw [← hwdef] at hw hnot
  have hPwz : frame.price F w = frame.price F z := by
    have h1 := HPaidInputs.price_V frame F hP z
    rw [← hzVw] at h1
    exact h1
  have hJwz : frame.roundedSlip F 1 w = frame.roundedSlip F 1 z + 1 := by
    have h1 := HPaidInputs.roundedSlip_V frame F hP 1 z
    rw [← hzVw] at h1
    exact h1
  rcases boundary_arc frame hw hnot with hH | hV | hVU | hHV
  · -- `w` on a free H arc: `P z = P w ≤ c₀` and `J z = −1`, so `K ≤ c₀ − 1`
    exfalso
    have hPw := hPH w hH
    have hJw := hJH w hH
    rw [hJwz] at hJw
    have hJz : frame.roundedSlip F 1 z = -1 := by linarith
    rw [hJz, ← hPwz] at hK
    linarith [hPw.1]
  · -- `w = vpath k` on the free V arc: `P z = c₀`, `J z = J (vpath k) − 1`
    obtain ⟨k, hk, hwk⟩ := VChain.freeV_eq_vpath_of_mem frame hV
    have hPw : frame.price F w = frame.cutPrice := PriceDeck.price_on_freeV frame F hP.strips hV
    have hJk := hpat k hk
    rw [← hwk] at hJk
    by_cases hkle : (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2
    · exfalso
      rw [if_pos hkle] at hJk
      have hJz : frame.roundedSlip F 1 z = -1 := by linarith
      rw [hJz, ← hPwz, hPw] at hK
      linarith
    · right
      refine ⟨(k : ℤ) - (frame.child.den + frame.child.num), by omega, by omega, ?_⟩
      have e1 := RowAt.vAt_add_len frame ((k : ℤ) - (frame.child.den + frame.child.num))
      rw [sub_add_cancel, RowAt.vAt_nat frame k hk] at e1
      have e2 : RowAt.vAt frame ((k : ℤ) - (frame.child.den + frame.child.num)) + RowAt.Vvec frame =
          z + RowAt.Vvec frame := by
        rw [← e1, ← hwk]
        exact hzVw
      exact (add_right_cancel e2).symm
  · -- `w − U` on the free V arc: `P z = c₀ − 1`, `J z = J v − 1 ≤ 0`, so `K ≤ c₀ − 1`
    exfalso
    have hvU : (w.1 - frame.child.den, w.2 - frame.child.num) + ((frame.child.den, frame.child.num) : Site) = w := by
      ext <;> simp
    have hPv := PriceDeck.price_on_freeV frame F hP.strips hVU
    have hPU := HPaidInputs.price_U frame F hP (w.1 - frame.child.den, w.2 - frame.child.num)
    rw [hvU, hPv] at hPU
    have hJU := HPaidInputs.roundedSlip_U frame F hP 1 (w.1 - frame.child.den, w.2 - frame.child.num)
    rw [hvU] at hJU
    obtain ⟨k', hk', hvk⟩ := VChain.freeV_eq_vpath_of_mem frame hVU
    have hJv := hpat k' hk'
    rw [← hvk] at hJv
    have hJvle : frame.roundedSlip F 1 (w.1 - frame.child.den, w.2 - frame.child.num) ≤ 1 := by
      rw [hJv]
      split_ifs <;> norm_num
    have hPz : frame.price F z = frame.cutPrice - 1 := by linarith
    have hJz : frame.roundedSlip F 1 z ≤ 0 := by linarith
    linarith
  · -- `w − V = z` on the free H arc: `K = P z ≥ c₀` forces `z = H_0`
    have hz' : (w.1 - (frame.child.num - frame.child.den), w.2 - (frame.child.num + frame.child.den)) = z := by
      rw [hzVw]
      ext <;> simp
    rw [hz'] at hHV
    have hPz := hPH z hHV
    have hJz := hJH z hHV
    rw [hJz] at hK
    left
    exact hPz.2 (le_antisymm hPz.1 (by linarith))

end FLatticePaper.BoundaryPair
