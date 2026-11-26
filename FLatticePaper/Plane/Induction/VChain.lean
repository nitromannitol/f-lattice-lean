import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.FreeVCutExist
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.W4Exceptional

/-! # The V chain of the free V cut

`vsucc z` is the successor of `z` on the free V cut: `(z.1, z.2+1)` if that is free, otherwise `(z.1 − 1, z.2+1)`. Starting at
`vFirst`, `vpath k` is the `k`-th iterate; its ordinate is `k`. The ordinate box `0 ≤ z.2 ≤ L − 1` on the free V cut
(even sites: `freeV_even_ordinate`; odd sites: `freeV_odd_box`) makes the iterates cover the cut, with `vLast = vpath (L − 1)`. -/

namespace FLatticePaper.VChain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

open Classical in
/-- The successor on the free V cut (the first free candidate). -/
noncomputable def vsucc (frame : ChildFrame) (z : Site) : Site :=
  if (z.1, z.2 + 1) ∈ frame.freeV then (z.1, z.2 + 1) else (z.1 - 1, z.2 + 1)

theorem vsucc_mem (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hne : z ≠ frame.vLast) :
    vsucc frame z ∈ frame.freeV := by
  unfold vsucc
  by_cases h : (z.1, z.2 + 1) ∈ frame.freeV
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    exact (FLatticePaper.FreeVCutExist.freeV_succ_exists frame hz hne).resolve_left h

theorem vsucc_ord (frame : ChildFrame) (z : Site) : (vsucc frame z).2 = z.2 + 1 := by
  unfold vsucc
  split_ifs <;> simp

/-- The chain from `vFirst`. -/
noncomputable def vpath (frame : ChildFrame) : ℕ → Site
  | 0 => FLatticePaper.Induction.vFirst
  | k + 1 => vsucc frame (vpath frame k)

theorem vpath_zero (frame : ChildFrame) : vpath frame 0 = FLatticePaper.Induction.vFirst := rfl

theorem vpath_succ (frame : ChildFrame) (k : ℕ) : vpath frame (k + 1) = vsucc frame (vpath frame k) := rfl

/-- The ordinate of the `k`-th iterate is `k`. -/
theorem vpath_ord (frame : ChildFrame) : ∀ k : ℕ, (vpath frame k).2 = (k : ℤ) := by
  intro k
  induction k with
  | zero => simp [vpath_zero, FLatticePaper.Induction.vFirst]
  | succ k ih => rw [vpath_succ, vsucc_ord, ih]; push_cast; ring

/-- The iterates stay in the free V cut up to the last ordinate `L − 1`. -/
theorem vpath_free (frame : ChildFrame) : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num - 1 →
    vpath frame k ∈ frame.freeV := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [vpath_zero]
    exact FLatticePaper.W4Exceptional.vFirst_mem_freeV frame
  | succ k ih =>
    intro hk
    have hk' : (k : ℤ) < frame.child.den + frame.child.num - 1 := by push_cast at hk; omega
    have hmem := ih hk'
    have hv : frame.vLast.2 = frame.child.num + frame.child.den - 1 := rfl
    have hne : vpath frame k ≠ frame.vLast := by
      intro heq
      have h1 := vpath_ord frame k
      rw [heq] at h1
      omega
    rw [vpath_succ]
    exact vsucc_mem frame hmem hne

/-- The ordinate box of the free V cut: `0 ≤ z.2 ≤ L − 1`. -/
theorem freeV_ordinate_box (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    0 ≤ z.2 ∧ z.2 ≤ frame.child.den + frame.child.num - 1 := by
  by_cases he : EvenSite z
  · have h := FLatticePaper.FreeVOrdinate.freeV_even_ordinate frame hz he
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨-, -, h1, h2⟩ := FLatticePaper.Induction.RouteSteps.freeV_odd_box frame hz he
    exact ⟨by omega, by omega⟩

/-- Coverage by ordinates: a free V site of ordinate `m` is `vpath m`. -/
theorem freeV_eq_vpath (frame : ChildFrame) : ∀ m : ℕ, ∀ z : Site, z ∈ frame.freeV → z.2 = (m : ℤ) →
    z = vpath frame m := by
  intro m
  induction m with
  | zero =>
    intro z hz hcol
    by_cases hne : z = FLatticePaper.Induction.vFirst
    · rw [hne, vpath_zero]
    · exfalso
      rcases FLatticePaper.FreeCutPred.freeV_pred_exists frame hz hne with h | h
      · have h1 := (freeV_ordinate_box frame h).1
        dsimp only at h1
        omega
      · have h1 := (freeV_ordinate_box frame h).1
        dsimp only at h1
        omega
  | succ m ih =>
    intro z hz hcol
    have hne : z ≠ FLatticePaper.Induction.vFirst := by
      intro h
      have h1 : z.2 = 0 := congrArg Prod.snd h
      omega
    rcases FLatticePaper.FreeCutPred.freeV_pred_exists frame hz hne with h | h
    · have hp := ih (z.1, z.2 - 1) h (by dsimp only; omega)
      rw [vpath_succ, ← hp]
      have e : ((z.1, z.2 - 1 + 1) : Site) = z := Prod.ext rfl (by simp)
      unfold vsucc
      rw [if_pos (by rw [e]; exact hz)]
      exact e.symm
    · have hp := ih (z.1 + 1, z.2 - 1) h (by dsimp only; omega)
      rw [vpath_succ, ← hp]
      have hnot : (((z.1 + 1, z.2 - 1) : Site).1, ((z.1 + 1, z.2 - 1) : Site).2 + 1) ∉ frame.freeV := by
        intro h'
        have key := FLatticePaper.FreeCutSucc.freeV_succ_unique frame h'
        apply key
        have e2 : ((((z.1 + 1, z.2 - 1) : Site).1 - 1, ((z.1 + 1, z.2 - 1) : Site).2 + 1) : Site) = z :=
          Prod.ext (by simp) (by simp)
        rw [e2]
        exact hz
      unfold vsucc
      rw [if_neg hnot]
      exact (Prod.ext (by simp) (by simp)).symm

/-- Every free V site is `vpath k` for an ordinate index `k < L`. -/
theorem freeV_eq_vpath_of_mem (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    ∃ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num ∧ z = vpath frame k := by
  have hb := freeV_ordinate_box frame hz
  exact ⟨z.2.toNat, by omega, freeV_eq_vpath frame _ z hz (by omega)⟩

/-- The last V site is the iterate of ordinate `L − 1`. -/
theorem vLast_eq_vpath (frame : ChildFrame) :
    frame.vLast = vpath frame (frame.child.num + frame.child.den - 1).toNat := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hv : frame.vLast.2 = frame.child.num + frame.child.den - 1 := rfl
  exact freeV_eq_vpath frame _ _ (FLatticePaper.FreeVOrdinate.vLast_mem_freeV frame) (by omega)

end FLatticePaper.VChain
