import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.FreeCutExist
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.FreeTraceBox

/-! # The H chain of the free trace

`hsucc z` is the successor of `z` on the free H trace: `z + (1,0)` if that is free, otherwise `z + (1,1)`. Starting at `hFirst`,
`hpath k` is the `k`-th iterate. Its `t`-grades satisfy `t ≡ (k+1) n (mod d)`, so the chain stays in `freeH` for `k + 1 < d`
(by coprimality of `n` and `d`), and it reaches `hLast` at `k = d − 1`; from `hLast` the step is `hFirst + U`. -/

namespace FLatticePaper.HChain

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

open Classical in
/-- The successor on the free H trace (the first candidate if it is free). -/
noncomputable def hsucc (frame : ChildFrame) (z : Site) : Site :=
  if (z.1 + 1, z.2) ∈ frame.freeH then (z.1 + 1, z.2) else (z.1 + 1, z.2 + 1)

/-- The successor of a free H site (off `hLast`) is free. -/
theorem hsucc_mem (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hne : z ≠ frame.hLast) :
    hsucc frame z ∈ frame.freeH := by
  unfold hsucc
  by_cases h : (z.1 + 1, z.2) ∈ frame.freeH
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact (FreeCutExist.freeH_succ_exists frame hz hne).resolve_left h

/-- The `t`-grade of the successor moves by `n` modulo `d`: `d ∣ t(hsucc z) − t(z) − n`. -/
theorem hsucc_tGrade (frame : ChildFrame) (z : Site) :
    frame.child.den ∣ frame.tGrade (hsucc frame z) - frame.tGrade z - frame.child.num := by
  unfold hsucc
  by_cases h : (z.1 + 1, z.2) ∈ frame.freeH
  · rw [if_pos h]
    refine ⟨0, ?_⟩
    rw [FreeCutPred.tGrade_eq_w1t, FreeCutPred.tGrade_eq_w1t, FreeCutPred.w1t_succX]; ring
  · rw [if_neg h]
    refine ⟨-1, ?_⟩
    rw [FreeCutPred.tGrade_eq_w1t, FreeCutPred.tGrade_eq_w1t, FreeCutExist.w1t_succXY]; ring

/-- The non-membership of `hLast + (1,0)`: its `t`-grade is `L`, even and above the H spectrum. -/
theorem hLast_succ_not_mem (frame : ChildFrame) :
    (frame.hLast.1 + 1, frame.hLast.2) ∉ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  intro h
  rw [FreeCutSucc.mem_freeH_iff] at h
  obtain ⟨-, -, hsp⟩ := h
  have ht : frame.tGrade (frame.hLast.1 + 1, frame.hLast.2) = frame.child.den + frame.child.num := by
    unfold ChildFrame.hLast ChildFrame.tGrade; ring
  rw [ht] at hsp
  unfold ChildFrame.hSpectrum at hsp
  omega

/-- The wrap: the successor of `hLast` is `hFirst + U = (d + 1, n)`. -/
theorem hsucc_hLast (frame : ChildFrame) :
    hsucc frame frame.hLast = (frame.child.den + 1, frame.child.num) := by
  unfold hsucc
  rw [if_neg (hLast_succ_not_mem frame)]
  unfold ChildFrame.hLast; ext <;> simp

/-- The chain from `hFirst`. -/
noncomputable def hpath (frame : ChildFrame) : ℕ → Site
  | 0 => FLatticePaper.Induction.hFirst
  | k + 1 => hsucc frame (hpath frame k)

theorem hpath_zero (frame : ChildFrame) : hpath frame 0 = FLatticePaper.Induction.hFirst := rfl

theorem hpath_succ (frame : ChildFrame) (k : ℕ) : hpath frame (k + 1) = hsucc frame (hpath frame k) := rfl

/-- The `t`-grade invariant and membership: for `k + 1 < d`, `hpath k` is a free H site with `t ≡ (k+1) n (mod d)`. -/
theorem hpath_free (frame : ChildFrame) : ∀ k : ℕ, (k : ℤ) + 1 < frame.child.den →
    hpath frame k ∈ frame.freeH ∧
      frame.child.den ∣ frame.tGrade (hpath frame k) - ((k : ℤ) + 1) * frame.child.num := by
  have hcop : IsCoprime frame.child.den frame.child.num := frame.child_reduced.symm
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨FLatticePaper.PsiMonoOffset.hFirst_mem_freeH frame, ?_⟩
    rw [hpath_zero]
    have ht : frame.tGrade FLatticePaper.Induction.hFirst = frame.child.num := by
      simp [ChildFrame.tGrade, FLatticePaper.Induction.hFirst]
    rw [ht]
    simp
  | succ k ih =>
    intro hk
    have hk' : (k : ℤ) + 1 < frame.child.den := by push_cast at hk; omega
    obtain ⟨hmem, hdiv⟩ := ih hk'
    have hne : hpath frame k ≠ frame.hLast := by
      intro heq
      have ht : frame.tGrade (hpath frame k) = frame.child.den := by
        rw [heq]
        dsimp only [ChildFrame.tGrade, ChildFrame.hLast]
        ring
      rw [ht] at hdiv
      have h1 : frame.child.den ∣ ((k : ℤ) + 1) * frame.child.num := by
        have := dvd_sub (dvd_refl frame.child.den) hdiv
        simpa using this
      have h2 : frame.child.den ∣ (k : ℤ) + 1 := hcop.dvd_of_dvd_mul_right h1
      have h3 : frame.child.den ≤ (k : ℤ) + 1 := Int.le_of_dvd (by omega) h2
      omega
    refine ⟨?_, ?_⟩
    · rw [hpath_succ]
      exact hsucc_mem frame hmem hne
    · rw [hpath_succ]
      have h1 := hsucc_tGrade frame (hpath frame k)
      have h2 := dvd_add h1 hdiv
      have e : frame.tGrade (hsucc frame (hpath frame k)) - (((k + 1 : ℕ) : ℤ) + 1) * frame.child.num =
          (frame.tGrade (hsucc frame (hpath frame k)) - frame.tGrade (hpath frame k) - frame.child.num) +
            (frame.tGrade (hpath frame k) - ((k : ℤ) + 1) * frame.child.num) := by
        push_cast; ring
      rw [e]
      exact h2

/-- Coverage by columns: a free H site in column `m + 1` is `hpath m`. The induction uses the free predecessor, the uniqueness of
the free successor, and the column box `1 ≤ z.1 ≤ d` of the free H trace. -/
theorem freeH_eq_hpath (frame : ChildFrame) : ∀ m : ℕ, ∀ z : Site, z ∈ frame.freeH → z.1 = (m : ℤ) + 1 →
    z = hpath frame m := by
  intro m
  induction m with
  | zero =>
    intro z hz hcol
    by_cases hne : z = FLatticePaper.Induction.hFirst
    · rw [hne, hpath_zero]
    · exfalso
      rcases FLatticePaper.FreeCutPred.freeH_pred_exists frame hz hne with h | h
      · have h1 := (FLatticePaper.Induction.FreeTraceBox.freeH_box frame h).1
        dsimp only at h1
        omega
      · have h1 := (FLatticePaper.Induction.FreeTraceBox.freeH_box frame h).1
        dsimp only at h1
        omega
  | succ m ih =>
    intro z hz hcol
    have hne : z ≠ FLatticePaper.Induction.hFirst := by
      intro h
      have h1 : z.1 = 1 := congrArg Prod.fst h
      omega
    rcases FLatticePaper.FreeCutPred.freeH_pred_exists frame hz hne with h | h
    · have hp := ih (z.1 - 1, z.2) h (by dsimp only; omega)
      rw [hpath_succ, ← hp]
      have e : ((z.1 - 1 + 1, z.2) : Site) = z := Prod.ext (by simp) rfl
      unfold hsucc
      rw [if_pos (by rw [e]; exact hz)]
      exact e.symm
    · have hp := ih (z.1 - 1, z.2 - 1) h (by dsimp only; omega)
      rw [hpath_succ, ← hp]
      have hnot : (((z.1 - 1, z.2 - 1) : Site).1 + 1, ((z.1 - 1, z.2 - 1) : Site).2) ∉ frame.freeH := by
        intro h'
        have key := FLatticePaper.FreeCutSucc.freeH_succ_unique frame h'
        apply key
        have e2 : ((((z.1 - 1, z.2 - 1) : Site).1 + 1, ((z.1 - 1, z.2 - 1) : Site).2 + 1) : Site) = z :=
          Prod.ext (by simp) (by simp)
        rw [e2]
        exact hz
      unfold hsucc
      rw [if_neg hnot]
      exact (Prod.ext (by simp) (by simp)).symm

/-- Every free H site is `hpath k` for a column index `k < d`. -/
theorem freeH_eq_hpath_of_mem (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    ∃ k : ℕ, (k : ℤ) < frame.child.den ∧ z = hpath frame k := by
  have hb := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz
  refine ⟨(z.1 - 1).toNat, by omega, freeH_eq_hpath frame _ z hz (by omega)⟩

end FLatticePaper.HChain
