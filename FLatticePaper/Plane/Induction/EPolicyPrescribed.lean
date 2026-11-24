import FLatticePaper.Plane.Induction.EPolicyFreeV
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.FreeTraceBox

/-!
# The prescribed directions of the signed policy on the reciprocal frame (task 118, W1 base)

`PrescribedAt (reciprocalFrame k) (reciprocalField k) η (ePolicy …)`: at a free H or V white centre the policy keeps the
prescribed input. The H trace is `freeH_box` (the row `y = 0`, `1 ≤ x ≤ d`); the V trace is `freeV_reciprocal`.
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey FLatticePaper.Induction

/-- At a native centre the selection of the representative is the selection of the centre. -/
theorem selDisp_nativeRep (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) {c : ℤ × ℤ}
    (hcN : NativeP (2 * (k : ℤ) + 3) c) :
    selDisp (2 * (k : ℤ) + 3) η (nativeRep (2 * (k : ℤ) + 3) c) = selDisp (2 * (k : ℤ) + 3) η c := by
  obtain ⟨hyN, i, j, hc⟩ := nativeRep_spec (stairEven_valid_reciprocal k) c
  rw [combine_mk_one (by omega)] at hc
  have h1 : c.1 = (nativeRep (2 * (k : ℤ) + 3) c).1 + i * (2 * (k : ℤ) + 3) + j * (1 - (2 * (k : ℤ) + 3)) := by
    have := congrArg Prod.fst hc
    simp only [Prod.fst_add] at this
    linarith
  have h2 : c.2 = (nativeRep (2 * (k : ℤ) + 3) c).2 + i + j * ((2 * (k : ℤ) + 3) + 1) := by
    have := congrArg Prod.snd hc
    simp only [Prod.snd_add] at this
    linarith
  exact selDisp_dup (by omega) (by omega) hη hyN hcN h1 h2

/-- The free H trace of the reciprocal frame is the row `y = 0`, with `1 ≤ x ≤ d`. -/
theorem prescribedH_policy (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : ℤ × ℤ)
    (hcH : c ∈ (reciprocalFrame k).freeH) (hw : laplacian (reciprocalField k) c = 0) (j : ℤ × ℤ) :
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c j ↔
      j = c + (reciprocalFrame k).prescribedH η c := by
  have hbox := FreeTraceBox.freeH_box (reciprocalFrame k) hcH
  rw [reciprocal_child_den, reciprocal_child_num] at hbox
  obtain ⟨x, y⟩ := c
  obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
  dsimp only at hx1 hxd hy0 hyn hw
  have hy : y = 0 := by omega
  subst hy
  have hcN : NativeP (2 * (k : ℤ) + 3) (x, 0) := by
    unfold NativeP
    left
    dsimp only
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [ePolicy_iff_sel k η hη (x, 0) j hw]
  unfold selF
  rw [selDisp_nativeRep k η hη hcN, prescribedH_reciprocal k η hη x hx1 hxd]

/-- On the free V trace of the reciprocal frame the explicit prescription is the selected displacement. -/
theorem prescribedV_policy (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) (c : ℤ × ℤ)
    (hcV : c ∈ (reciprocalFrame k).freeV) (hw : laplacian (reciprocalField k) c = 0) (j : ℤ × ℤ) :
    ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k)) c j ↔
      j = c + (reciprocalFrame k).prescribedV η c := by
  have hd3 : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  have hdodd : (2 * (k : ℤ) + 3) % 2 = 1 := by omega
  obtain ⟨x, y⟩ := c
  rw [ePolicy_iff_sel k η hη (x, y) j hw]
  unfold selF
  have hcF := freeV_reciprocal k hcV
  dsimp only at hcF
  have hpV : ∀ z : ℤ × ℤ, (reciprocalFrame k).prescribedV η z =
      if z = (0, 0) then (1, 0) else if z = (1 - (2 * (k : ℤ) + 3) + 1, 1 + (2 * (k : ℤ) + 3) - 1) then (η, 0)
        else if EvenSite z then (η, 0) else (0, -η) := by
    intro z
    unfold ChildFrame.prescribedV ChildFrame.vLast
    rw [reciprocal_child_num, reciprocal_child_den]
    rfl
  rcases hcF with h | h | h
  · obtain ⟨hx, hy⟩ := Prod.mk.inj h
    subst hx
    subst hy
    have hN : NativeP (2 * (k : ℤ) + 3) ((0 : ℤ), (0 : ℤ)) := Or.inr (Or.inl rfl)
    rw [selDisp_nativeRep k η hη hN]
    have hev : EvenSite ((0 : ℤ), (0 : ℤ)) := by
      unfold EvenSite
      norm_num
    have hS : SpecialE (2 * (k : ℤ) + 3) 0 0 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have hV : ¬ ((((0 : ℤ)) = 2 - (2 * (k : ℤ) + 3) ∧ (0 : ℤ) = 2 * (k : ℤ) + 3) ∨
        ((0 : ℤ) = 2 ∧ (0 : ℤ) = 2 * (k : ℤ) + 3 + 1)) := by
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
    have hsel : selDisp (2 * (k : ℤ) + 3) η ((0 : ℤ), (0 : ℤ)) = (1, 0) := by
      rw [selDisp_even_val hev, if_pos hS]
      split_ifs
      rfl
    rw [hsel, hpV]
    simp
  · obtain ⟨hs, hy1, hyd⟩ := h
    have hx : x = 1 - y := by omega
    subst hx
    have hN : NativeP (2 * (k : ℤ) + 3) (1 - y, y) := by
      unfold NativeP
      left
      dsimp only
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [selDisp_nativeRep k η hη hN]
    have hO : ¬ EvenSite (1 - y, y) := by
      unfold EvenSite
      dsimp only
      omega
    have hD : OddDown (2 * (k : ℤ) + 3) (1 - y) y := Or.inr (Or.inl ⟨by ring, hy1, by omega⟩)
    rw [selDisp_odd hO, if_pos hD, hpV]
    have hne0 : ((1 - y, y) : ℤ × ℤ) ≠ (0, 0) := fun e => by
      simp only [Prod.mk.injEq] at e
      omega
    have hneL : ((1 - y, y) : ℤ × ℤ) ≠ (1 - (2 * (k : ℤ) + 3) + 1, 1 + (2 * (k : ℤ) + 3) - 1) := fun e => by
      simp only [Prod.mk.injEq] at e
      omega
    have hc' : ¬ (1 - y = 1 - (2 * (k : ℤ) + 3) + 1 ∧ y = 2 * (k : ℤ) + 3) := by omega
    simp [hne0, hO, hc']
  · obtain ⟨hx, hy⟩ := Prod.mk.inj h
    subst hx
    subst hy
    have hN : NativeP (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) := by
      unfold NativeP
      left
      dsimp only
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [selDisp_nativeRep k η hη hN]
    have hev : EvenSite (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) := by
      unfold EvenSite
      dsimp only
      omega
    have hS : SpecialE (2 * (k : ℤ) + 3) (2 - (2 * (k : ℤ) + 3)) (2 * (k : ℤ) + 3) :=
      Or.inl ⟨rfl, rfl⟩
    have hsel : selDisp (2 * (k : ℤ) + 3) η (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) = (η, 0) := by
      rw [selDisp_even_val hev]
      simp [hS]
    rw [hsel, hpV]
    have hne0 : ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) : ℤ × ℤ) ≠ (0, 0) := fun e => by
      simp only [Prod.mk.injEq] at e
      omega
    have hL : ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3) : ℤ × ℤ) = (1 - (2 * (k : ℤ) + 3) + 1, 1 + (2 * (k : ℤ) + 3) - 1) := by
      ext <;> (simp; try ring)
    have hc' : ¬ (1 - (2 * (k : ℤ) + 3) + 1 = 0 ∧ (2 * (k : ℤ) + 3) = 0) := by omega
    simp [hL, hc']

/-- The prescribed directions of the signed policy `e(-1, eta)` on the reciprocal frame at `3^k`. -/
theorem prescribedAt_reciprocal (k : ℕ) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    PrescribedAt (reciprocalFrame k) (reciprocalField k) η
      (ePolicy (2 * (k : ℤ) + 3) η (laplacian (reciprocalField k))) :=
  ⟨fun c hcH hw j => prescribedH_policy k η hη c hcH hw j,
    fun c hcV hw j => prescribedV_policy k η hη c hcV hw j⟩

end FLatticePaper.EPolicy
