import FLatticePaper.Plane.Induction.HX2Diag
import FLatticePaper.Plane.Induction.FanPropagation
import FLatticePaper.Plane.Induction.RegionalCompat
import FLatticePaper.Plane.Induction.W1Constructor

/-! # The easy case of hderiv: the east middle forces its vertical input

For an even free V root `z` (not the origin) with the east middle `M1 = (z.1 + 1, z.2)` white and the diagonal `M2 = (z.1 + 1, z.2 - 1)`
white, the forced edge `M1 → M2` holds with an empty seed. The argument is section B's route in its simplest form:
* `M1` lies in the strict interior `W1.StrictInterior` (by the bounds of the root), so `W1Forced` gives a forced edge `M1 → o`;
* the region `S = {M1, M2}` with the chosen arrows `M1 → M2` and `M2 → y`, `y = (z.1, z.2 - 1)` the lower input, and ranks `2, 1, 0`
  satisfies the hypotheses of `RegionalCompat.regional_forced`, since `y` is not in the strict interior (its `s`-grade is at most `L - 2`);
  so `o = M2`.
The black-`M2` case is not covered here: for `η = -1` it occurs exactly when `t(z) < -L`, and then `u2 = (z.1 + 2, z.2 - 1)` lies in the strict
interior, so the region must grow. -/

namespace FLatticePaper.Induction

theorem hderiv_easy {G : Field} (frame : ChildFrame)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ vFirst)
    (hlapM1 : laplacian G (z.1 + 1, z.2) = 0) (hlapM2 : laplacian G (z.1 + 1, z.2 - 1) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) (z.1 + 1, z.2 - 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hodd1 : ¬ EvenSite (z.1 + 1, z.2) := by
    show ¬ ((z.1 + 1 + z.2) % 2 = 0)
    omega
  have hevM2 : EvenSite (z.1 + 1, z.2 - 1) := by
    show (z.1 + 1 + (z.2 - 1)) % 2 = 0
    omega
  have hodY : ¬ EvenSite (z.1, z.2 - 1) := by
    show ¬ ((z.1 + (z.2 - 1)) % 2 = 0)
    omega
  obtain ⟨hr1, hr2, hr3, hr4⟩ := frame.root_bounds hz hev
  have htlo := frame.t_le_neg_L hz hev hzF
  have hPgt := P_gt_L _ _ _ hn0 hdn hP
  -- the lower input lies in the V band, so it is not in the strict interior
  have hlow := frame.lower_in_vBand hz hev hzF (δ := 1) (Or.inl rfl) (Or.inl rfl)
  obtain ⟨-, hYrange⟩ := (frame.mem_vBand_iff _).mp hlow
  rw [if_neg hodY] at hYrange
  have hYnotR : ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z.1, z.2 - 1) := by
    intro h
    unfold FLatticePaper.W1.StrictInterior at h
    simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c,
      if_neg hodY] at h
    obtain ⟨-, -, h3, -⟩ := h
    have e : FLatticePaper.W1.w1s frame.child.num frame.child.den (z.1, z.2 - 1)
        = frame.sGrade (z.1, z.2 - 1) := rfl
    rw [e] at h3
    omega
  -- the east middle lies in the strict interior
  have htM : FLatticePaper.W1.w1t frame.child.num frame.child.den (z.1 + 1, z.2)
      = frame.tGrade z + frame.child.num := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    ring
  have hsM : FLatticePaper.W1.w1s frame.child.num frame.child.den (z.1 + 1, z.2)
      = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    ring
  have hT : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := hP.symm
  have hM1R : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z.1 + 1, z.2) := by
    unfold FLatticePaper.W1.StrictInterior
    simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c,
      if_neg hodd1, htM, hsM, hT]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  -- the three sites of the region and their chosen arrows
  have hne12 : (z.1 + 1, z.2 - 1) ≠ (z.1 + 1, z.2) := by
    intro h
    have h2 := congrArg Prod.snd h
    simp only at h2
    omega
  have hneY1 : (z.1, z.2 - 1) ≠ (z.1 + 1, z.2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hneY2 : (z.1, z.2 - 1) ≠ (z.1 + 1, z.2 - 1) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hr : ∀ x u : Site,
      ((x = (z.1 + 1, z.2) ∧ u = (z.1 + 1, z.2 - 1)) ∨ (x = (z.1 + 1, z.2 - 1) ∧ u = (z.1, z.2 - 1))) →
        (fun y : Site => if y = (z.1 + 1, z.2) then (2 : ℤ) else if y = (z.1 + 1, z.2 - 1) then 1 else 0) u <
          (fun y : Site => if y = (z.1 + 1, z.2) then (2 : ℤ) else if y = (z.1 + 1, z.2 - 1) then 1 else 0) x := by
    intro x u hC
    rcases hC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [hne12]
    · simp [hneY1, hneY2]
  have hS : ∀ x u : Site, (x = (z.1 + 1, z.2) ∨ x = (z.1 + 1, z.2 - 1)) →
      ((x = (z.1 + 1, z.2) ∧ u = (z.1 + 1, z.2 - 1)) ∨ (x = (z.1 + 1, z.2 - 1) ∧ u = (z.1, z.2 - 1))) →
        FLatticePaper.W1.StrictInterior frame.child.num frame.child.den u →
          (u = (z.1 + 1, z.2) ∨ u = (z.1 + 1, z.2 - 1)) := by
    intro x u _ hC hR
    rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inr rfl
    · exact absurd hR hYnotR
  have hblack : ∀ x : Site, (x = (z.1 + 1, z.2) ∨ x = (z.1 + 1, z.2 - 1)) → laplacian G x = -1 →
      ∀ u : Site, (u = incomingNeg x ∨ u = incomingPos x) →
        ((x = (z.1 + 1, z.2) ∧ u = (z.1 + 1, z.2 - 1)) ∨ (x = (z.1 + 1, z.2 - 1) ∧ u = (z.1, z.2 - 1))) := by
    intro x hx hl u _
    rcases hx with rfl | rfl
    · rw [hlapM1] at hl
      norm_num at hl
    · rw [hlapM2] at hl
      norm_num at hl
  have hwhite : ∀ x : Site, (x = (z.1 + 1, z.2) ∨ x = (z.1 + 1, z.2 - 1)) → laplacian G x = 0 →
      ∃ u : Site, ((x = (z.1 + 1, z.2) ∧ u = (z.1 + 1, z.2 - 1)) ∨ (x = (z.1 + 1, z.2 - 1) ∧ u = (z.1, z.2 - 1))) ∧
        (u = incomingNeg x ∨ u = incomingPos x) := by
    intro x hx _
    rcases hx with rfl | rfl
    · refine ⟨(z.1 + 1, z.2 - 1), Or.inl ⟨rfl, rfl⟩, Or.inl ?_⟩
      rw [FLatticePaper.FanPropagation.incomingNeg_of_odd _ hodd1]
    · refine ⟨(z.1, z.2 - 1), Or.inr ⟨rfl, rfl⟩, Or.inl ?_⟩
      rw [FLatticePaper.FanPropagation.incomingNeg_of_even _ hevM2]
      ext <;> simp
  -- the forced edge out of the east middle, and the regional identification of its output
  obtain ⟨o, hfo⟩ := hW1 (z.1 + 1, z.2) hM1R hlapM1
  have hreg := FLatticePaper.RegionalCompat.regional_forced (F := G)
    (R := FLatticePaper.W1.StrictInterior frame.child.num frame.child.den)
    (S := fun x : Site => x = (z.1 + 1, z.2) ∨ x = (z.1 + 1, z.2 - 1))
    (C := fun x u : Site => (x = (z.1 + 1, z.2) ∧ u = (z.1 + 1, z.2 - 1)) ∨ (x = (z.1 + 1, z.2 - 1) ∧ u = (z.1, z.2 - 1)))
    (r := fun y : Site => if y = (z.1 + 1, z.2) then (2 : ℤ) else if y = (z.1 + 1, z.2 - 1) then 1 else 0)
    hr hS hblack hwhite hfo (Or.inl rfl)
  have hoM2 : o = (z.1 + 1, z.2 - 1) := by
    rcases hreg with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h.symm hne12
  rw [hoM2] at hfo
  exact FLatticePaper.W1.forcedEdgeIn_forced hfo

end FLatticePaper.Induction
