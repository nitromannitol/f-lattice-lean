import FLatticePaper.Plane.Induction.VGap
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.RoutePlus
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.RouteRegion
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.InternalReturns

/-! # The v2 arrows: the strict translates of the even sources (sign `η = 1` first)

For an odd free V root `z` with a free diagonal `(z.1 - 1, z.2 + 1)` (the `η = 1` case of the `v2` hypothesis), the even site
`(z.1, z.2 + 1)` is strictly interior. The grades: `t(z) ≤ d` (closed), `s(z) ≤ d + n - 2` (V spectrum), `t(z) ≥ 2n + d - T`
and `s(z) ≥ 3n + 2 - d` (the diagonal is closed), and `t(z) + T ≥ 2d + n - 1` by `VGap.no_gap`. -/

namespace FLatticePaper.V2Arrows

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem plus_source_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    StrictInterior frame.child.num frame.child.den (z.1, z.2 + 1) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  -- z: its closed rectangle (odd branch), and the V spectrum of s(z)
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz
  obtain ⟨hzcl, -, hzvs⟩ := hz
  have hzcl' := (frame.mem_closedPolygon_iff z).mp hzcl
  obtain ⟨-, hzt1, hzt2, hzs1, hzs2⟩ : ¬ EvenSite z ∧ _ := by
    rcases hzcl' with h | h
    · exact absurd h.1 hodd
    · exact ⟨h.1, h.2⟩
  unfold ChildFrame.vSpectrum at hzvs
  obtain ⟨-, hzvs⟩ := hzvs
  -- the diagonal: free, so closed (its parity is odd)
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hdiag
  obtain ⟨hdcl, -, -⟩ := hdiag
  have hdodd : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    omega
  have hdcl' := (frame.mem_closedPolygon_iff (z.1 - 1, z.2 + 1)).mp hdcl
  obtain ⟨-, hdt1, -, hds1, -⟩ : ¬ EvenSite (z.1 - 1, z.2 + 1) ∧ _ := by
    rcases hdcl' with h | h
    · exact absurd h.1 hdodd
    · exact ⟨h.1, h.2⟩
  have hs_le : frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hzvs with h | h
    · linarith [h.2]
    · linarith [h.2]
  have hTbig : 2 * frame.child.den - 2 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega)]
  -- the grades of z from the closed diagonal
  have hdt1' : frame.child.num - frame.child.periodDenominator
      ≤ frame.child.num * (z.1 - 1) - frame.child.den * (z.2 + 1) := hdt1
  have hds1' : 2 - frame.child.den + frame.child.num
      ≤ (frame.child.den + frame.child.num) * (z.1 - 1) + (frame.child.den - frame.child.num) * (z.2 + 1) := hds1
  have ht1 : 2 * frame.child.num + frame.child.den ≤ frame.tGrade z + frame.child.periodDenominator := by
    unfold ChildFrame.tGrade
    rw [hTd] at hdt1' ⊢
    linarith
  have hs1 : 3 * frame.child.num + 2 - frame.child.den ≤ frame.sGrade z := by
    unfold ChildFrame.sGrade
    linarith
  -- the gap: t(z) + T ≥ 2d + n - 1
  have ht2 : frame.tGrade z + frame.child.periodDenominator ≤ 2 * frame.child.den + frame.child.num - 2 →
      False := fun h => VGap.no_gap frame z ht1 h hs1 hs_le
  have hgap : 2 * frame.child.den + frame.child.num - 1 ≤ frame.tGrade z + frame.child.periodDenominator := by
    by_contra hlt
    exact ht2 (by omega)
  have hevu : EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite
    unfold EvenSite at hodd
    omega
  -- the strict conditions of the even source (z.1, z.2 + 1)
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, w1t, w1s, w1T, if_pos hevu]
  unfold ChildFrame.tGrade at hgap hzt2
  unfold ChildFrame.sGrade at hs1 hs_le
  rw [hTd] at hgap hTbig
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hTbig, hgap, hs1, hs_le]

/-- The grade facts of an odd free V root with a free diagonal (for `η = 1`). -/
theorem freeV_odd_facts (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    frame.tGrade z ≤ frame.child.den ∧ frame.sGrade z ≤ frame.child.den + frame.child.num - 2 ∧
      2 * frame.child.num + frame.child.den ≤ frame.tGrade z + frame.child.periodDenominator ∧
      3 * frame.child.num + 2 - frame.child.den ≤ frame.sGrade z := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz
  obtain ⟨hzcl, -, hzvs⟩ := hz
  have hzcl' := (frame.mem_closedPolygon_iff z).mp hzcl
  obtain ⟨-, hzt1, hzt2, hzs1, hzs2⟩ : ¬ EvenSite z ∧ _ := by
    rcases hzcl' with h | h
    · exact absurd h.1 hodd
    · exact ⟨h.1, h.2⟩
  unfold ChildFrame.vSpectrum at hzvs
  obtain ⟨-, hzvs⟩ := hzvs
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hdiag
  obtain ⟨hdcl, -, -⟩ := hdiag
  have hdodd : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hodd ⊢
    omega
  have hdcl' := (frame.mem_closedPolygon_iff (z.1 - 1, z.2 + 1)).mp hdcl
  obtain ⟨-, hdt1, -, hds1, -⟩ : ¬ EvenSite (z.1 - 1, z.2 + 1) ∧ _ := by
    rcases hdcl' with h | h
    · exact absurd h.1 hdodd
    · exact ⟨h.1, h.2⟩
  have hs_le : frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hzvs with h | h
    · linarith [h.2]
    · linarith [h.2]
  have hdt1' : frame.child.num - frame.child.periodDenominator
      ≤ frame.child.num * (z.1 - 1) - frame.child.den * (z.2 + 1) := hdt1
  have hds1' : 2 - frame.child.den + frame.child.num
      ≤ (frame.child.den + frame.child.num) * (z.1 - 1) + (frame.child.den - frame.child.num) * (z.2 + 1) := hds1
  refine ⟨hzt2, hs_le, ?_, ?_⟩
  · unfold ChildFrame.tGrade
    linarith
  · unfold ChildFrame.sGrade
    linarith

/-- The H-side translate of the even `a2` source: `(z.1 - 1, z.2) + (d, n)` is strictly interior (for `η = 1`). -/
theorem plus_next_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) := by
  obtain ⟨hzt2, hs_le, ht1, hs1⟩ := freeV_odd_facts frame hz hodd hdiag
  have htn := VGap.t_le_n_plus_one frame z hzt2 hs1 hs_le
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hTbig : 2 * frame.child.den - 2 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega)]
  have hevw : EvenSite ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) := by
    simp only [EvenSite, Prod.fst_add, Prod.snd_add] at hodd ⊢
    omega
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, w1t, w1s, w1T, if_pos hevw, Prod.fst_add, Prod.snd_add]
  unfold ChildFrame.tGrade at ht1 htn
  unfold ChildFrame.sGrade at hs1 hs_le
  rw [hTd] at ht1 hTbig
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hTbig, ht1, htn, hs1, hs_le]

/-- A free V root is not strictly interior. -/
theorem not_strict_of_freeV {frame : ChildFrame} {v : Site} (hv : v ∈ frame.freeV) :
    ¬ StrictInterior frame.child.num frame.child.den v := by
  intro hS
  have hnf := strictInterior_nonfree frame hS
  exact hnf 0 (FLatticePaper.RouteStay.zero_mem_span frame) (Set.mem_union_right _ (by simpa using hv))



/-- The `η = 1` first arrow of `v2`: the even source `(z.1, z.2 + 1)` is strictly interior (translate zero), with the free diagonal
as its port. -/
theorem v2_a0_plus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    laplacian G (z.1, z.2 + 1) = -1 ∨ C.policy (z.1, z.2 + 1) (z.1 - 1, z.2 + 1) := by
  by_cases hb : laplacian G (z.1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hevu : EvenSite (z.1, z.2 + 1) := by
      unfold EvenSite
      unfold EvenSite at hodd
      omega
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + 0) (u + 0) := fun x u => by simp
    have hs : EvenSite (0 : Site) := by
      unfold EvenSite
      norm_num
    have hin : (z.1 - 1, z.2 + 1) = incomingNeg (z.1, z.2 + 1) ∨ (z.1 - 1, z.2 + 1) = incomingPos (z.1, z.2 + 1) :=
      Or.inl (by unfold incomingNeg; rw [if_pos hevu])
    have hqS : StrictInterior frame.child.num frame.child.den ((z.1, z.2 + 1) + 0) := by
      simpa using plus_source_strict frame hz hodd hdiag
    have hport : ¬ StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2 + 1) + 0) := by
      simpa using not_strict_of_freeV (frame := frame) hdiag
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hs hT (by simpa using hw) hqS hin hport

/-- The `η = 1` third arrow of `v2`: the even source `(z.1 - 1, z.2)` keeps `z` through the translate by `(d, n)`, with `z` a
free port. -/
theorem v2_a2_plus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) z := by
  by_cases hb : laplacian G (z.1 - 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2) = 0 := (hbin _).resolve_left hb
    have heven : EvenSite (z.1 - 1, z.2) := by
      unfold EvenSite
      unfold EvenSite at hodd
      omega
    have hK : frame.child.modifiedDeck.combine 1 0 = (frame.child.den, frame.child.num) :=
      ChainWire.combine_one_zero_eq_Kdeck frame
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + (frame.child.den, frame.child.num)) (u + (frame.child.den, frame.child.num)) := by
      intro x u
      have h := hdeck 1 0 x u
      rw [hK] at h
      exact h
    have hsK : EvenSite (frame.child.den, frame.child.num) := by
      unfold EvenSite
      have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
      omega
    have hqw : laplacian G ((z.1 - 1, z.2) + (frame.child.den, frame.child.num)) = 0 := by
      rw [StripColours.lap_add_kernel frame hP.periods]
      exact hw
    have hqS := plus_next_strict frame hz hodd hdiag
    have hin : z = incomingPos (z.1 - 1, z.2) := by
      unfold incomingPos
      rw [if_pos heven]
      ext <;> simp
    have hport : ¬ StrictInterior frame.child.num frame.child.den (z + (frame.child.den, frame.child.num)) := by
      intro hS
      have hnf := strictInterior_nonfree frame hS
      have hz' := FLatticePaper.ForcedArrows.nonfree_of_add_span (frame := frame) (FLatticePaper.Induction.Kdeck_mem_span frame) hnf
      exact hz' 0 (FLatticePaper.RouteStay.zero_mem_span frame) (Set.mem_union_right _ (by simpa using hz))
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hsK hT hqw hqS (Or.inr hin) hport

/-- The `η = 1` middle arrow of `v2`: the free odd diagonal keeps `(z.1 - 1, z.2)`, its prescribed input `(0, -1)`. -/
theorem v2_a1_plus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = 1)
    {z : Site} (hodd : ¬ EvenSite z) (hdiag : (z.1 - 1, z.2 + 1) ∈ frame.freeV) :
    laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ C.policy (z.1 - 1, z.2 + 1) (z.1 - 1, z.2) := by
  by_cases hb : laplacian G (z.1 - 1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hodd1 : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
      unfold EvenSite at hodd ⊢
      omega
    refine (C.prescribed.2 _ hdiag hw _).mpr ?_
    rw [FLatticePaper.InternalReturns.prescribedV_odd frame η hodd1, hη]
    ext <;> simp

/-- **The v2 row for `η = 1`.** For an odd free V root `z` with the free diagonal of the `v2` hypothesis, the three arrows of the
route are black or kept by the canonical policy, in the exact form of the `v2` field of `RouteGenuine`. -/
theorem v2_row_plus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = 1)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 + -η, z.2 - -η) ∈ frame.freeV) :
    (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 + -η, z.2 - -η)) ∧
    (laplacian G (z.1 + -η, z.2 - -η) = -1 ∨ C.policy (z.1 + -η, z.2 - -η) (z.1 + -η, z.2)) ∧
    (laplacian G (z.1 + -η, z.2) = -1 ∨ C.policy (z.1 + -η, z.2) z) := by
  subst hη
  have e1 : (z.1 + -1, z.2 - -1) = (z.1 - 1, z.2 + 1) := Prod.ext (by ring) (by ring)
  have e0 : (z.1, z.2 - -1) = (z.1, z.2 + 1) := Prod.ext rfl (by ring)
  have e2 : (z.1 + -1, z.2) = (z.1 - 1, z.2) := Prod.ext (by ring) rfl
  rw [e1] at hdiag
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e1]
    exact v2_a0_plus C hW1 hbin hz hodd hdiag
  · rw [e1, e2]
    exact v2_a1_plus C hbin rfl hodd hdiag
  · rw [e2]
    exact v2_a2_plus C hW1 hP hdeck hbin hz hodd hdiag


end FLatticePaper.V2Arrows
