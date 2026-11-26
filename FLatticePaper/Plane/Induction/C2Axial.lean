import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.TpFrame
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.RouteRegion
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.RoutePlus
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.InternalReturns

/-! # The west neighbour of an even free H root with a free diagonal predecessor is strictly interior

For an even free H root `z` whose diagonal predecessor `(z.1 - 1, z.2 - 1)` is free, the axial predecessor `u = (z.1 - 1, z.2)` lies in
the strict interior. The four inequalities come from:
* `t(z) ≥ 2` (the even H spectrum) and `t(z) ≤ 2n - 2` (the diagonal's upper spectrum bound, since `t(diag) = t(z) - n + d`);
* `s(z) ≥ 2(d + n)`: the box `1 ≤ z.1 ≤ d`, `0 ≤ z.2 ≤ n - 1` with `z.1 ≠ 1` (parity and `t(z) ≥ 2`), so `z.1 ≥ 2` and `z.2 ≥ 0`;
* `s(z) < T + 2 - 2d` (`RouteSteps.freeH_even_s_lt`).
Hence `u` is strictly interior, and `strictInterior_nonfree` gives that `u` is nonfree. -/

namespace FLatticePaper.C2Axial

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem west_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hdiag : (z.1 - 1, z.2 - 1) ∈ frame.freeH) :
    StrictInterior frame.child.num frame.child.den (z.1 - 1, z.2) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FreeTraceBox.freeH_box frame hz
  obtain ⟨⟨ht2, -⟩, -⟩ := TpFrame.freeH_even_tu frame hz hev
  have hdiagEv : EvenSite (z.1 - 1, z.2 - 1) := by
    unfold EvenSite at hev ⊢
    omega
  obtain ⟨⟨-, hvd⟩, -⟩ := TpFrame.freeH_even_tu frame hdiag hdiagEv
  have hsup := RouteSteps.freeH_even_s_lt frame hz hev
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    omega
  -- z.1 ≥ 2: z.1 = 1 would force z.2 odd, hence z.2 ≥ 1, and then t(z) = n - d z.2 ≤ n - d < 2
  have hx2 : 2 ≤ z.1 := by
    by_contra hlt
    have h1 : z.1 = 1 := by omega
    have hy1 : 1 ≤ z.2 := by
      unfold EvenSite at hev
      omega
    unfold ChildFrame.tGrade at ht2
    rw [h1] at ht2
    nlinarith
  -- s(z) ≥ 2(d + n)
  have hsl : 2 * (frame.child.den + frame.child.num) ≤ frame.sGrade z := by
    unfold ChildFrame.sGrade
    nlinarith
  -- the translated grades of the axial source, and the bounds
  unfold ChildFrame.tGrade at ht2 hvd
  unfold ChildFrame.sGrade at hsl hsup
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, w1t, w1s, w1T, if_neg hodd]
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  rw [hTd] at hsup
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- A free H root is not strictly interior (strict sites are nonfree, and a free site is not). -/
theorem not_strict_of_freeH {frame : ChildFrame} {v : Site} (hv : v ∈ frame.freeH) :
    ¬ StrictInterior frame.child.num frame.child.den v := by
  intro hS
  have hnf := strictInterior_nonfree frame hS
  exact hnf 0 (FLatticePaper.RouteStay.zero_mem_span frame) (Set.mem_union_left _ (by simpa using hv))

/-- **The H C2 axial arrow.** For an even free H root `z` with a free diagonal predecessor, the axial predecessor
`u = (z.1 - 1, z.2)` is black, or the canonical policy keeps its diagonal next `(z.1 - 1, z.2 - 1)`. -/
theorem c2_axial_arrow {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) (hdiag : (z.1 - 1, z.2 - 1) ∈ frame.freeH) :
    laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 - 1) := by
  by_cases hb : laplacian G (z.1 - 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2) = 0 := (hbin _).resolve_left hb
    have hSI := west_strict frame hz hev hdiag
    have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
      unfold EvenSite at hev ⊢
      omega
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + 0) (u + 0) := fun x u => by simp
    have hs : EvenSite (0 : Site) := by
      unfold EvenSite
      norm_num
    have hin : (z.1 - 1, z.2 - 1) = incomingNeg (z.1 - 1, z.2) ∨ (z.1 - 1, z.2 - 1) = incomingPos (z.1 - 1, z.2) :=
      Or.inl (by unfold incomingNeg; rw [if_neg hodd])
    have hport := not_strict_of_freeH (frame := frame) hdiag
    have key := FLatticePaper.RouteRegion.route_port_arrow C hW1 (q := (z.1 - 1, z.2)) (nxt := (z.1 - 1, z.2 - 1)) (s := 0) hs hT
      (by simpa using hw) (by simpa using hSI) hin (by simpa using hport)
    simpa using key

/-- The even free H root has `s(z) ≥ 2(d + n)`: the box gives `z.1 ≥ 1`, and `z.1 = 1` would force `z.2 ≥ 1`, hence
`t(z) ≤ n - d < 2`. -/
theorem even_sGrade_ge (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    2 * (frame.child.den + frame.child.num) ≤ frame.sGrade z := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hx1, hxd, hy0, hyn⟩ := FreeTraceBox.freeH_box frame hz
  obtain ⟨⟨ht2, -⟩, -⟩ := TpFrame.freeH_even_tu frame hz hev
  have hx2 : 2 ≤ z.1 := by
    by_contra hlt
    have h1 : z.1 = 1 := by omega
    have hy1 : 1 ≤ z.2 := by
      unfold EvenSite at hev
      omega
    unfold ChildFrame.tGrade at ht2
    rw [h1] at ht2
    nlinarith
  unfold ChildFrame.sGrade
  nlinarith

/-- The west-and-down site `(z.1, z.2 - 1) + V` is strictly interior, for an even free H root `z`. -/
theorem down_translate_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    StrictInterior frame.child.num frame.child.den ((z.1, z.2 - 1) + FLatticePaper.RoutePlus.Vt frame) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨⟨ht2, htd⟩, -⟩ := TpFrame.freeH_even_tu frame hz hev
  have hsl := even_sGrade_ge frame hz hev
  have hsup := RouteSteps.freeH_even_s_lt frame hz hev
  have hodd : ¬ EvenSite ((z.1, z.2 - 1) + FLatticePaper.RoutePlus.Vt frame) := by
    simp only [EvenSite, FLatticePaper.RoutePlus.Vt, Prod.fst_add, Prod.snd_add] at hev ⊢
    omega
  have hTbig : 2 * frame.child.den - 2 < frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega)]
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  unfold ChildFrame.tGrade at ht2 htd
  unfold ChildFrame.sGrade at hsl hsup
  rw [hTd] at hsup
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, w1t, w1s, w1T, if_neg hodd]
  simp only [FLatticePaper.RoutePlus.Vt, Prod.fst_add, Prod.snd_add]
  dsimp only at hsup
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hTbig]

/-- **The H C2 second arrow.** For an even free H root `z`, the arrow from `(z.1, z.2 - 1)` to `z` is black, or the canonical
policy keeps `z` there: the source is strictly interior after the translation by `V`, and `z` is a free port. -/
theorem c2_down_arrow {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) z := by
  by_cases hb : laplacian G (z.1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have hodd : ¬ EvenSite (z.1, z.2 - 1) := by
      unfold EvenSite at hev ⊢
      omega
    have hV : frame.child.modifiedDeck.combine 0 1 = FLatticePaper.RoutePlus.Vt frame :=
      ChainWire.combine_zero_one_eq_Vdeck frame
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + FLatticePaper.RoutePlus.Vt frame) (u + FLatticePaper.RoutePlus.Vt frame) := by
      intro x u
      have h := hdeck 0 1 x u
      rw [hV] at h
      exact h
    have hVev : EvenSite (FLatticePaper.RoutePlus.Vt frame) := by
      unfold EvenSite FLatticePaper.RoutePlus.Vt
      obtain ⟨hn0, hnd, hd2, hd3, hT'⟩ := frame.child_facts
      omega
    have hqw : laplacian G ((z.1, z.2 - 1) + FLatticePaper.RoutePlus.Vt frame) = 0 := by
      unfold FLatticePaper.RoutePlus.Vt
      rw [StripColours.lap_add_transverse frame hP.periods]
      exact hw
    have hqS := down_translate_strict frame hz hev
    have hin : z = incomingPos (z.1, z.2 - 1) := by
      unfold incomingPos
      rw [if_neg hodd]
      ext <;> simp
    have hport : ¬ StrictInterior frame.child.num frame.child.den (z + FLatticePaper.RoutePlus.Vt frame) := by
      intro hS
      have hnf := strictInterior_nonfree frame hS
      have hz' := (FLatticePaper.RoutePlus.nonfree_add_Vt frame z).mp hnf
      exact hz' 0 (FLatticePaper.RouteStay.zero_mem_span frame) (Set.mem_union_left _ (by simpa using hz))
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hVev hT hqw hqS (Or.inr hin) hport

/-- **The H C2 diagonal arrow.** The free diagonal `(z.1 - 1, z.2 - 1)` of an even root keeps `(z.1, z.2 - 1)`: its prescribed
input is `(1, 0)` (even free H root). -/
theorem c2_diag_arrow {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hev : EvenSite z) (hv : (z.1 - 1, z.2 - 1) ∈ frame.freeH) :
    laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1, z.2 - 1) := by
  by_cases hb : laplacian G (z.1 - 1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 - 1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have hvev : EvenSite (z.1 - 1, z.2 - 1) := by
      unfold EvenSite at hev ⊢
      omega
    refine (C.prescribed.1 _ hv hw _).mpr ?_
    rw [FLatticePaper.InternalReturns.prescribedH_even frame η hvev]
    ext <;> simp

/-- **The H C2 row of the route structure.** For an even free H root `z` with a free diagonal predecessor, the three arrows of the
`C.2` route are black or kept by the canonical policy: the axial and the last arrow by the port instances, the diagonal by the
prescription. -/
theorem h2_C2 {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) :
    ∀ z ∈ frame.freeH, laplacian G z = 0 → EvenSite z → (z.1 - 1, z.2 - 1) ∈ frame.freeH →
      (laplacian G (z.1 - 1, z.2) = -1 ∨ C.policy (z.1 - 1, z.2) (z.1 - 1, z.2 - 1)) ∧
      (laplacian G (z.1 - 1, z.2 - 1) = -1 ∨ C.policy (z.1 - 1, z.2 - 1) (z.1, z.2 - 1)) ∧
      (laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) z) := by
  intro z hz _ hev hdiag
  exact ⟨c2_axial_arrow C hW1 hbin hz hev hdiag, c2_diag_arrow C hbin hev hdiag,
    c2_down_arrow C hW1 hP hdeck hbin hz hev⟩

end FLatticePaper.C2Axial
