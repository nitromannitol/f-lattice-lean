import FLatticePaper.Plane.Induction.V2Arrows
import FLatticePaper.Plane.Induction.FreeCutPred
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.RouteRegion
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.InternalReturns

/-! # The v2 row for `η = -1`, by the reflection `x ↦ vLast − x + (d, n)`

The reflection `σ x = vLast − x + (d, n)` preserves the strict interior (`strict_reflect`) and sends the free V cut to its
translate `vLast − z` (`FreeCutPred.freeV_reflect`). An `η = -1` configuration at `z` (free odd root, free diagonal
`(z.1 + 1, z.2 − 1)`) is mapped to the `η = +1` configuration at `w = vLast − z`, so its two strict facts are the `η = +1` facts
`V2Arrows.plus_source_strict` and `V2Arrows.plus_next_strict`. The policy is not reflected: the arrows are the route arrows of the
canonical policy of sign `−1` (`RouteRegion.route_port_arrow`), and the prescription of sign `−1` at odd free V roots is `(0, 1)`. -/

namespace FLatticePaper.V2Minus

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The reflection identity for the strict interior. -/
theorem strict_reflect (frame : ChildFrame) (x : Site) :
    StrictInterior frame.child.num frame.child.den x ↔
      StrictInterior frame.child.num frame.child.den
        (frame.vLast - x + (frame.child.den, frame.child.num)) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hyeq : EvenSite (frame.vLast - x + (frame.child.den, frame.child.num)) ↔ EvenSite x := by
    unfold EvenSite ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    omega
  have ht : w1t frame.child.num frame.child.den (frame.vLast - x + (frame.child.den, frame.child.num))
      = (frame.child.num + frame.child.den - (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2))
        - w1t frame.child.num frame.child.den x := by
    unfold w1t ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  have hs : w1s frame.child.num frame.child.den (frame.vLast - x + (frame.child.den, frame.child.num))
      = (2 * frame.child.num + (frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2))
        - w1s frame.child.num frame.child.den x := by
    unfold w1s ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring
  unfold StrictInterior
  by_cases hx : EvenSite x
  · have hy : EvenSite (frame.vLast - x + (frame.child.den, frame.child.num)) := hyeq.mpr hx
    simp only [w1b, w1a, w1h, w1c, w1T, if_pos hx, if_pos hy]
    rw [ht, hs]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · have hy : ¬ EvenSite (frame.vLast - x + (frame.child.den, frame.child.num)) := fun h => hx (hyeq.mp h)
    simp only [w1b, w1a, w1h, w1c, w1T, if_neg hx, if_neg hy]
    rw [ht, hs]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The reflection `z ↦ vLast − z` maps the free V cut to itself (`FreeCutPred.freeV_reflect`). -/
theorem vLast_sub_mem_freeV (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) :
    frame.vLast - z ∈ frame.freeV := by
  have h := FLatticePaper.FreeCutPred.freeV_reflect frame (x := z.1) (y := z.2) hz
  have e : frame.vLast - z
      = (frame.child.num - frame.child.den + 1 - z.1, frame.child.num + frame.child.den - 1 - z.2) := by
    ext <;> simp [ChildFrame.vLast]
  rw [e]
  exact h

/-- The reflection of an odd site is odd. -/
theorem odd_vLast_sub (frame : ChildFrame) {z : Site} (hodd : ¬ EvenSite z) : ¬ EvenSite (frame.vLast - z) := by
  unfold EvenSite ChildFrame.vLast at *
  simp only [Prod.fst_sub, Prod.snd_sub] at *
  omega

/-- The reflected diagonal: `vLast − (z.1 + 1, z.2 − 1)` is the `η = +1` diagonal of `w = vLast − z`. -/
theorem reflect_diag (frame : ChildFrame) {z : Site} (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    ((frame.vLast - z).1 - 1, (frame.vLast - z).2 + 1) ∈ frame.freeV := by
  have h := vLast_sub_mem_freeV frame hdiag
  have e : frame.vLast - (z.1 + 1, z.2 - 1) = ((frame.vLast - z).1 - 1, (frame.vLast - z).2 + 1) := by
    ext <;> simp [ChildFrame.vLast] <;> ring
  rw [← e]
  exact h

/-- **The source of the `η = −1` first arrow is strict after the deck shift `(d, n)`.** Its reflection is the `η = +1` source
`(w.1, w.2 + 1)` of `w = vLast − z`, strict by `V2Arrows.plus_source_strict`. -/
theorem minus_source_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    StrictInterior frame.child.num frame.child.den ((z.1, z.2 - 1) + (frame.child.den, frame.child.num)) := by
  apply (strict_reflect frame _).mpr
  have e : frame.vLast - ((z.1, z.2 - 1) + (frame.child.den, frame.child.num)) + (frame.child.den, frame.child.num)
      = ((frame.vLast - z).1, (frame.vLast - z).2 + 1) := by
    ext <;> simp [ChildFrame.vLast] <;> ring
  rw [e]
  exact FLatticePaper.V2Arrows.plus_source_strict frame (vLast_sub_mem_freeV frame hz) (odd_vLast_sub frame hodd)
    (reflect_diag frame hdiag)

/-- **The middle site of the `η = −1` third arrow is strict.** Its reflection is the `η = +1` translate `(w.1 − 1, w.2) + (d, n)`
of `V2Arrows.plus_next_strict`. -/
theorem minus_next_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    StrictInterior frame.child.num frame.child.den (z.1 + 1, z.2) := by
  apply (strict_reflect frame _).mpr
  have e : frame.vLast - (z.1 + 1, z.2) + (frame.child.den, frame.child.num)
      = ((frame.vLast - z).1 - 1, (frame.vLast - z).2) + (frame.child.den, frame.child.num) := by
    ext
    · simp [ChildFrame.vLast]
      ring
    · simp [ChildFrame.vLast]
  rw [e]
  exact FLatticePaper.V2Arrows.plus_next_strict frame (vLast_sub_mem_freeV frame hz) (odd_vLast_sub frame hodd)
    (reflect_diag frame hdiag)

/-- A free V root translated by `(d, n)` is not strict: a strict translate would make the root nonfree. -/
theorem not_strict_shift_of_freeV {frame : ChildFrame} {D : Site} (hD : D ∈ frame.freeV) :
    ¬ StrictInterior frame.child.num frame.child.den (D + (frame.child.den, frame.child.num)) := by
  intro hS
  have hnf := FLatticePaper.Induction.strictInterior_nonfree frame hS
  apply hnf (-(frame.child.den, frame.child.num))
    (FLatticePaper.Induction.span_neg_mem (FLatticePaper.Induction.Kdeck_mem_span frame))
  rw [show D + (frame.child.den, frame.child.num) + -(frame.child.den, frame.child.num) = D by abel]
  exact Set.mem_union_right _ hD

/-- **The `η = −1` first arrow of `v2`.** The even source `(z.1, z.2 − 1)` is not strict, but its deck translate by `(d, n)` is,
with the free diagonal as port (`route_port_arrow` with the shift `(d, n)`). -/
theorem v2_a0_minus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    laplacian G (z.1, z.2 - 1) = -1 ∨ C.policy (z.1, z.2 - 1) (z.1 + 1, z.2 - 1) := by
  by_cases hb : laplacian G (z.1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have heven : EvenSite (z.1, z.2 - 1) := by
      unfold EvenSite at hodd ⊢
      omega
    have hK : frame.child.modifiedDeck.combine 1 0 = (frame.child.den, frame.child.num) :=
      ChainWire.combine_one_zero_eq_Kdeck frame
    have hT : ∀ x u, C.policy x u ↔
        C.policy (x + (frame.child.den, frame.child.num)) (u + (frame.child.den, frame.child.num)) := by
      intro x u
      have h := hdeck 1 0 x u
      rw [hK] at h
      exact h
    have hsK : EvenSite (frame.child.den, frame.child.num) := by
      unfold EvenSite
      have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
      omega
    have hqw : laplacian G ((z.1, z.2 - 1) + (frame.child.den, frame.child.num)) = 0 := by
      rw [StripColours.lap_add_kernel frame hP.periods]
      exact hw
    have hqS := minus_source_strict frame hz hodd hdiag
    have hin : (z.1 + 1, z.2 - 1) = incomingNeg (z.1, z.2 - 1) ∨ (z.1 + 1, z.2 - 1) = incomingPos (z.1, z.2 - 1) :=
      Or.inr (by unfold incomingPos; rw [if_pos heven])
    have hport := not_strict_shift_of_freeV (frame := frame) hdiag
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hsK hT hqw hqS hin hport

/-- **The `η = −1` middle arrow of `v2`.** The free odd diagonal keeps `(z.1 + 1, z.2)`: its prescribed input is `(0, 1)`. -/
theorem v2_a1_minus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = -1)
    {z : Site} (hodd : ¬ EvenSite z) (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    laplacian G (z.1 + 1, z.2 - 1) = -1 ∨ C.policy (z.1 + 1, z.2 - 1) (z.1 + 1, z.2) := by
  by_cases hb : laplacian G (z.1 + 1, z.2 - 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 + 1, z.2 - 1) = 0 := (hbin _).resolve_left hb
    have hodd1 : ¬ EvenSite (z.1 + 1, z.2 - 1) := by
      unfold EvenSite at hodd ⊢
      omega
    refine (C.prescribed.2 _ hdiag hw _).mpr ?_
    rw [FLatticePaper.InternalReturns.prescribedV_odd frame η hodd1, hη]
    ext <;> simp

/-- **The `η = −1` third arrow of `v2`.** The free root `z` is the input of its even source `(z.1 + 1, z.2)` (no shift), strict by
`minus_next_strict`, and `z` is a free port. -/
theorem v2_a2_minus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 + 1, z.2 - 1) ∈ frame.freeV) :
    laplacian G (z.1 + 1, z.2) = -1 ∨ C.policy (z.1 + 1, z.2) z := by
  by_cases hb : laplacian G (z.1 + 1, z.2) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1 + 1, z.2) = 0 := (hbin _).resolve_left hb
    have heven : EvenSite (z.1 + 1, z.2) := by
      unfold EvenSite at hodd ⊢
      omega
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + 0) (u + 0) := fun x u => by simp
    have hs : EvenSite (0 : Site) := by
      unfold EvenSite
      norm_num
    have hqw : laplacian G ((z.1 + 1, z.2) + 0) = 0 := by simpa using hw
    have hqS : StrictInterior frame.child.num frame.child.den ((z.1 + 1, z.2) + 0) := by
      simpa using minus_next_strict frame hz hodd hdiag
    have hin : z = incomingNeg (z.1 + 1, z.2) ∨ z = incomingPos (z.1 + 1, z.2) :=
      Or.inl (by unfold incomingNeg; rw [if_pos heven]; ext <;> simp)
    have hport : ¬ StrictInterior frame.child.num frame.child.den (z + 0) := by
      simpa using FLatticePaper.V2Arrows.not_strict_of_freeV (frame := frame) hz
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hs hT hqw hqS hin hport

/-- **The v2 row for `η = −1`**, in the form of the `v2` field of `RouteGenuine` (with `η` substituted). -/
theorem v2_row_minus {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = -1)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 + -η, z.2 - -η) ∈ frame.freeV) :
    (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 + -η, z.2 - -η)) ∧
    (laplacian G (z.1 + -η, z.2 - -η) = -1 ∨ C.policy (z.1 + -η, z.2 - -η) (z.1 + -η, z.2)) ∧
    (laplacian G (z.1 + -η, z.2) = -1 ∨ C.policy (z.1 + -η, z.2) z) := by
  subst hη
  have e0 : (z.1, z.2 - -(-1)) = (z.1, z.2 - 1) := Prod.ext rfl (by ring)
  have e1 : (z.1 + -(-1), z.2 - -(-1)) = (z.1 + 1, z.2 - 1) := Prod.ext (by ring) (by ring)
  have e2 : (z.1 + -(-1), z.2) = (z.1 + 1, z.2) := Prod.ext (by ring) rfl
  rw [e1] at hdiag
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e1]
    exact v2_a0_minus C hW1 hP hdeck hbin hz hodd hdiag
  · rw [e1, e2]
    exact v2_a1_minus C hbin rfl hodd hdiag
  · rw [e2]
    exact v2_a2_minus C hW1 hbin hz hodd hdiag

/-- **The v2 row for both signs**, in the exact form of the `v2` field of `RouteGenuine` (`η = 1` from `V2Arrows.v2_row_plus`,
`η = -1` from `v2_row_minus`). -/
theorem v2_row {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = 1 ∨ η = -1)
    {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) (hdiag : (z.1 + -η, z.2 - -η) ∈ frame.freeV) :
    (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 + -η, z.2 - -η)) ∧
    (laplacian G (z.1 + -η, z.2 - -η) = -1 ∨ C.policy (z.1 + -η, z.2 - -η) (z.1 + -η, z.2)) ∧
    (laplacian G (z.1 + -η, z.2) = -1 ∨ C.policy (z.1 + -η, z.2) z) := by
  rcases hη with h | h
  · exact FLatticePaper.V2Arrows.v2_row_plus C hW1 hP hdeck hbin h hz hodd hdiag
  · exact v2_row_minus C hW1 hP hdeck hbin h hz hodd hdiag

/-- The `v2` field of `RouteGenuine` at a canonical policy of sign `η = ±1`. -/
theorem v2_field {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) (hP : frame.Packet G)
    (hdeck : ∀ (i j : ℤ) (x u : Site), C.policy x u ↔
      C.policy (x + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j))
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (hη : η = 1 ∨ η = -1) :
    ∀ z ∈ frame.freeV, laplacian G z = 0 → ¬ EvenSite z → (z.1 + -η, z.2 - -η) ∈ frame.freeV →
      (laplacian G (z.1, z.2 - -η) = -1 ∨ C.policy (z.1, z.2 - -η) (z.1 + -η, z.2 - -η)) ∧
      (laplacian G (z.1 + -η, z.2 - -η) = -1 ∨ C.policy (z.1 + -η, z.2 - -η) (z.1 + -η, z.2)) ∧
      (laplacian G (z.1 + -η, z.2) = -1 ∨ C.policy (z.1 + -η, z.2) z) :=
  fun _ hz _ hodd hdiag => v2_row C hW1 hP hdeck hbin hη hz hodd hdiag

end FLatticePaper.V2Minus
