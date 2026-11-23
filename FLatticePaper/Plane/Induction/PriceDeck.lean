import FLatticePaper.Plane.Induction.PriceBoundary
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.StrongPriceValues

/-! # The boundary price bound from the deck: the native V trace, the top and right traces, and `hbd` (task 111)

* `sGrade_parentShift`: the parent shift `v = ε(N−D, N+D)` has `s(v) = 2` (the child is `2·odd + even`, `ε = odd.det even`, `ε² = 1`).
* `price_on_freeV`: on the native V trace (`z ∈ freeV`), `F = h₀` at `z` and at `z − v` (both s-values lie in the band `[1−2d, 2L−1]` of
  `HasStrips`), so `P = c₀` (`StrongPriceValues.price_eq_cutPrice_of_harmonic`). This is provable, not an input.
* `si_neighbour_mem`, `not_strictInterior_of_onBoundary`: a strict-interior site has all four neighbours in the closed polygon, so a boundary
  site is outside the strict interior (checked by brute force on the valid child frames before proving).
* `hbd_of_packet`: `outside_SI_free` classifies a boundary site as free, or its translate by `−V` or `−K` is free. The transverse and kernel
  drifts (`ChildFrame.price_transverse`, `ChildFrame.price_kernel`) move the bound: `P(z) = P(z − V)` and `P(z) = P(z − K) − 1`. So the bound
  needs only the bottom bound `P ≤ c₀` on the free H trace (`hH`), which `PriceH` gives from the sheet-offer identity. -/

namespace FLatticePaper.PriceDeck

open Farey FLatticePaper FLatticePaper.Induction

/-- The child numerator and denominator are odd (`child_parity`), so their sums and differences are even. -/
theorem child_odd_witness (frame : ChildFrame) :
    ∃ a c : ℤ, frame.child.num = 2 * a + 1 ∧ frame.child.den = 2 * c + 1 := by
  obtain ⟨hn, hd⟩ := FLatticePaper.W1Exit.child_parity frame
  exact ⟨frame.child.num / 2, frame.child.den / 2, by omega, by omega⟩

/-- The period denominator `T = d² + 2dn − n²` is even. -/
theorem periodDenominator_even (frame : ChildFrame) : frame.child.periodDenominator % 2 = 0 := by
  obtain ⟨a, c, ha, hc⟩ := child_odd_witness frame
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [hT, ha, hc]
  have key : (2 * c + 1) ^ 2 + 2 * (2 * c + 1) * (2 * a + 1) - (2 * a + 1) ^ 2 =
      2 * (2 * c ^ 2 + 4 * c + 4 * c * a + 1 - 2 * a ^ 2) := by ring
  rw [key]
  exact Int.mul_emod_right _ _

/-- The s-grade is even. -/
theorem sGrade_even (frame : ChildFrame) (z : Site) : frame.sGrade z % 2 = 0 := by
  obtain ⟨a, c, ha, hc⟩ := child_odd_witness frame
  have key : frame.sGrade z = 2 * ((a + c + 1) * z.1 + (c - a) * z.2) := by
    unfold ChildFrame.sGrade
    rw [ha, hc]
    ring
  rw [key]
  exact Int.mul_emod_right _ _

/-- The shift of the sGrade by the parent shift: `s(v) = 2`. -/
theorem sGrade_parentShift (frame : ChildFrame) : frame.sGrade frame.parentShift = 2 := by
  have hd : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := by
    unfold ChildFrame.child Parents.current Parents.combine
    simp
  have hn : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := by
    unfold ChildFrame.child Parents.current Parents.combine
    simp
  have heps : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den := by
    unfold ChildFrame.eps Fraction.det
    ring
  have key : (frame.child.den + frame.child.num) * (frame.parents.odd.num - frame.parents.odd.den) +
      (frame.child.den - frame.child.num) * (frame.parents.odd.num + frame.parents.odd.den) =
      2 * (frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den) := by
    rw [hd, hn]
    ring
  have hsq := frame.eps_sq
  have hsv : frame.sGrade frame.parentShift =
      frame.eps * ((frame.child.den + frame.child.num) * (frame.parents.odd.num - frame.parents.odd.den) +
        (frame.child.den - frame.child.num) * (frame.parents.odd.num + frame.parents.odd.den)) := by
    unfold ChildFrame.sGrade ChildFrame.parentShift
    ring
  rw [hsv, key, ← heps]
  linear_combination (2 : ℤ) * hsq

/-- **The native V trace is provable**: on `freeV`, the price is `cutPrice`. The field is `h₀` at `z` and at `z − v` (both s-values lie in the
harmonic band `[1−2d, 2L−1]` of `HasStrips`), so `StrongPriceValues.price_eq_cutPrice_of_harmonic` applies. -/
theorem price_on_freeV (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F) {z : Site}
    (hz : z ∈ frame.freeV) : frame.price F z = frame.cutPrice := by
  obtain ⟨-, -, hvs⟩ := hz
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hsub : frame.sGrade (z - frame.parentShift) = frame.sGrade z - 2 := by
    rw [← sGrade_parentShift frame]
    unfold ChildFrame.sGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  unfold ChildFrame.vSpectrum at hvs
  obtain ⟨hev, hr⟩ := hvs
  have hb1 : 1 - 2 * frame.child.den ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
  have hb2 : 1 - 2 * frame.child.den ≤ frame.sGrade (z - frame.parentShift) ∧
      frame.sGrade (z - frame.parentShift) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
    rw [hsub]
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega
  exact FLatticePaper.StrongPriceValues.price_eq_cutPrice_of_harmonic frame F z
    (hS.2 z hb1.1 hb1.2) (hS.2 _ hb2.1 hb2.2)

/-- The grade `t` at a translate: `t(z + u) = t(z) + n u₁ − d u₂`. -/
theorem tGrade_add (frame : ChildFrame) (z u : Site) :
    frame.tGrade (z + u) = frame.tGrade z + (frame.child.num * u.1 - frame.child.den * u.2) := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The grade `s` at a translate: `s(z + u) = s(z) + L u₁ + (d − n) u₂`. -/
theorem sGrade_add (frame : ChildFrame) (z u : Site) :
    frame.sGrade (z + u) = frame.sGrade z + ((frame.child.den + frame.child.num) * u.1 +
      (frame.child.den - frame.child.num) * u.2) := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- A unit step changes the parity of a site. -/
theorem evenSite_add_unit (z u : Site) (hu : u = (0, 1) ∨ u = (0, -1) ∨ u = (1, 0) ∨ u = (-1, 0)) :
    EvenSite (z + u) ↔ ¬ EvenSite z := by
  rcases hu with rfl | rfl | rfl | rfl <;> unfold EvenSite <;> simp <;> omega

/-- A strict-interior site has all four neighbours in the closed polygon. -/
theorem si_neighbour_mem (frame : ChildFrame) {z : Site}
    (hz : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z) (u : Site)
    (hu : u = (0, 1) ∨ u = (0, -1) ∨ u = (1, 0) ∨ u = (-1, 0)) :
    z + u ∈ frame.closedPolygon := by
  obtain ⟨a, c, ha, hc⟩ := child_odd_witness frame
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hTev := periodDenominator_even frame
  have htp := tGrade_parity frame z
  have hsev := sGrade_even frame z
  have hpar := evenSite_add_unit z u hu
  rw [mem_closedPolygon_iff]
  rcases hu with rfl | rfl | rfl | rfl
  all_goals
    rw [tGrade_add, sGrade_add]
    dsimp only
    by_cases hE : EvenSite z
    · rw [if_neg (fun h => (hpar.mp h) hE)]
      have hS := (SI_even_iff frame z hE).1 hz
      simp only [EvenSite] at hE
      omega
    · rw [if_pos (hpar.mpr hE)]
      have hS := (SI_odd_iff frame z hE).1 hz
      simp only [EvenSite] at hE
      omega

/-- A boundary site of the closed polygon is outside the strict interior. -/
theorem not_strictInterior_of_onBoundary (frame : ChildFrame) {z : Site}
    (hz : FLatticePaper.Induction.OnBoundary frame.closedPolygon z) :
    ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z := by
  intro hSI
  rcases hz with h | h | h | h
  · exact h.2 (si_neighbour_mem frame hSI _ (Or.inl rfl))
  · exact h.2 (si_neighbour_mem frame hSI _ (Or.inr (Or.inl rfl)))
  · exact h.2 (si_neighbour_mem frame hSI _ (Or.inr (Or.inr (Or.inl rfl))))
  · exact h.2 (si_neighbour_mem frame hSI _ (Or.inr (Or.inr (Or.inr rfl))))

/-- A free site has the bound `P ≤ c₀`: on the free H trace by the bottom bound `hH`, on the native V trace by `price_on_freeV`. -/
theorem price_le_of_free (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F)
    (hH : ∀ z ∈ frame.freeH, frame.price F z ≤ frame.cutPrice) {u : Site}
    (hu : u ∈ frame.freeH ∪ frame.freeV) : frame.price F u ≤ frame.cutPrice := by
  rcases hu with h | h
  · exact hH u h
  · rw [price_on_freeV frame F hS h]

/-- **`hbd` from the deck.** Given the bottom bound on the free H trace, the boundary bound holds at every boundary site: the site is free,
or its translate by `−V` (the transverse drift is zero) or by `−K` (the kernel drift is `−1`) is free. -/
theorem hbd_of_packet (frame : ChildFrame) (F : Field) (hpk : frame.Packet F)
    (hH : ∀ z ∈ frame.freeH, frame.price F z ≤ frame.cutPrice) :
    ∀ z, FLatticePaper.Induction.OnBoundary frame.closedPolygon z → frame.price F z ≤ frame.cutPrice := by
  intro z hz
  have hzE : z ∈ frame.closedPolygon := by
    rcases hz with h | h | h | h <;> exact h.1
  have hnot := not_strictInterior_of_onBoundary frame hz
  rcases outside_SI_free frame z hzE hnot with h | h | h
  · exact price_le_of_free frame F hpk.strips hH h
  · have hV : frame.child.modifiedDeck.transverse = Vdeck frame := by
      rw [ChildFrame.child_modifiedDeck_transverse]
      rfl
    have key := frame.price_transverse F hpk.periods (z + -Vdeck frame)
    rw [hV, show z + -Vdeck frame + Vdeck frame = z by abel] at key
    rw [key]
    exact price_le_of_free frame F hpk.strips hH h
  · have hK : frame.child.modifiedDeck.kernel = Kdeck frame := by
      rw [ChildFrame.child_modifiedDeck_kernel]
      rfl
    have key := frame.price_kernel F hpk.periods (z + -Kdeck frame)
    rw [hK, show z + -Kdeck frame + Kdeck frame = z by abel] at key
    have hb := price_le_of_free frame F hpk.strips hH h
    rw [key]
    omega

/-- **The bottom bound from the phase W0 of `PriceH`**: with the phase identity `P = c₀ − E_H`, the arc identity `E_H = 1 + min(0, Ψ − 1)`
and the `Ψ` values, the free H trace has `P ≤ c₀`. These are the named inputs of the bottom side. -/
theorem hH_of_phaseW0 (frame : ChildFrame) (F : Field) (EHv Ψ : Site → ℤ) (h0 : Site)
    (hh0 : h0 ∈ frame.freeH)
    (hP : ∀ z ∈ frame.freeH, frame.price F z = frame.cutPrice - EHv z)
    (hEH : ∀ z ∈ frame.freeH, EHv z = 1 + min 0 (Ψ z - 1))
    (hΨ0 : Ψ h0 = 0) (hΨ : ∀ z ∈ frame.freeH, z ≠ h0 → 1 ≤ Ψ z) (hΨnn : ∀ z ∈ frame.freeH, 0 ≤ Ψ z) :
    ∀ z ∈ frame.freeH, frame.price F z ≤ frame.cutPrice :=
  fun z hz => (FLatticePaper.PriceH.price_arc_W0 (frame.price F) EHv Ψ frame.cutPrice frame.freeH h0 hh0 hP hEH hΨ0 hΨ hΨnn).2.2 z hz

/-- **The bottom bound from the phase W1 of `PriceH`** (`P(z) = c₀ − 1 − E_H(refl z)`), the same conclusion. -/
theorem hH_of_phaseW1 (frame : ChildFrame) (F : Field) (EHv Ψ refl : Site → ℤ) (h0 : Site)
    (hh0 : h0 ∈ frame.freeH)
    (hP : ∀ z ∈ frame.freeH, frame.price F z = frame.cutPrice - 1 - EHv (refl z))
    (hEH : ∀ z ∈ frame.freeH, EHv (refl z) = min 0 (Ψ (refl z) - 1))
    (hΨ0 : Ψ (refl h0) = 0) (hΨ : ∀ z ∈ frame.freeH, z ≠ h0 → 1 ≤ Ψ (refl z))
    (hΨnn : ∀ z ∈ frame.freeH, 0 ≤ Ψ (refl z)) :
    ∀ z ∈ frame.freeH, frame.price F z ≤ frame.cutPrice :=
  fun z hz => (FLatticePaper.PriceH.price_arc_W1 (frame.price F) EHv Ψ refl frame.cutPrice frame.freeH h0 hh0 hP hEH hΨ0 hΨ hΨnn).2.2 z hz

end FLatticePaper.PriceDeck
