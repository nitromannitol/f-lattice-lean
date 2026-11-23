import FLatticePaper.Plane.Induction.TwoRank
import FLatticePaper.Plane.Induction.BothFreeGrades

/-! Task 72 / Q20: the both-free exclusion of a raw rise, with the per-sign prescription link (Q1: the auxiliary game of sign `η`
prescribes `prescribedH η` / `prescribedV η` at free white centres; the F-policy has sign `η`, the translated opposite g-policy has
sign `−η`, so its selection at `z + ησ` is the `(−η)`-prescription).

`both_free_rise_false`: at a rise whose roots `z` and `z + ησ` are free, the two selections differ (`u ≠ v`) while the prescriptions
force them equal. The shifted-V case uses the price constancy on the V star, under the harmonic-window hypothesis `hwin`. -/

namespace FLatticePaper.BothFreeRise

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.BothFreeGrades

/-- The policy `P` of sign `η` prescribes the free directions: at a free H (V) white centre its only selected input is the prescribed
one. -/
def PrescribedAt (frame : ChildFrame) (F : Field) (η : ℤ) (P : Site → Site → Prop) : Prop :=
  (∀ c, c ∈ frame.freeH → laplacian F c = 0 → ∀ j, P c j ↔ j = c + frame.prescribedH η c) ∧
  (∀ c, c ∈ frame.freeV → laplacian F c = 0 → ∀ j, P c j ↔ j = c + frame.prescribedV η c)

theorem shiftσ_eq (frame : ChildFrame) (η : ℤ) : shiftσ frame η = η • frame.shortShift := by
  ext <;> simp

/-- The price is constant between two V-star sites whose grades lie in the harmonic window `[3 − 2d, 2L − 1]` (the window of the
centre and of its input, shifted by the parent step `v`, which has grade `2`). -/
theorem price_const_of_window (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F) {z u : Site}
    (hz : 3 - 2 * frame.child.den ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1)
    (hu : 3 - 2 * frame.child.den ≤ frame.sGrade u ∧ frame.sGrade u ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    frame.price F u = frame.price F z := by
  have hz1 : F z = harmonicGrid z := hS.2 z (by omega) (by omega)
  have hu1 : F u = harmonicGrid u := hS.2 u (by omega) (by omega)
  have hz2 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift) := by
    have hsz := sGrade_sub frame z frame.parentShift
    rw [sGrade_parentShift] at hsz
    exact hS.2 _ (by omega) (by omega)
  have hu2 : F (u - frame.parentShift) = harmonicGrid (u - frame.parentShift) := by
    have hsu := sGrade_sub frame u frame.parentShift
    rw [sGrade_parentShift] at hsu
    exact hS.2 _ (by omega) (by omega)
  exact price_const_on_star frame F hz1 hz2 hu1 hu2

/-- **Both-free exclusion.** A rise `P(u + ησ) = P(z + ησ) + 1` at `z → u` (with `z`, `z + ησ` white and the other input `v` of `z`
selected by the translated opposite policy `Q`) is impossible when both roots are free. -/
theorem both_free_rise_false (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    {P Q : Site → Site → Prop} (hP : PrescribedAt frame F η P) (hQ : PrescribedAt frame F (-η) Q)
    {z u v : Site} (hPu : P z u) (hwF : laplacian F z = 0) (hwG : laplacian F (z + η • frame.shortShift) = 0)
    (hzF : z ∈ frame.freeH ∨ z ∈ frame.freeV)
    (hzG : z + η • frame.shortShift ∈ frame.freeH ∨ z + η • frame.shortShift ∈ frame.freeV)
    (hvu : v ≠ u) (hvQ : Q (z + η • frame.shortShift) (v + η • frame.shortShift))
    (hwin : z + η • frame.shortShift ∈ frame.freeV →
      (3 - 2 * frame.child.den ≤ frame.sGrade (z + η • frame.shortShift) ∧
        frame.sGrade (z + η • frame.shortShift) ≤ 2 * (frame.child.den + frame.child.num) - 1) ∧
      (3 - 2 * frame.child.den ≤ frame.sGrade (u + η • frame.shortShift) ∧
        frame.sGrade (u + η • frame.shortShift) ≤ 2 * (frame.child.den + frame.child.num) - 1))
    (hrise : frame.price F (u + η • frame.shortShift) = frame.price F (z + η • frame.shortShift) + 1) : False := by
  by_cases hz'V : z + η • frame.shortShift ∈ frame.freeV
  · -- the shifted centre is a V root: the price is constant on its star, against the unit rise
    obtain ⟨hw1, hw2⟩ := hwin hz'V
    have := price_const_of_window frame F hS hw1 hw2
    omega
  · have hz'H : z + η • frame.shortShift ∈ frame.freeH := by
      rcases hzG with h | h
      · exact h
      · exact absurd h hz'V
    -- the translated opposite selection at `z + ησ`: `v = z + prescribedH (−η) (z + ησ)`
    have hvsel := (hQ.1 _ hz'H hwG (v + η • frame.shortShift)).mp hvQ
    have hv : v = z + frame.prescribedH (-η) (z + η • frame.shortShift) := by
      have h2 : v + η • frame.shortShift = z + η • frame.shortShift + frame.prescribedH (-η) (z + η • frame.shortShift) := hvsel
      calc v = (v + η • frame.shortShift) - η • frame.shortShift := by abel
        _ = (z + η • frame.shortShift + frame.prescribedH (-η) (z + η • frame.shortShift)) - η • frame.shortShift := by rw [h2]
        _ = z + frame.prescribedH (-η) (z + η • frame.shortShift) := by abel
    rcases hzF with hzH | hzV
    · -- H/H: the two prescribed directions agree
      have hu : u = z + frame.prescribedH η z := (hP.1 z hzH hwF u).mp hPu
      have hw' : z + shiftσ frame η ∈ frame.freeH := by
        rw [shiftσ_eq]
        exact hz'H
      have hag := prescribedH_shift_agree frame hη hzH hw'
      rw [shiftσ_eq] at hag
      apply hvu
      rw [hu, hv, ← hag]
    · -- V/H: the V prescription agrees with the H prescription of the shifted H centre (`k = 0`)
      have hu : u = z + frame.prescribedV η z := (hP.2 z hzV hwF u).mp hPu
      have hr : z + η • frame.shortShift = (z + shiftσ frame η) -
          ((0 : ℤ) * frame.child.modifiedDeck.transverse.1, (0 : ℤ) * frame.child.modifiedDeck.transverse.2) := by
        rw [shiftσ_eq]
        refine Prod.ext ?_ ?_ <;> simp
      have hag := V_H_choices_agree_derived frame hη hzV 0 (z + η • frame.shortShift) hr hz'H
      apply hvu
      rw [hu, hv, hag]

/-- **The chain monotonicity from the free roots.** `Φ_η` does not increase along the F-policy `C.policy`, given: the per-sign
prescription links (`hLinkP` for sign `η`, `hLinkQ` for the translated opposite policy `opp` of sign `−η`), the opposite policy's raw
slip monotonicity (`ChainPairData.oppRawSlip`), its quota and price monotonicity (`hoppQuota`, `hoppPrice`), the unit shifted-price
increments (`hunit`, from `HasUnitPrice`), the harmonic window at a shifted V root (`hwin`), and the forced transfer (`hfree`: a rise's
roots are free, the audit's finite unit forcing step, NOT yet formalized). -/
theorem chain_nonincreasing_of_free_roots (frame : ChildFrame) {F : Field} (C : CanonicalSignedPolicy frame F)
    (hS : frame.HasStrips F) {η : ℤ} (hη : η = 1 ∨ η = -1) (opp : Site → Site → Prop)
    (hoppRaw : NonincreasingAlong (fun y => F y - F (y + (-η) • frame.shortShift)) opp)
    (hoppQuota : RetainQuota F opp) (hoppPrice : ∀ c i, opp c i → frame.price F i ≤ frame.price F c)
    (hlapF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) (hU : HasUnitPrice frame F)
    (hLinkP : PrescribedAt frame F η C.policy) (hLinkQ : PrescribedAt frame F (-η) opp)
    (hfree : ∀ z u, C.policy z u → frame.chainPotential F η z < frame.chainPotential F η u →
      (z ∈ frame.freeH ∨ z ∈ frame.freeV) ∧ (z + η • frame.shortShift ∈ frame.freeH ∨ z + η • frame.shortShift ∈ frame.freeV))
    (hwin : ∀ z u, C.policy z u → frame.chainPotential F η z < frame.chainPotential F η u →
      z + η • frame.shortShift ∈ frame.freeV →
      (3 - 2 * frame.child.den ≤ frame.sGrade (z + η • frame.shortShift) ∧
        frame.sGrade (z + η • frame.shortShift) ≤ 2 * (frame.child.den + frame.child.num) - 1) ∧
      (3 - 2 * frame.child.den ≤ frame.sGrade (u + η • frame.shortShift) ∧
        frame.sGrade (u + η • frame.shortShift) ≤ 2 * (frame.child.den + frame.child.num) - 1)) :
    NonincreasingAlong (frame.chainPotential F η) C.policy := by
  intro z u hu
  by_contra hlt
  rw [not_le] at hlt
  have hin : u = incomingNeg z ∨ u = incomingPos z := C.policyEdge z u hu
  -- the unit shifted-price increment on the F-policy edge, from `HasUnitPrice` at the even-translated edge `(u + ησ, z + ησ)`
  have hunit : ∀ a b, C.policy a b →
      frame.price F (b + η • frame.shortShift) ≤ frame.price F (a + η • frame.shortShift) + 1 := by
    intro a b hab
    have hs : ((η • frame.shortShift).1 + (η • frame.shortShift).2) % 2 = 0 := by
      obtain ⟨k, hk⟩ : (2 : ℤ) ∣ frame.shortShift.1 + frame.shortShift.2 :=
        Int.dvd_of_emod_eq_zero (FLatticePaper.BothFreeGrades.shortShift_even frame)
      rcases hη with rfl | rfl <;> simp <;> omega
    have he := TwoRank.edge_add_of_even (η • frame.shortShift) hs (C.policyEdge a b hab)
    have h1 := (hU _ _ he).2
    unfold priceIncrement at h1
    omega
  obtain ⟨hgF, hF, -, -, hPs, v, hv1, hv2, hvQ⟩ := TwoRank.rise_local_frame frame C hη opp hoppRaw hoppQuota hoppPrice
    hlapF hunit hu hin hlt
  obtain ⟨hzF, hzG⟩ := hfree z u hu hlt
  exact both_free_rise_false frame hS hη hLinkP hLinkQ hu hF hgF hzF hzG hv2 hvQ (fun h => hwin z u hu hlt h) hPs

end FLatticePaper.BothFreeRise
