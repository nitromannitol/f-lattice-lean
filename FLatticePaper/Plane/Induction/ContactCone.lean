import FLatticePaper.Plane.BellmanRank
import FLatticePaper.Plane.Induction.ComparisonContacts
import FLatticePaper.Plane.Induction.QuadraticCap

/-! # Task 98: the contact cone of a true fort (ALL_SLOPE_STEP, "every visited root is an m-contact in the actual fort")

A true fort `S` of a field `F` (`IsIncomingFort F S`: a black site of `S` has an input in `S`, a white site of `S` has both inputs in `S`).
A comparison field `m` with `m ≤ F` at the inputs and binary laplacian. A contact is a site of `S` with `F = m`. At a contact the two input
excesses `F − m` sum to `lap F − lap m` (the centre terms cancel), so:

* at a black contact both inputs are contacts (`contact_black`), and the fort gives an input in `S`;
* at a white contact the fort gives both inputs in `S`, and the excess sum is `−lap m ∈ {0, 1}`, so one input is a contact: the cone steps
  to a contact of `S` at every contact of `S` (`fort_contact_input`).

The comparison field of the fan is the vertical parabola `m(z) = capMin (z.2 − b)` (`QuadraticCap`): laplacian `0` at even sites (horizontal
inputs) and `−1` at odd sites (vertical inputs). -/

namespace FLatticePaper.ContactCone

open FLatticePaper FLatticePaper.QuadraticCap

/-- The sum of the input excesses of `F` over `m` at a contact is the difference of the laplacians. -/
theorem excess_sum {F m : Field} {c : Site} (hc : F c = m c) :
    (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) =
      laplacian F c - laplacian m c := by
  unfold laplacian
  linarith

/-- **The contact cone step.** A contact of a true fort `S` of `F` has an input which is a contact of `S`. -/
theorem fort_contact_input {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S) {c : Site} (hcS : c ∈ S)
    (hc : F c = m c) (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0)
    (h1 : m (incomingNeg c) ≤ F (incomingNeg c)) (h2 : m (incomingPos c) ≤ F (incomingPos c)) :
    ∃ i : Site, (i = incomingNeg c ∨ i = incomingPos c) ∧ i ∈ S ∧ F i = m i := by
  have hsum := excess_sum (F := F) (m := m) hc
  rcases hfort c hcS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · -- black: both inputs are contacts (the excess sum is `−1 − lap m ≤ 0`)
    have hmc := hm c
    have hsum0 : (F (incomingNeg c) - m (incomingNeg c)) + (F (incomingPos c) - m (incomingPos c)) ≤ 0 := by
      rw [hsum, hl]
      omega
    have e1 : F (incomingNeg c) = m (incomingNeg c) := by omega
    have e2 : F (incomingPos c) = m (incomingPos c) := by omega
    rcases hsome with hn | hp'
    · exact ⟨incomingNeg c, Or.inl rfl, hn, e1⟩
    · exact ⟨incomingPos c, Or.inr rfl, hp', e2⟩
  · -- white: both inputs are in `S`; the excess sum is `−lap m ∈ {0, 1}`
    have hmc := hm c
    rw [hl] at hsum
    rcases hmc with hmc | hmc
    · -- `lap m c = −1`: the excess sum is one, so one input is a contact
      rw [hmc] at hsum
      by_cases e1 : F (incomingNeg c) = m (incomingNeg c)
      · exact ⟨incomingNeg c, Or.inl rfl, hn, e1⟩
      · exact ⟨incomingPos c, Or.inr rfl, hp, by omega⟩
    · -- `lap m c = 0`: the excess sum is zero, both inputs are contacts
      rw [hmc] at hsum
      exact ⟨incomingNeg c, Or.inl rfl, hn, by omega⟩

/-- **The parabola comparison field** `m(z) = capMin (z.2 − b)` (vertical in `z.2`). -/
def parabolaField (b : ℤ) : Field := fun z => capMin (z.2 - b)

theorem parabola_lap_even (b : ℤ) (z : Site) (hz : EvenSite z) : laplacian (parabolaField b) z = 0 := by
  unfold laplacian parabolaField incomingNeg incomingPos
  simp only [hz, if_true]
  ring

theorem parabola_lap_odd (b : ℤ) (z : Site) (hz : ¬ EvenSite z) : laplacian (parabolaField b) z = -1 := by
  unfold laplacian parabolaField incomingNeg incomingPos
  simp only [hz, if_false]
  have h1 := two_capMin (z.2 - b - 1)
  have h2 := two_capMin (z.2 - b + 1)
  have h0 := two_capMin (z.2 - b)
  have h : 2 * (capMin (z.2 - 1 - b) + capMin (z.2 + 1 - b) - 2 * capMin (z.2 - b)) = -2 := by
    have e1 : z.2 - 1 - b = z.2 - b - 1 := by ring
    have e2 : z.2 + 1 - b = z.2 - b + 1 := by ring
    rw [e1, e2]
    linear_combination h1 + h2 - 2 * h0
  omega

theorem parabola_binary (b : ℤ) (z : Site) : laplacian (parabolaField b) z = -1 ∨ laplacian (parabolaField b) z = 0 := by
  by_cases hz : EvenSite z
  · exact Or.inr (parabola_lap_even b z hz)
  · exact Or.inl (parabola_lap_odd b z hz)

end FLatticePaper.ContactCone
