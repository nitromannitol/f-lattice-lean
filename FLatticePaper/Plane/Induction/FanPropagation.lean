import FLatticePaper.Plane.Induction.ContactCone
import FLatticePaper.Plane.Induction.W1Finite

/-! # Task 98 (2): the fan propagation of contacts and its first boundary exit (ALL_SLOPE_STEP, the low- and high-slope fans; FIXED_FREE §9)

Let `S` be a true fort of `F` (`IsIncomingFort F S`), and `m` a comparison field: binary, even sites with laplacian `0` (horizontal inputs,
the parabola's zero deficit), and `m ≤ F` everywhere (the window bound). A contact is a point of `S` with `F = m`.

* From an even contact both inputs are contacts in `S` (`even_contact_both`): the east input is the fan's step.
* From an odd contact a contacting input in `S` exists (`fort_contact_input`): the fan's selected step.

Iterating these steps from a contact `v₀` gives a fan path `p n` of contacts in `S`. Its `x`-coordinate advances by one every two steps
(an even step is east, an odd step is vertical), so the path cannot stay in the finite strict interior forever. Hence it has a first exit
`p k ∉ StrictInterior`, a contact of `S` on the boundary, reached through strict-interior contacts (`fan_first_exit`). The boundary terminal
is then excluded by its paid removal (the hypothesis of `fan_paid_contradiction`), which is FIXED_FREE §9's terminal step. -/

namespace FLatticePaper.FanPropagation

open FLatticePaper FLatticePaper.ContactCone

theorem incomingPos_of_even (v : Site) (h : EvenSite v) : incomingPos v = (v.1 + 1, v.2) := by
  unfold incomingPos
  rw [if_pos h]

theorem incomingNeg_of_even (v : Site) (h : EvenSite v) : incomingNeg v = (v.1 - 1, v.2) := by
  unfold incomingNeg
  rw [if_pos h]

theorem incomingPos_of_odd (v : Site) (h : ¬ EvenSite v) : incomingPos v = (v.1, v.2 + 1) := by
  unfold incomingPos
  rw [if_neg h]

theorem incomingNeg_of_odd (v : Site) (h : ¬ EvenSite v) : incomingNeg v = (v.1, v.2 - 1) := by
  unfold incomingNeg
  rw [if_neg h]

theorem not_even_incomingPos_of_even (v : Site) (h : EvenSite v) : ¬ EvenSite (incomingPos v) := by
  rw [incomingPos_of_even v h]
  unfold EvenSite at h ⊢
  simp only
  omega

theorem even_incomingNeg_of_odd (v : Site) (h : ¬ EvenSite v) : EvenSite (incomingNeg v) := by
  rw [incomingNeg_of_odd v h]
  unfold EvenSite at h ⊢
  simp only
  omega

theorem even_incomingPos_of_odd (v : Site) (h : ¬ EvenSite v) : EvenSite (incomingPos v) := by
  rw [incomingPos_of_odd v h]
  unfold EvenSite at h ⊢
  simp only
  omega

/-- **Both inputs of an even contact of a true fort are contacts in the fort** (the zero horizontal deficit of the parabola). -/
theorem even_contact_both {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S) {v : Site} (hv : v ∈ S)
    (hc : F v = m v) (he : laplacian m v = 0) (hle : ∀ x, m x ≤ F x) :
    incomingNeg v ∈ S ∧ incomingPos v ∈ S ∧ F (incomingNeg v) = m (incomingNeg v) ∧
      F (incomingPos v) = m (incomingPos v) := by
  have hsum := excess_sum (F := F) (m := m) hc
  have h1 := hle (incomingNeg v)
  have h2 := hle (incomingPos v)
  rcases hfort v hv with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · exfalso
    rw [hl, he] at hsum
    omega
  · rw [hl, he] at hsum
    refine ⟨hn, hp, ?_, ?_⟩
    · omega
    · omega

/-- **One fan step**: from a contact of `S` there is a contact of `S` as the next point, the east input at an even contact. -/
theorem fan_step {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) {v : Site} (hv : v ∈ S) (hc : F v = m v) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ (EvenSite v → w = incomingPos v) ∧
      (w = incomingNeg v ∨ w = incomingPos v) := by
  by_cases he : EvenSite v
  · obtain ⟨_, hp, _, ep⟩ := even_contact_both hfort hv hc (hme v he) hle
    exact ⟨incomingPos v, hp, ep, fun _ => rfl, Or.inr rfl⟩
  · obtain ⟨i, hi, hiS, hic⟩ := fort_contact_input hfort hv hc hm hle
    exact ⟨i, hiS, hic, fun h => absurd h he, hi⟩

/-- The contacts of `S` for `F` and `m`. -/
abbrev FanT (F m : Field) (S : Set Site) : Type := {v : Site // v ∈ S ∧ F v = m v}

/-- **The fan path** from a contact: the iterate of the chosen step. -/
theorem fan_path_exists {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) :
    ∃ next : FanT F m S → FanT F m S, ∀ v : FanT F m S,
      (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧ ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1) := by
  have hex : ∀ v : FanT F m S, ∃ w : FanT F m S,
      (EvenSite v.1 → w.1 = incomingPos v.1) ∧ (w.1 = incomingNeg v.1 ∨ w.1 = incomingPos v.1) := by
    intro v
    obtain ⟨w, hwS, hwc, hE, hI⟩ := fan_step hfort hm hme hle v.2.1 v.2.2
    exact ⟨⟨w, hwS, hwc⟩, hE, hI⟩
  choose next hnext using hex
  exact ⟨next, hnext⟩

theorem step_x_even {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S}
    (hnext : ∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1))
    (v : FanT F m S) (he : EvenSite v.1) : (next v).1.1 = v.1.1 + 1 := by
  rw [(hnext v).1 he, incomingPos_of_even _ he]

theorem step_x_odd {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S}
    (hnext : ∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1))
    (v : FanT F m S) (ho : ¬ EvenSite v.1) : (next v).1.1 = v.1.1 := by
  rcases (hnext v).2 with h | h
  · rw [h, incomingNeg_of_odd _ ho]
  · rw [h, incomingPos_of_odd _ ho]

theorem step_parity_even {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S}
    (hnext : ∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1))
    (v : FanT F m S) (he : EvenSite v.1) : ¬ EvenSite (next v).1 := by
  rw [(hnext v).1 he]
  exact not_even_incomingPos_of_even _ he

theorem step_parity_odd {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S}
    (hnext : ∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1))
    (v : FanT F m S) (ho : ¬ EvenSite v.1) : EvenSite (next v).1 := by
  rcases (hnext v).2 with h | h
  · rw [h]
    exact even_incomingNeg_of_odd _ ho
  · rw [h]
    exact even_incomingPos_of_odd _ ho

/-- Two steps advance the `x`-coordinate by one, whatever the parity. -/
theorem fan_x_two_steps {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S}
    (hnext : ∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1))
    (start : FanT F m S) (n : ℕ) :
    ((next^[n + 2] start).1).1 = ((next^[n] start).1).1 + 1 := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  by_cases he : EvenSite ((next^[n] start).1)
  · have hx1 := step_x_even hnext (next^[n] start) he
    have hodd := step_parity_even hnext (next^[n] start) he
    have hx2 := step_x_odd hnext (next (next^[n] start)) hodd
    rw [hx2, hx1]
  · have hx1 := step_x_odd hnext (next^[n] start) he
    have hev := step_parity_odd hnext (next^[n] start) he
    have hx2 := step_x_even hnext (next (next^[n] start)) hev
    rw [hx2, hx1]

/-- **The first exit of the fan** (ALL_SLOPE_STEP, the fan stops at its first boundary terminal): from a contact of the fort `S` the
fan path reaches a contact of `S` outside the strict interior, through strict-interior contacts only. -/
theorem fan_first_exit {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) :
    ∃ k : ℕ, (∃ next : FanT F m S → FanT F m S,
      (∀ v : FanT F m S, (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
        ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1)) ∧
      (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∈ S ∧ F (next^[k] ⟨v0, hv0S, hv0c⟩).1 = m (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧
      ¬ FLatticePaper.W1.StrictInterior n d (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧
      ∀ j < k, FLatticePaper.W1.StrictInterior n d (next^[j] ⟨v0, hv0S, hv0c⟩).1) := by
  obtain ⟨next, hnext⟩ := fan_path_exists hfort hm hme hle
  set start : FanT F m S := ⟨v0, hv0S, hv0c⟩ with hstart
  have hfin := FLatticePaper.W1Finite.strictInterior_finite n d hn hnd
  have hex : ∃ k : ℕ, ¬ FLatticePaper.W1.StrictInterior n d (next^[k] start).1 := by
    by_contra hall
    have hall2 : ∀ k : ℕ, FLatticePaper.W1.StrictInterior n d (next^[k] start).1 := fun k => by
      by_contra h
      exact hall ⟨k, h⟩
    obtain ⟨M, hM⟩ := (hfin.image Prod.fst).bddAbove
    -- the x-coordinate grows by one every two steps, so it is unbounded on the path
    have hgrow : ∀ k : ℕ, ((next^[2 * k] start).1).1 = v0.1 + k := by
      intro k
      induction k with
      | zero => simp [hstart]
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, fan_x_two_steps hnext start (2 * k), ih]
        push_cast
        ring
    have hk : (((M - v0.1).toNat + 1 : ℕ) : ℤ) = (M - v0.1).toNat + 1 := by push_cast; ring
    have hbound := hM ⟨(next^[2 * ((M - v0.1).toNat + 1)] start).1, hall2 _, rfl⟩
    rw [hgrow] at hbound
    have htoNat : ((M - v0.1).toNat : ℤ) ≥ M - v0.1 := Int.self_le_toNat _
    push_cast at hbound
    omega
  classical
  refine ⟨Nat.find hex, next, hnext, (next^[Nat.find hex] start).2.1, (next^[Nat.find hex] start).2.2,
    Nat.find_spec hex, fun j hj => ?_⟩
  have := Nat.find_min hex hj
  exact not_not.mp this

/-- **The fan contradiction** (FIXED_FREE §9): a true fort of `F` containing a fan contact, under the paid exclusion of every boundary
contact of `S` (the terminal's removal), is impossible. -/
theorem fan_paid_contradiction {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hle : ∀ x, m x ≤ F x) (n d : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0)
    (hpaid : ∀ v : Site, v ∈ S → F v = m v → ¬ FLatticePaper.W1.StrictInterior n d v → False) : False := by
  obtain ⟨k, next, _, hmem, hcon, hout, _⟩ := fan_first_exit hfort hm hme hle n d hn hnd v0 hv0S hv0c
  exact hpaid _ hmem hcon hout

end FLatticePaper.FanPropagation
