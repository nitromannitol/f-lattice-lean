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


/-- **Both inputs of an even contact of a true fort are contacts in the fort** (the zero horizontal deficit of the parabola). The window
bound `m ≤ F` is needed at the two inputs only. -/
theorem even_contact_both_fortAt {N : Site → Prop} {F m : Field} {S : Set Site} (hfort : FortAt N F S) {v : Site}
    (hN : N v) (hv : v ∈ S)
    (hc : F v = m v) (he : laplacian m v = 0) (h1 : m (incomingNeg v) ≤ F (incomingNeg v))
    (h2 : m (incomingPos v) ≤ F (incomingPos v)) :
    incomingNeg v ∈ S ∧ incomingPos v ∈ S ∧ F (incomingNeg v) = m (incomingNeg v) ∧
      F (incomingPos v) = m (incomingPos v) := by
  have hsum := excess_sum (F := F) (m := m) hc
  rcases hfort v hv hN with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · exfalso
    rw [hl, he] at hsum
    omega
  · rw [hl, he] at hsum
    refine ⟨hn, hp, ?_, ?_⟩
    · omega
    · omega

/-- **Both inputs of an even contact of a true fort are contacts in the fort** (the unrestricted fort). -/
theorem even_contact_both {F m : Field} {S : Set Site} (hfort : IsIncomingFort F S) {v : Site} (hv : v ∈ S)
    (hc : F v = m v) (he : laplacian m v = 0) (h1 : m (incomingNeg v) ≤ F (incomingNeg v))
    (h2 : m (incomingPos v) ≤ F (incomingPos v)) :
    incomingNeg v ∈ S ∧ incomingPos v ∈ S ∧ F (incomingNeg v) = m (incomingNeg v) ∧
      F (incomingPos v) = m (incomingPos v) :=
  even_contact_both_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) trivial hv hc he h1 h2

/-- The window bound `m ≤ F` at the inputs of every point satisfying the interior predicate `P` (the fan's interior). -/
def WindowOn (P : Site → Prop) (F m : Field) : Prop :=
  ∀ x, P x → ∀ i : Site, (i = incomingNeg x ∨ i = incomingPos x) → m i ≤ F i

/-- **One fan step**: from a contact of `S` at an interior point, the next point is a contact of `S`: the east input at an even contact,
a contacting input in `S` at an odd contact. -/
theorem fan_step_fortAt {N : Site → Prop} {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : FortAt N F S)
    (hPN : ∀ x, P x → N x)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) {v : Site} (hP : P v) (hv : v ∈ S) (hc : F v = m v) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ (EvenSite v → w = incomingPos v) ∧
      (w = incomingNeg v ∨ w = incomingPos v) := by
  have h1 := hwin v hP (incomingNeg v) (Or.inl rfl)
  have h2 := hwin v hP (incomingPos v) (Or.inr rfl)
  by_cases he : EvenSite v
  · obtain ⟨_, hp, _, ep⟩ := even_contact_both_fortAt hfort (hPN v hP) hv hc (hme v he) h1 h2
    exact ⟨incomingPos v, hp, ep, fun _ => rfl, Or.inr rfl⟩
  · obtain ⟨i, hi, hiS, hic⟩ := fort_contact_input_fortAt hfort hv (hPN v hP) hc hm h1 h2
    exact ⟨i, hiS, hic, fun h => absurd h he, hi⟩

/-- **One fan step** for the unrestricted fort. -/
theorem fan_step {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) {v : Site} (hP : P v) (hv : v ∈ S) (hc : F v = m v) :
    ∃ w : Site, w ∈ S ∧ F w = m w ∧ (EvenSite v → w = incomingPos v) ∧
      (w = incomingNeg v ∨ w = incomingPos v) :=
  fan_step_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) (fun _ _ => trivial) hm hme hwin hP hv hc

/-- The contacts of `S` for `F` and `m`. -/
abbrev FanT (F m : Field) (S : Set Site) : Type := {v : Site // v ∈ S ∧ F v = m v}

/-- The step rules of a fan at a point `v`. -/
def FanRules {F m : Field} {S : Set Site} (next : FanT F m S → FanT F m S) (v : FanT F m S) : Prop :=
  (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧ ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1)

/-- A fan step function obeying the rules at every interior point, from the one-step existence. -/
theorem fan_path_exists_fortAt {N : Site → Prop} {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : FortAt N F S)
    (hPN : ∀ x, P x → N x)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) :
    ∃ next : FanT F m S → FanT F m S, ∀ v : FanT F m S, P v.1 → FanRules next v := by
  have hex : ∀ v : FanT F m S, ∃ w : FanT F m S, (P v.1 → FanRules (fun _ => w) v) := by
    intro v
    by_cases hPv : P v.1
    · obtain ⟨w, hwS, hwc, hE, hI⟩ := fan_step_fortAt hfort hPN hm hme hwin hPv v.2.1 v.2.2
      exact ⟨⟨w, hwS, hwc⟩, fun _ => ⟨hE, hI⟩⟩
    · exact ⟨v, fun h => absurd h hPv⟩
  choose next hnext using hex
  exact ⟨fun v => next v, fun v hPv => hnext v hPv⟩

/-- A fan step function obeying the rules at every interior point (the unrestricted fort). -/
theorem fan_path_exists {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) :
    ∃ next : FanT F m S → FanT F m S, ∀ v : FanT F m S, P v.1 → FanRules next v :=
  fan_path_exists_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) (fun _ _ => trivial) hm hme hwin

/-- A step function from a contact of `S` at the start, with the north input at an odd start: the override keeps the rules. -/
theorem fan_path_exists_north_fortAt {N : Site → Prop} {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : FortAt N F S)
    (hPN : ∀ x, P x → N x)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) (hodd : ¬ EvenSite v0)
    (hnS : incomingPos v0 ∈ S) (hnc : F (incomingPos v0) = m (incomingPos v0)) :
    ∃ next : FanT F m S → FanT F m S, (∀ v : FanT F m S, P v.1 → FanRules next v) ∧
      (next ⟨v0, hv0S, hv0c⟩).1 = incomingPos v0 := by
  classical
  obtain ⟨next, hnext⟩ := fan_path_exists_fortAt hfort hPN hm hme hwin
  let start : FanT F m S := ⟨v0, hv0S, hv0c⟩
  let north : FanT F m S := ⟨incomingPos v0, hnS, hnc⟩
  refine ⟨fun v => if v = start then north else next v, fun v hPv => ?_, ?_⟩
  · by_cases hvs : v = start
    · rw [hvs]
      dsimp only [FanRules]
      rw [if_pos rfl]
      exact ⟨fun h => absurd h hodd, Or.inr rfl⟩
    · dsimp only [FanRules]
      rw [if_neg hvs]
      exact hnext v hPv
  · show (if start = start then north else next start).1 = incomingPos v0
    rw [if_pos rfl]

/-- The north-start step function (the unrestricted fort). -/
theorem fan_path_exists_north {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) (hodd : ¬ EvenSite v0)
    (hnS : incomingPos v0 ∈ S) (hnc : F (incomingPos v0) = m (incomingPos v0)) :
    ∃ next : FanT F m S → FanT F m S, (∀ v : FanT F m S, P v.1 → FanRules next v) ∧
      (next ⟨v0, hv0S, hv0c⟩).1 = incomingPos v0 :=
  fan_path_exists_north_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) (fun _ _ => trivial) hm hme hwin v0 hv0S hv0c
    hodd hnS hnc

/-- The step rules at a point, read from the fan's rules. -/
theorem rules_of_fanRules {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) : (EvenSite v.1 → (next v).1 = incomingPos v.1) ∧
      ((next v).1 = incomingNeg v.1 ∨ (next v).1 = incomingPos v.1) := h

theorem step_x_even {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) (he : EvenSite v.1) : (next v).1.1 = v.1.1 + 1 := by
  rw [h.1 he, incomingPos_of_even _ he]

theorem step_x_odd {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) (ho : ¬ EvenSite v.1) : (next v).1.1 = v.1.1 := by
  rcases h.2 with h' | h'
  · rw [h', incomingNeg_of_odd _ ho]
  · rw [h', incomingPos_of_odd _ ho]

theorem step_parity_even {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) (he : EvenSite v.1) : ¬ EvenSite (next v).1 := by
  rw [h.1 he]
  exact not_even_incomingPos_of_even _ he

theorem step_parity_odd {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} {v : FanT F m S}
    (h : FanRules next v) (ho : ¬ EvenSite v.1) : EvenSite (next v).1 := by
  rcases h.2 with h' | h'
  · rw [h']
    exact even_incomingNeg_of_odd _ ho
  · rw [h']
    exact even_incomingPos_of_odd _ ho

/-- Two steps advance the `x`-coordinate by one, when the rules hold along the path. -/
theorem fan_x_two_steps {F m : Field} {S : Set Site} {next : FanT F m S → FanT F m S} (start : FanT F m S) (n : ℕ)
    (hr : ∀ k : ℕ, FanRules next (next^[k] start)) :
    ((next^[n + 2] start).1).1 = ((next^[n] start).1).1 + 1 := by
  have e1 : next^[n + 1] start = next (next^[n] start) := Function.iterate_succ_apply' next n start
  have e2 : next^[n + 2] start = next (next^[n + 1] start) := Function.iterate_succ_apply' next (n + 1) start
  by_cases he : EvenSite ((next^[n] start).1)
  · have hx1 : ((next^[n + 1] start).1).1 = ((next^[n] start).1).1 + 1 := by
      rw [e1]
      exact step_x_even (hr n) he
    have hodd : ¬ EvenSite ((next^[n + 1] start).1) := by
      rw [e1]
      exact step_parity_even (hr n) he
    have hx2 := step_x_odd (hr (n + 1)) hodd
    rw [e2, hx2, hx1]
  · have hx1 : ((next^[n + 1] start).1).1 = ((next^[n] start).1).1 := by
      rw [e1]
      exact step_x_odd (hr n) he
    have hev : EvenSite ((next^[n + 1] start).1) := by
      rw [e1]
      exact step_parity_odd (hr n) he
    have hx2 := step_x_even (hr (n + 1)) hev
    rw [e2, hx2, hx1]

/-- **The first exit of a fan** (ALL_SLOPE_STEP, the fan stops at its first boundary terminal), for any step function obeying the rules at
the interior points `P`, when the interior is finite: a contact of `S` outside `P`, reached through interior contacts. -/
theorem fan_first_exit_of {F m : Field} {S : Set Site} {P : Site → Prop} (next : FanT F m S → FanT F m S)
    (hr : ∀ v : FanT F m S, P v.1 → FanRules next v) (hfinP : {c | P c}.Finite) (start : FanT F m S) :
    ∃ k : ℕ, ¬ P (next^[k] start).1 ∧ ∀ j < k, P (next^[j] start).1 := by
  have hex : ∃ k : ℕ, ¬ P (next^[k] start).1 := by
    by_contra hall
    have hall2 : ∀ k : ℕ, P (next^[k] start).1 := fun k => by
      by_contra h
      exact hall ⟨k, h⟩
    have hrk : ∀ k : ℕ, FanRules next (next^[k] start) := fun k => hr _ (hall2 k)
    obtain ⟨M, hM⟩ := (hfinP.image Prod.fst).bddAbove
    have hgrow : ∀ k : ℕ, ((next^[2 * k] start).1).1 = start.1.1 + k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, fan_x_two_steps start (2 * k) hrk, ih]
        push_cast
        ring
    have hbound := hM ⟨(next^[2 * ((M - start.1.1).toNat + 1)] start).1, hall2 _, rfl⟩
    rw [hgrow] at hbound
    have htoNat : ((M - start.1.1).toNat : ℤ) ≥ M - start.1.1 := Int.self_le_toNat _
    push_cast at hbound
    omega
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_⟩
  exact not_not.mp (Nat.find_min hex hj)

/-- **The first exit of a fan from a contact of a fort** (existence of the step function). -/
theorem fan_first_exit_fortAt {N : Site → Prop} {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : FortAt N F S)
    (hPN : ∀ x, P x → N x)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) (hfinP : {c | P c}.Finite) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) :
    ∃ k : ℕ, (∃ next : FanT F m S → FanT F m S, (∀ v : FanT F m S, P v.1 → FanRules next v) ∧
      (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∈ S ∧ F (next^[k] ⟨v0, hv0S, hv0c⟩).1 = m (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧
      ¬ P (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧ ∀ j < k, P (next^[j] ⟨v0, hv0S, hv0c⟩).1) := by
  obtain ⟨next, hr⟩ := fan_path_exists_fortAt hfort hPN hm hme hwin
  obtain ⟨k, hk, hj⟩ := fan_first_exit_of next hr hfinP ⟨v0, hv0S, hv0c⟩
  exact ⟨k, next, hr, (next^[k] ⟨v0, hv0S, hv0c⟩).2.1, (next^[k] ⟨v0, hv0S, hv0c⟩).2.2, hk, hj⟩

/-- **The first exit of a fan from a contact of a fort** (the unrestricted fort). -/
theorem fan_first_exit {F m : Field} {S : Set Site} {P : Site → Prop} (hfort : IsIncomingFort F S)
    (hm : ∀ x, laplacian m x = -1 ∨ laplacian m x = 0) (hme : ∀ x, EvenSite x → laplacian m x = 0)
    (hwin : WindowOn P F m) (hfinP : {c | P c}.Finite) (v0 : Site) (hv0S : v0 ∈ S) (hv0c : F v0 = m v0) :
    ∃ k : ℕ, (∃ next : FanT F m S → FanT F m S, (∀ v : FanT F m S, P v.1 → FanRules next v) ∧
      (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∈ S ∧ F (next^[k] ⟨v0, hv0S, hv0c⟩).1 = m (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧
      ¬ P (next^[k] ⟨v0, hv0S, hv0c⟩).1 ∧ ∀ j < k, P (next^[j] ⟨v0, hv0S, hv0c⟩).1) :=
  fan_first_exit_fortAt (N := fun _ => True) (fortAt_of_incoming hfort) (fun _ _ => trivial) hm hme hwin hfinP v0 hv0S hv0c

end FLatticePaper.FanPropagation
