import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.CanonForced
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.FreeNonfree

/-! # Endpoint row arrows of the canonical policy (the disjunct form of the `RouteGenuine` row fields)

Each arrow is a prescription at a free white centre (`presc_atH`, `presc_atV`), or its deck translate (`shiftH_iff`, `shiftV_iff`),
so it is kept by the canonical policy `C` unless the centre is black (the disjunct `laplacian = −1`). The rows `rH0`, `rV1`, the first
`rH1` and the first `rVprev` arrow are proved here; the rest is recorded in the report. -/

namespace FLatticePaper.RouteRows

open FLatticePaper FLatticePaper.Induction FLatticePaper.EndpointRows

/-- **Row `H_0`**: `(0,1) → (0,0) → (1,0)` for `η = 1`; `(1,−1) → (0,−1) → (0,0) → (1,0)` for `η = −1`. -/
theorem rH0_fields {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hdU : ∀ x u, C.policy x u ↔ C.policy (x + Kdeck frame) (u + Kdeck frame))
    (hdV : ∀ x u, C.policy x u ↔ C.policy (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    (η = 1 → (laplacian G (0, 1) = -1 ∨ C.policy (0, 1) (0, 0)) ∧ (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0))) ∧
    (η = -1 → (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (0, -1)) ∧ (laplacian G (0, -1) = -1 ∨ C.policy (0, -1) (0, 0)) ∧
      (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0))) := by
  constructor
  · intro h
    subst h
    have r12 : C.policy (0, 1) (0, 0) :=
      (presc_atV C.prescribed F.fV01 F.w01 (prescV01 1) (0, 0)).mpr (by decide)
    have r20 : C.policy (0, 0) (1, 0) :=
      (presc_atV C.prescribed F.fV00 F.w00 (prescV00 1) (1, 0)).mpr (by decide)
    exact ⟨Or.inr r12, Or.inr r20⟩
  · intro h
    subst h
    have r01 : C.policy (1, -1) (0, -1) := (shiftV_iff hdV C.prescribed F (0, -1)).mpr (by decide)
    have r12 : C.policy (0, -1) (0, 0) := (shiftH_iff hdU C.prescribed F (0, 0)).mpr (by decide)
    have r20 : C.policy (0, 0) (1, 0) :=
      (presc_atV C.prescribed F.fV00 F.w00 (prescV00 (-1)) (1, 0)).mpr (by decide)
    exact ⟨Or.inr r01, Or.inr r12, Or.inr r20⟩

/-- **Row `V_1`, `η = −1`**: `(0,0) → (1,0) → (1,1)`, the second arrow the prescription at the free `H_0 = (1,0)`. -/
theorem rV1_fields {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (F : EndpointFacts frame G) :
    η = -1 → (laplacian G (0, 0) = -1 ∨ C.policy (0, 0) (1, 0)) ∧ (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, 1)) := by
  intro h
  subst h
  have hv : frame.prescribedH (-1) (1, 0) = (0, 1) := by
    have h : frame.prescribedH (-1) (1, 0) = (0, -(-1)) := frame.prescribedH_hFirst (-1)
    rw [h]
    decide
  have r20 : C.policy (0, 0) (1, 0) :=
    (presc_atV C.prescribed F.fV00 F.w00 (prescV00 (-1)) (1, 0)).mpr (by decide)
  have r01 : C.policy (1, 0) (1, 1) := (presc_atH C.prescribed F.fH10 F.w10 hv (1, 1)).mpr (by decide)
  exact ⟨Or.inr r20, Or.inr r01⟩

/-- **Row `H_1`, `η = 1`**: `(1,0) → (1,−1) → (2,−1)`, the first arrow the prescription at `H_0`, the second the deck translate. -/
theorem rH1_plus_fields {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hdV : ∀ x u, C.policy x u ↔ C.policy (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    η = 1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, -1)) ∧ (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1)) := by
  intro h
  subst h
  have hv : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
  have r01 : C.policy (1, 0) (1, -1) := (presc_atH C.prescribed F.fH10 F.w10 hv (1, -1)).mpr (by decide)
  have r12 : C.policy (1, -1) (2, -1) := (shiftV_iff hdV C.prescribed F (2, -1)).mpr (by decide)
  exact ⟨Or.inr r01, Or.inr r12⟩

/-- **Row `H_1`, `η = −1`, first arrow**: `(1,0) → (1,1)`, the prescription at `H_0`. -/
theorem rH1_minus_first {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (F : EndpointFacts frame G) :
    η = -1 → (laplacian G (1, 0) = -1 ∨ C.policy (1, 0) (1, 1)) := by
  intro h
  subst h
  have hv : frame.prescribedH (-1) (1, 0) = (0, 1) := by
    have h : frame.prescribedH (-1) (1, 0) = (0, -(-1)) := frame.prescribedH_hFirst (-1)
    rw [h]
    decide
  exact Or.inr ((presc_atH C.prescribed F.fH10 F.w10 hv (1, 1)).mpr (by decide))

/-- **Row `V_prev`, `η = 1`, first arrow**: `(1,−1) → (2,−1)`, the deck translate by `V`. -/
theorem rVprev_plus_first {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hdV : ∀ x u, C.policy x u ↔ C.policy (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    η = 1 → (laplacian G (1, -1) = -1 ∨ C.policy (1, -1) (2, -1)) := by
  intro h
  subst h
  exact Or.inr ((shiftV_iff hdV C.prescribed F (2, -1)).mpr (by decide))

/-- **Row `H_last`**: `(−1,−2) → (−1,−1)` (black, or white and nonfree, forced to its free input `(−1,−1)`), then
`(−1,−1) → (0,−1)` by the deck translate. The nonfreeness of `(−1,−2)` is a hypothesis (open, see the report). -/
theorem rHlast_fields {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hdU : ∀ x u, C.policy x u ↔ C.policy (x + Kdeck frame) (u + Kdeck frame))
    (F : EndpointFacts frame G) (hN : Nonfree frame (-1, -2)) :
    (laplacian G (-1, -2) = -1 ∨ C.policy (-1, -2) (-1, -1)) ∧ (laplacian G (-1, -1) = -1 ∨ C.policy (-1, -1) (0, -1)) := by
  have hfreeLL : ¬ Nonfree frame (-1, -1) := by
    apply translate_free (Kdeck_mem_span frame)
    have e : (-1, -1) + Kdeck frame = (frame.child.den - 1, frame.child.num - 1) := by
      rw [kdeck_eq]
      simp only [Prod.mk.injEq]
      constructor <;> ring
    rw [e]
    exact Set.mem_union_left _ F.fHP
  constructor
  · by_cases hb : laplacian G (-1, -2) = -1
    · exact Or.inl hb
    · have h0 : laplacian G (-1, -2) = 0 := (hbin _).resolve_left hb
      have hF : FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (-1, -2) (-1, -1) :=
        FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inr (by decide)) hfreeLL
      exact Or.inr (FLatticePaper.CanonForced.canon_of_forced C h0 hF)
  · exact Or.inr ((shiftHprev_iff hdU C.prescribed F (0, -1)).mpr (by decide))

/-- **Row `H_1`, `η = −1`, second arrow**: `(2,1) → (2,0)`, black, or white and nonfree, forced to its free input `(2,0)`. -/
theorem rH1_minus_second {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (F : EndpointFacts frame G) (hN : Nonfree frame (2, 1)) :
    laplacian G (2, 1) = -1 ∨ C.policy (2, 1) (2, 0) := by
  by_cases hb : laplacian G (2, 1) = -1
  · exact Or.inl hb
  · have h0 : laplacian G (2, 1) = 0 := (hbin _).resolve_left hb
    have hfreeH20 : ¬ Nonfree frame (2, 0) := by
      apply translate_free (zero_mem_span frame)
      rw [add_zero]
      exact Set.mem_union_left _ F.fH20
    have hF : FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (2, 1) (2, 0) :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inl (by decide)) hfreeH20
    exact Or.inr (FLatticePaper.CanonForced.canon_of_forced C h0 hF)

/-- **Row `V_prev`, `η = 1`, second arrow**: `(2,−2) → (1,−2)`, black, or white and nonfree, forced to its free input `(1,−2)`. -/
theorem rVprev_plus_second {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (F : EndpointFacts frame G) (hN : Nonfree frame (2, -2)) :
    laplacian G (2, -2) = -1 ∨ C.policy (2, -2) (1, -2) := by
  by_cases hb : laplacian G (2, -2) = -1
  · exact Or.inl hb
  · have h0 : laplacian G (2, -2) = 0 := (hbin _).resolve_left hb
    have hfreeVP : ¬ Nonfree frame (1, -2) := by
      apply translate_free (Vdeck_mem_span frame)
      have e : (1, -2) + Vdeck frame = (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
        rw [vdeck_eq]
        simp only [Prod.mk.injEq]
        constructor <;> ring
      rw [e]
      exact Set.mem_union_right _ F.fVP
    have hF : FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (2, -2) (1, -2) :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inl (by decide)) hfreeVP
    exact Or.inr (FLatticePaper.CanonForced.canon_of_forced C h0 hF)

/-- **Row `H_last`** with the nonfreeness of `(−1,−2)` proved (`FreeNonfree.nonfree_m12`). -/
theorem rHlast_fields' {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    (hdU : ∀ x u, C.policy x u ↔ C.policy (x + Kdeck frame) (u + Kdeck frame))
    (F : EndpointFacts frame G) :
    (laplacian G (-1, -2) = -1 ∨ C.policy (-1, -2) (-1, -1)) ∧ (laplacian G (-1, -1) = -1 ∨ C.policy (-1, -1) (0, -1)) :=
  rHlast_fields C hP hW1 hbin hdU F FLatticePaper.FreeNonfree.nonfree_m12

/-- **Row `H_1`, `η = −1`, second arrow** with the nonfreeness of `(2,1)` proved (`FreeNonfree.nonfree_21`). -/
theorem rH1_minus_second' {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (F : EndpointFacts frame G) :
    laplacian G (2, 1) = -1 ∨ C.policy (2, 1) (2, 0) :=
  rH1_minus_second C hP hW1 hbin F FLatticePaper.FreeNonfree.nonfree_21

/-- **Row `V_prev`, `η = 1`, second arrow** with the nonfreeness of `(2,−2)` proved (`FreeNonfree.nonfree_2m2`). -/
theorem rVprev_plus_second' {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hP : frame.Packet G) (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) (F : EndpointFacts frame G) :
    laplacian G (2, -2) = -1 ∨ C.policy (2, -2) (1, -2) :=
  rVprev_plus_second C hP hW1 hbin F FLatticePaper.FreeNonfree.nonfree_2m2

end FLatticePaper.RouteRows
