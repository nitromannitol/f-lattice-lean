import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.ReturnPrescribed
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.W1Witness
import FLatticePaper.Plane.Induction.W1NonfreeOut
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.CanonicalDirections
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.WestSelect
import FLatticePaper.Plane.Induction.DeckParentSquare

/-! # The endpoint table of the free boundary (Q32, the §D rows of ALL_WHITE_THREE_STEP_RETURNS)

Each row is a three-edge return `q0 → q1 → q2 → z` of a free endpoint `z`, written at the table's coordinates. The shifted endpoints
`(0,−1) = Hlast − U`, `(1,−1) = Vend − V`, `(−1,−1) = Hprev − U` and `(1,−2) = Vprev − V` are carried to the native points by the
deck equivariance of the policy (`hdU`, `hdV`). The colours and freeness of the finitely many sites of the table are collected in
`EndpointFacts`. -/

namespace FLatticePaper.EndpointRows

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut
  FLatticePaper.W1Witness FLatticePaper.ReturnPrescribed FLatticePaper.FanCompat FLatticePaper.AndOrRank Farey

/-- The colours and freeness of the endpoint table, at the table's coordinates and at the native endpoints. -/
structure EndpointFacts (frame : ChildFrame) (G : Field) : Prop where
  b11 : laplacian G (1, 1) = -1
  b0m2 : laplacian G (0, -2) = -1
  bm10 : laplacian G (-1, 0) = -1
  b2m1 : laplacian G (2, -1) = -1
  w10 : laplacian G (1, 0) = 0
  w00 : laplacian G (0, 0) = 0
  w01 : laplacian G (0, 1) = 0
  w20 : laplacian G (2, 0) = 0
  w0m1 : laplacian G (0, -1) = 0
  wm11 : laplacian G (-1, -1) = 0
  w1m1 : laplacian G (1, -1) = 0
  w1m2 : laplacian G (1, -2) = 0
  fH10 : (1, 0) ∈ frame.freeH
  fV00 : (0, 0) ∈ frame.freeV
  fV01 : (0, 1) ∈ frame.freeV
  fH20 : (2, 0) ∈ frame.freeH
  wHL : laplacian G frame.hLast = 0
  fHL : frame.hLast ∈ frame.freeH
  wHP : laplacian G (frame.child.den - 1, frame.child.num - 1) = 0
  fHP : (frame.child.den - 1, frame.child.num - 1) ∈ frame.freeH
  wVL : laplacian G frame.vLast = 0
  fVL : frame.vLast ∈ frame.freeV
  wVP : laplacian G (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) = 0
  fVP : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) ∈ frame.freeV

/-! ## Helpers -/

section Helpers

variable {frame : ChildFrame} {G : Field} {R : Site → Site → Prop}

/-- A deck-transported prescription: `R x j ↔ j = x + c` from the literal point `x + τ`. -/
theorem iff_of_deck {τ : Site} (hdeck : ∀ x u, R x u ↔ R (x + τ) (u + τ)) {x c : Site}
    (hx : ∀ j, R (x + τ) j ↔ j = (x + τ) + c) : ∀ j, R x j ↔ j = x + c := by
  intro j
  rw [hdeck x j, hx (j + τ)]
  rw [show x + τ + c = x + c + τ by abel]
  exact add_left_inj τ

/-- A literal free H point with its prescription value. -/
theorem presc_atH {η : ℤ} (hpres : PrescribedAt frame G η R) {p c : Site} (hp : p ∈ frame.freeH)
    (hl : laplacian G p = 0) (hc : frame.prescribedH η p = c) : ∀ j, R p j ↔ j = p + c := by
  intro j
  rw [hpres.1 p hp hl j, hc]

/-- A literal free V point with its prescription value. -/
theorem presc_atV {η : ℤ} (hpres : PrescribedAt frame G η R) {p c : Site} (hp : p ∈ frame.freeV)
    (hl : laplacian G p = 0) (hc : frame.prescribedV η p = c) : ∀ j, R p j ↔ j = p + c := by
  intro j
  rw [hpres.2 p hp hl j, hc]

/-- A translate of a free point is not nonfree. -/
theorem translate_free {p τ : Site} (hτ : τ ∈ frame.child.modifiedDeck.span)
    (h : p + τ ∈ frame.freeH ∪ frame.freeV) : ¬ Nonfree frame p :=
  fun hN => hN τ hτ h

/-- The native translates of the shifted endpoints. -/
theorem kdeck_eq (p : Site) : p + Kdeck frame = (p.1 + frame.child.den, p.2 + frame.child.num) := by
  unfold Kdeck
  rfl

theorem vdeck_eq (p : Site) : p + Vdeck frame = (p.1 + (frame.child.num - frame.child.den), p.2 + (frame.child.num + frame.child.den)) := by
  unfold Vdeck
  rfl

end Helpers

/-- The square lemma: the clauses of `ParentSquareOut`. -/
theorem parentSquareOut_of_square {G : Field} {R : Site → Site → Prop} {a b : ℤ} {z q0 q1 q2 o : Site}
    (hz : z ∈ squareCorners a b) (h0 : q0 ∈ squareCorners a b) (h1 : q1 ∈ squareCorners a b)
    (h2 : q2 ∈ squareCorners a b)
    (hcov : ∀ c' ∈ squareCorners a b, c' ≠ z → c' = q0 ∨ c' = q1 ∨ c' = q2)
    (d01 : q0 ≠ q1) (d12 : q1 ≠ q2) (d02 : q0 ≠ q2)
    (hin0 : q0 = incomingNeg z ∨ q0 = incomingPos z) (hn0 : ¬ R z q0)
    (e1 : Edge q1 q0) (e2 : Edge q2 q1) (e3 : Edge z q2)
    (r01 : R q0 q1) (r12 : R q1 q2) (r20 : R q2 z)
    (hout : o = incomingNeg z ∨ o = incomingPos z) (hosq : o ∉ squareCorners a b)
    (ro : R z o) (huq : ∀ j, R z j → j = o)
    (c0 : laplacian G q0 = -1 ∨ (laplacian G q0 = 0 ∧ ∀ j, R q0 j → j = q1))
    (c1 : laplacian G q1 = -1 ∨ (laplacian G q1 = 0 ∧ ∀ j, R q1 j → j = q2))
    (c2 : laplacian G q2 = -1 ∨ (laplacian G q2 = 0 ∧ ∀ j, R q2 j → j = z)) :
    ParentSquareOut G R z :=
  ⟨q0, q1, q2, o, a, b, hz, h0, h1, h2, hcov, d01, d12, d02, hin0, hn0, e1, e2, e3, r01, r12, r20, hout, hosq,
    ro, huq, c0, c1, c2⟩

/-- The white clause: a white point with its unique retained input. -/
theorem clause_white {G : Field} {R : Site → Site → Prop}
    (hwu : ∀ c j j', laplacian G c = 0 → R c j → R c j' → j = j')
    {c q : Site} (hc : laplacian G c = 0) (r : R c q) :
    laplacian G c = -1 ∨ (laplacian G c = 0 ∧ ∀ j, R c j → j = q) :=
  Or.inr ⟨hc, fun j hj => hwu c j q hc hj r⟩

/-! ## Shifted endpoints, carried to the native points by the deck -/

section Shifts

variable {frame : ChildFrame} {G : Field} {η : ℤ} {R : Site → Site → Prop}

/-- The shifted `Hlast`: `(0,−1) → (0,0)`. -/
theorem shiftH_iff (hdU : ∀ x u, R x u ↔ R (x + Kdeck frame) (u + Kdeck frame))
    (hpres : PrescribedAt frame G η R) (F : EndpointFacts frame G) :
    ∀ j, R (0, -1) j ↔ j = (0, -1) + (0, 1) := by
  apply iff_of_deck hdU
  have e : (0, -1) + Kdeck frame = frame.hLast := by
    rw [kdeck_eq]
    unfold ChildFrame.hLast
    simp only [Prod.mk.injEq]
    constructor <;> ring
  intro j
  rw [e]
  have hL : frame.prescribedH η frame.hLast = (0, 1) := by
    unfold ChildFrame.prescribedH
    obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
    have h1 : frame.hLast ≠ hFirst := by
      intro h
      have h1 := congrArg Prod.fst h
      unfold ChildFrame.hLast hFirst at h1
      simp only at h1
      omega
    rw [if_neg h1, if_pos rfl]
  exact presc_atH hpres F.fHL F.wHL hL j

/-- The shifted `Hprev`: `(−1,−1) → (0,−1)`. -/
theorem shiftHprev_iff (hdU : ∀ x u, R x u ↔ R (x + Kdeck frame) (u + Kdeck frame))
    (hpres : PrescribedAt frame G η R) (F : EndpointFacts frame G) :
    ∀ j, R (-1, -1) j ↔ j = (-1, -1) + (1, 0) := by
  apply iff_of_deck hdU
  have e : (-1, -1) + Kdeck frame = (frame.child.den - 1, frame.child.num - 1) := by
    rw [kdeck_eq]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  intro j
  rw [e]
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hev : EvenSite (frame.child.den - 1, frame.child.num - 1) := by
    unfold EvenSite
    simp only
    have : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    omega
  have h1 : (frame.child.den - 1, frame.child.num - 1) ≠ hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    unfold hFirst at h1
    simp only at h1
    omega
  have h2 : (frame.child.den - 1, frame.child.num - 1) ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    unfold ChildFrame.hLast at h1
    simp only at h1
    omega
  exact presc_atH hpres F.fHP F.wHP (prescribedH_even η hev h1 h2) j

end Shifts

/-! ## The rows of the table -/

/-- **Row H0, `η+`:** `(1,1) → (0,1) → (0,0) → (1,0)`. -/
theorem row_H0_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained) (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (1, 0) := by
  have r01 : W.retained (1, 1) (0, 1) := by
    have e : incomingNeg (1, 1) = (0, 1) := by decide
    have h := (W.quota.1 (1, 1) F.b11).1
    rw [e] at h
    exact h
  have r12 : W.retained (0, 1) (0, 0) := by
    have hv : frame.prescribedV 1 (0, 1) = (0, -1) := by
      apply FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame 1 (by decide)
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        unfold ChildFrame.vLast at h1 h2
        obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
        simp only at h1 h2
        omega
      · decide
    exact (presc_atV hpres F.fV01 F.w01 hv (0, 0)).mpr (by decide)
  have r20 : W.retained (0, 0) (1, 0) := by
    have hv : frame.prescribedV 1 (0, 0) = (1, 0) := frame.prescribedV_vFirst 1
    exact (presc_atV hpres F.fV00 F.w00 hv (1, 0)).mpr (by decide)
  have hn0 : ¬ W.retained (1, 0) (1, 1) := by
    intro h
    have hv : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
    have := (presc_atH hpres F.fH10 F.w10 hv (1, 1)).mp h
    exact absurd this (by decide)
  have ro : W.retained (1, 0) (1, -1) := by
    have hv : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
    exact (presc_atH hpres F.fH10 F.w10 hv (1, -1)).mpr (by decide)
  have huq : ∀ j, W.retained (1, 0) j → j = (1, -1) := by
    intro j hj
    have hv : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
    have := (presc_atH hpres F.fH10 F.w10 hv j).mp hj
    rw [this]
    decide
  exact parentSquareOut_of_square (a := 0) (b := 0) (z := (1, 0)) (q0 := (1, 1)) (q1 := (0, 1)) (q2 := (0, 0))
    (o := (1, -1)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (Or.inl F.b11) (clause_white hwu F.w01 r12) (clause_white hwu F.w00 r20)

/-- The zero vector is in the deck span. -/
theorem zero_mem_span (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [FLatticePaper.Farey.PeriodDeck.combine]⟩

/-- The shifted `Vend`: `(1,−1) → (2,−1)` for the sign `η` (the east prescription `(η,0)` of `Vend`). -/
theorem shiftV_iff {frame : ChildFrame} {G : Field} {η : ℤ} {R : Site → Site → Prop}
    (hdV : ∀ x u, R x u ↔ R (x + Vdeck frame) (u + Vdeck frame))
    (hpres : PrescribedAt frame G η R) (F : EndpointFacts frame G) :
    ∀ j, R (1, -1) j ↔ j = (1, -1) + (η, 0) := by
  apply iff_of_deck hdV
  have e : (1, -1) + Vdeck frame = frame.vLast := by
    rw [vdeck_eq]
    unfold ChildFrame.vLast
    simp only [Prod.mk.injEq]
    constructor <;> ring
  intro j
  rw [e]
  have hvL : frame.prescribedV η frame.vLast = (η, 0) := by
    unfold ChildFrame.prescribedV
    have h1 : frame.vLast ≠ FLatticePaper.Induction.vFirst := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      unfold ChildFrame.vLast FLatticePaper.Induction.vFirst at h1 h2
      obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
      simp only at h1 h2
      omega
    rw [if_neg h1, if_pos rfl]
  exact presc_atV hpres F.fVL F.wVL hvL j

/-- The shifted `Vprev`: `(1,−2) → (1,−1)` for the sign `η` (the south prescription `(0,−η)` of `Vprev`). -/
theorem shiftVprev_iff {frame : ChildFrame} {G : Field} {η : ℤ} {R : Site → Site → Prop}
    (hdV : ∀ x u, R x u ↔ R (x + Vdeck frame) (u + Vdeck frame))
    (hpres : PrescribedAt frame G η R) (F : EndpointFacts frame G) :
    ∀ j, R (1, -2) j ↔ j = (1, -2) + (0, -η) := by
  apply iff_of_deck hdV
  have e : (1, -2) + Vdeck frame = (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
    rw [vdeck_eq]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  intro j
  rw [e]
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hodd : ¬ EvenSite (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
    unfold EvenSite
    simp only
    omega
  have h1 : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) ≠
      FLatticePaper.Induction.vFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    unfold FLatticePaper.Induction.vFirst at h1
    simp only at h1
    omega
  have h2 : (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) ≠ frame.vLast := by
    intro h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.vLast at h2
    simp only at h2
    omega
  have hvp : frame.prescribedV η (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2)
      = (0, -η) := FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame η h1 h2 hodd
  exact presc_atV hpres F.fVP F.wVP hvp j

/-- **Row H0, `η−`:** `(1,−1) → (0,−1) → (0,0) → (1,0)`. -/
theorem row_H0_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed (-1))
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (1, 0) := by
  have hv : frame.prescribedH (-1) (1, 0) = (0, 1) := by
    have h : frame.prescribedH (-1) (1, 0) = (0, -(-1)) := frame.prescribedH_hFirst (-1)
    rw [h]
    decide
  have r01 : W.retained (1, -1) (0, -1) := (shiftV_iff hdV hpres F (0, -1)).mpr (by decide)
  have r12 : W.retained (0, -1) (0, 0) := (shiftH_iff hdU hpres F (0, 0)).mpr (by decide)
  have r20 : W.retained (0, 0) (1, 0) := by
    have hv0 : frame.prescribedV (-1) (0, 0) = (1, 0) := frame.prescribedV_vFirst (-1)
    exact (presc_atV hpres F.fV00 F.w00 hv0 (1, 0)).mpr (by decide)
  have hn0 : ¬ W.retained (1, 0) (1, -1) := by
    intro h
    have := (presc_atH hpres F.fH10 F.w10 hv (1, -1)).mp h
    exact absurd this (by decide)
  have ro : W.retained (1, 0) (1, 1) := (presc_atH hpres F.fH10 F.w10 hv (1, 1)).mpr (by decide)
  have huq : ∀ j, W.retained (1, 0) j → j = (1, 1) := fun j hj => by
    rw [(presc_atH hpres F.fH10 F.w10 hv j).mp hj]
    decide
  exact parentSquareOut_of_square (a := 0) (b := -1) (z := (1, 0)) (q0 := (1, -1)) (q1 := (0, -1)) (q2 := (0, 0))
    (o := (1, 1)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w1m1 r01) (clause_white hwu F.w0m1 r12) (clause_white hwu F.w00 r20)

/-- **Row Hlast (both signs):** `(0,−2) → (−1,−2) → (−1,−1) → (0,−1)`, the root the shifted `Hlast`. The arrow `(−1,−2) → (−1,−1)`
is the black rule or the forcing of a nonfree white to its free input `(−1,−1)`. -/
theorem row_Hlast {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed η)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G η W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (F : EndpointFacts frame G)
    (hsrc : laplacian G (-1, -2) = -1 ∨ (laplacian G (-1, -2) = 0 ∧ Nonfree frame (-1, -2))) :
    ParentSquareOut G W.retained (0, -1) := by
  have hfreeLL : ¬ Nonfree frame (-1, -1) := by
    apply translate_free (Kdeck_mem_span frame)
    have e : (-1, -1) + Kdeck frame = (frame.child.den - 1, frame.child.num - 1) := by
      rw [kdeck_eq]
      simp only [Prod.mk.injEq]
      constructor <;> ring
    rw [e]
    exact Set.mem_union_left _ F.fHP
  have r01 : W.retained (0, -2) (-1, -2) := by
    have e : incomingNeg (0, -2) = (-1, -2) := by decide
    have h := (W.quota.1 (0, -2) F.b0m2).1
    rw [e] at h
    exact h
  have r12 : W.retained (-1, -2) (-1, -1) := by
    rcases hsrc with h | ⟨h0, hN⟩
    · have e : incomingPos (-1, -2) = (-1, -1) := by decide
      have h2 := (W.quota.1 (-1, -2) h).2
      rw [e] at h2
      exact h2
    · have hF : ForcedEdge G (fun _ _ => False) (-1, -2) (-1, -1) :=
        FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inr (by decide)) hfreeLL
      exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have r20 : W.retained (-1, -1) (0, -1) := (shiftHprev_iff hdU hpres F (0, -1)).mpr (by decide)
  have hn0 : ¬ W.retained (0, -1) (0, -2) := by
    intro h
    have := (shiftH_iff hdU hpres F (0, -2)).mp h
    exact absurd this (by decide)
  have ro : W.retained (0, -1) (0, 0) := (shiftH_iff hdU hpres F (0, 0)).mpr (by decide)
  have huq : ∀ j, W.retained (0, -1) j → j = (0, 0) := fun j hj => (shiftH_iff hdU hpres F j).mp hj |>.trans (by decide)
  have c1 : laplacian G (-1, -2) = -1 ∨ (laplacian G (-1, -2) = 0 ∧ ∀ j, W.retained (-1, -2) j → j = (-1, -1)) := by
    rcases hsrc with h | ⟨h0, -⟩
    · exact Or.inl h
    · exact clause_white hwu h0 r12
  exact parentSquareOut_of_square (a := -1) (b := -2) (z := (0, -1)) (q0 := (0, -2)) (q1 := (-1, -2)) (q2 := (-1, -1))
    (o := (0, 0)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (Or.inl F.b0m2) c1 (clause_white hwu F.wm11 r20)

/-- The prescription of the free H point `(2,0)` is east, for both signs. -/
theorem prescH20 {frame : ChildFrame} (η : ℤ) : frame.prescribedH η (2, 0) = (1, 0) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  have h1 : (2, 0) ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have := congrArg Prod.fst h
    unfold FLatticePaper.Induction.hFirst at this
    simp only at this
    omega
  have h2 : (2, 0) ≠ frame.hLast := by
    intro h
    have := congrArg Prod.fst h
    unfold ChildFrame.hLast at this
    simp only at this
    omega
  exact prescribedH_even η (by decide) h1 h2

/-- The prescription of the free V point `(0,1)` is `(0,−η)` (it is not `vFirst` nor `vLast`). -/
theorem prescV01 {frame : ChildFrame} (η : ℤ) : frame.prescribedV η (0, 1) = (0, -η) := by
  obtain ⟨hn1, hnd, hdn, hd3, -⟩ := frame.child_facts
  apply FLatticePaper.Induction.CanonicalDirections.prescribedV_internal_odd frame η (by decide)
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    unfold ChildFrame.vLast at h1 h2
    simp only at h1 h2
    omega
  · decide

/-- The free V point `(0,0)` is `vFirst`, prescribed east. -/
theorem prescV00 {frame : ChildFrame} (η : ℤ) : frame.prescribedV η (0, 0) = (1, 0) :=
  frame.prescribedV_vFirst η

/-- **Row V0, both signs:** `(−1,0) → (−1,−1) → (0,−1) → (0,0)`, the root `V0 = (0,0)` retaining `(1,0)`. -/
theorem row_V0 {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (W : OldPolicyWitness frame G seed η)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G η W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (0, 0) := by
  have r01 : W.retained (-1, 0) (-1, -1) := by
    have e : incomingNeg (-1, 0) = (-1, -1) := by decide
    have h := (W.quota.1 (-1, 0) F.bm10).1
    rw [e] at h
    exact h
  have r12 : W.retained (-1, -1) (0, -1) := (shiftHprev_iff hdU hpres F (0, -1)).mpr (by decide)
  have r20 : W.retained (0, -1) (0, 0) := (shiftH_iff hdU hpres F (0, 0)).mpr (by decide)
  have hn0 : ¬ W.retained (0, 0) (-1, 0) := by
    intro h
    have hv0 : frame.prescribedV η (0, 0) = (1, 0) := prescV00 η
    have := (presc_atV hpres F.fV00 F.w00 hv0 (-1, 0)).mp h
    exact absurd this (by decide)
  have ro : W.retained (0, 0) (1, 0) := by
    have hv0 : frame.prescribedV η (0, 0) = (1, 0) := prescV00 η
    exact (presc_atV hpres F.fV00 F.w00 hv0 (1, 0)).mpr (by decide)
  have huq : ∀ j, W.retained (0, 0) j → j = (1, 0) := fun j hj => by
    have hv0 : frame.prescribedV η (0, 0) = (1, 0) := prescV00 η
    rw [(presc_atV hpres F.fV00 F.w00 hv0 j).mp hj]
    decide
  exact parentSquareOut_of_square (a := -1) (b := -1) (z := (0, 0)) (q0 := (-1, 0)) (q1 := (-1, -1)) (q2 := (0, -1))
    (o := (1, 0)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (Or.inl F.bm10) (clause_white hwu F.wm11 r12) (clause_white hwu F.w0m1 r20)

/-- **Row Vend, `η+`:** `(0,−1) → (0,0) → (1,0) → (1,−1)`, the root the shifted `Vend` retaining `(2,−1)`. -/
theorem row_Vend_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (1, -1) := by
  have r01 : W.retained (0, -1) (0, 0) := (shiftH_iff hdU hpres F (0, 0)).mpr (by decide)
  have r12 : W.retained (0, 0) (1, 0) := (presc_atV hpres F.fV00 F.w00 (prescV00 1) (1, 0)).mpr (by decide)
  have r20 : W.retained (1, 0) (1, -1) := by
    have hv : frame.prescribedH 1 (1, 0) = (0, -1) := by
      have h : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
      exact h
    exact (presc_atH hpres F.fH10 F.w10 hv (1, -1)).mpr (by decide)
  have hn0 : ¬ W.retained (1, -1) (0, -1) := by
    intro h
    have := (shiftV_iff hdV hpres F (0, -1)).mp h
    exact absurd this (by decide)
  have ro : W.retained (1, -1) (2, -1) := (shiftV_iff hdV hpres F (2, -1)).mpr (by decide)
  have huq : ∀ j, W.retained (1, -1) j → j = (2, -1) := fun j hj => (shiftV_iff hdV hpres F j).mp hj |>.trans (by decide)
  exact parentSquareOut_of_square (a := 0) (b := -1) (z := (1, -1)) (q0 := (0, -1)) (q1 := (0, 0)) (q2 := (1, 0))
    (o := (2, -1)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w0m1 r01) (clause_white hwu F.w00 r12) (clause_white hwu F.w10 r20)

/-- The arrow `(2,−2) → (1,−2)`: the black rule, or the forcing of the nonfree white `(2,−2)` to its free input `(1,−2)`. -/
theorem arrow_22 {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed η) (F : EndpointFacts frame G)
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2))) :
    W.retained (2, -2) (1, -2) := by
  have hfreeVP : ¬ Nonfree frame (1, -2) := by
    apply translate_free (Vdeck_mem_span frame)
    have e : (1, -2) + Vdeck frame = (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
      rw [vdeck_eq]
      simp only [Prod.mk.injEq]
      constructor <;> ring
    rw [e]
    exact Set.mem_union_right _ F.fVP
  rcases hsrc2 with h | ⟨h0, hN⟩
  · have e : incomingNeg (2, -2) = (1, -2) := by decide
    have h2 := (W.quota.1 (2, -2) h).1
    rw [e] at h2
    exact h2
  · have hF : ForcedEdge G (fun _ _ => False) (2, -2) (1, -2) :=
      FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inl (by decide)) hfreeVP
    exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)

/-- The colour clause of `(2,−2)` with its retained target `(1,−2)`. -/
theorem clause_22 {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (W : OldPolicyWitness frame G seed η)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2)))
    (r : W.retained (2, -2) (1, -2)) :
    laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ ∀ j, W.retained (2, -2) j → j = (1, -2)) := by
  rcases hsrc2 with h | ⟨h0, -⟩
  · exact Or.inl h
  · exact clause_white hwu h0 r

/-- **Row Vend, `η−`:** `(2,−1) → (2,−2) → (1,−2) → (1,−1)`, the root the shifted `Vend` retaining `(0,−1)`. -/
theorem row_Vend_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed (-1))
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G)
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2))) :
    ParentSquareOut G W.retained (1, -1) := by
  have r01 : W.retained (2, -1) (2, -2) := by
    have e : incomingNeg (2, -1) = (2, -2) := by decide
    have h := (W.quota.1 (2, -1) F.b2m1).1
    rw [e] at h
    exact h
  have r12 : W.retained (2, -2) (1, -2) := arrow_22 hP hW1 W F hsrc2
  have r20 : W.retained (1, -2) (1, -1) := (shiftVprev_iff hdV hpres F (1, -1)).mpr (by decide)
  have hn0 : ¬ W.retained (1, -1) (2, -1) := by
    intro h
    have := (shiftV_iff hdV hpres F (2, -1)).mp h
    exact absurd this (by decide)
  have ro : W.retained (1, -1) (0, -1) := (shiftV_iff hdV hpres F (0, -1)).mpr (by decide)
  have huq : ∀ j, W.retained (1, -1) j → j = (0, -1) := fun j hj => (shiftV_iff hdV hpres F j).mp hj |>.trans (by decide)
  exact parentSquareOut_of_square (a := 1) (b := -2) (z := (1, -1)) (q0 := (2, -1)) (q1 := (2, -2)) (q2 := (1, -2))
    (o := (0, -1)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (Or.inl F.b2m1) (clause_22 W hwu hsrc2 r12) (clause_white hwu F.w1m2 r20)

/-- **Row H1, `η+`:** `(1,0) → (1,−1) → (2,−1) → (2,0)`, the root `H1 = (2,0)` retaining `(3,0)`. -/
theorem row_H1_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (2, 0) := by
  have hv : frame.prescribedH 1 (1, 0) = (0, -1) := by
    have h : frame.prescribedH 1 (1, 0) = (0, -1) := frame.prescribedH_hFirst 1
    exact h
  have r01 : W.retained (1, 0) (1, -1) := (presc_atH hpres F.fH10 F.w10 hv (1, -1)).mpr (by decide)
  have r12 : W.retained (1, -1) (2, -1) := (shiftV_iff hdV hpres F (2, -1)).mpr (by decide)
  have r20 : W.retained (2, -1) (2, 0) := by
    have e := (W.quota.1 (2, -1) F.b2m1).2
    have e2 : incomingPos (2, -1) = (2, 0) := by decide
    rw [e2] at e
    exact e
  have hn0 : ¬ W.retained (2, 0) (1, 0) := by
    intro h
    have := (presc_atH hpres F.fH20 F.w20 (prescH20 1) (1, 0)).mp h
    exact absurd this (by decide)
  have ro : W.retained (2, 0) (3, 0) := (presc_atH hpres F.fH20 F.w20 (prescH20 1) (3, 0)).mpr (by decide)
  have huq : ∀ j, W.retained (2, 0) j → j = (3, 0) := fun j hj => (presc_atH hpres F.fH20 F.w20 (prescH20 1) j).mp hj |>.trans (by decide)
  exact parentSquareOut_of_square (a := 1) (b := -1) (z := (2, 0)) (q0 := (1, 0)) (q1 := (1, -1)) (q2 := (2, -1))
    (o := (3, 0)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w10 r01) (clause_white hwu F.w1m1 r12) (Or.inl F.b2m1)

/-- **Row H1, `η−`:** `(1,0) → (1,1) → (2,1) → (2,0)`, the root `H1 = (2,0)` retaining `(3,0)`. -/
theorem row_H1_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed (-1))
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G (-1) W.retained)
    (F : EndpointFacts frame G)
    (hsrc3 : laplacian G (2, 1) = -1 ∨ (laplacian G (2, 1) = 0 ∧ Nonfree frame (2, 1))) :
    ParentSquareOut G W.retained (2, 0) := by
  have hv : frame.prescribedH (-1) (1, 0) = (0, 1) := by
    have h : frame.prescribedH (-1) (1, 0) = (0, -(-1)) := frame.prescribedH_hFirst (-1)
    rw [h]
    decide
  have r01 : W.retained (1, 0) (1, 1) := (presc_atH hpres F.fH10 F.w10 hv (1, 1)).mpr (by decide)
  have r12 : W.retained (1, 1) (2, 1) := by
    have e := (W.quota.1 (1, 1) F.b11).2
    have e2 : incomingPos (1, 1) = (2, 1) := by decide
    rw [e2] at e
    exact e
  have hfreeH20 : ¬ Nonfree frame (2, 0) := by
    apply translate_free (zero_mem_span frame)
    rw [add_zero]
    exact Set.mem_union_left _ F.fH20
  have r20 : W.retained (2, 1) (2, 0) := by
    rcases hsrc3 with h | ⟨h0, hN⟩
    · have e := (W.quota.1 (2, 1) h).1
      have e2 : incomingNeg (2, 1) = (2, 0) := by decide
      rw [e2] at e
      exact e
    · have hF : ForcedEdge G (fun _ _ => False) (2, 1) (2, 0) :=
        FLatticePaper.ForcedArrows.forced_to_free_input hP hW1 hN h0 (Or.inl (by decide)) hfreeH20
      exact W.forcedRetained _ _ (FLatticePaper.WestSelect.forcedEdge_seed_mono hF)
  have hn0 : ¬ W.retained (2, 0) (1, 0) := by
    intro h
    have := (presc_atH hpres F.fH20 F.w20 (prescH20 (-1)) (1, 0)).mp h
    exact absurd this (by decide)
  have ro : W.retained (2, 0) (3, 0) := (presc_atH hpres F.fH20 F.w20 (prescH20 (-1)) (3, 0)).mpr (by decide)
  have huq : ∀ j, W.retained (2, 0) j → j = (3, 0) := fun j hj =>
    (presc_atH hpres F.fH20 F.w20 (prescH20 (-1)) j).mp hj |>.trans (by decide)
  have c2 : laplacian G (2, 1) = -1 ∨ (laplacian G (2, 1) = 0 ∧ ∀ j, W.retained (2, 1) j → j = (2, 0)) := by
    rcases hsrc3 with h | ⟨h0, -⟩
    · exact Or.inl h
    · exact clause_white hwu h0 r20
  exact parentSquareOut_of_square (a := 1) (b := 0) (z := (2, 0)) (q0 := (1, 0)) (q1 := (1, 1)) (q2 := (2, 1))
    (o := (3, 0)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w10 r01) (Or.inl F.b11) c2

/-- **Row V1, `η−`:** `(0,0) → (1,0) → (1,1) → (0,1)`, the root `V1 = (0,1)` retaining `(0,2)`. -/
theorem row_V1_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed (-1))
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G (-1) W.retained) (F : EndpointFacts frame G) :
    ParentSquareOut G W.retained (0, 1) := by
  have hv1 : frame.prescribedV (-1) (0, 1) = (0, -(-1)) := prescV01 (-1)
  have hn0 : ¬ W.retained (0, 1) (0, 0) := by
    intro h
    have := (presc_atV hpres F.fV01 F.w01 hv1 (0, 0)).mp h
    exact absurd this (by decide)
  have r01 : W.retained (0, 0) (1, 0) := (presc_atV hpres F.fV00 F.w00 (prescV00 (-1)) (1, 0)).mpr (by decide)
  have hv : frame.prescribedH (-1) (1, 0) = (0, 1) := by
    have h : frame.prescribedH (-1) (1, 0) = (0, -(-1)) := frame.prescribedH_hFirst (-1)
    rw [h]
    decide
  have r12 : W.retained (1, 0) (1, 1) := (presc_atH hpres F.fH10 F.w10 hv (1, 1)).mpr (by decide)
  have r20 : W.retained (1, 1) (0, 1) := by
    have e := (W.quota.1 (1, 1) F.b11).1
    have e2 : incomingNeg (1, 1) = (0, 1) := by decide
    rw [e2] at e
    exact e
  have ro : W.retained (0, 1) (0, 2) := (presc_atV hpres F.fV01 F.w01 hv1 (0, 2)).mpr (by decide)
  have huq : ∀ j, W.retained (0, 1) j → j = (0, 2) := fun j hj =>
    (presc_atV hpres F.fV01 F.w01 hv1 j).mp hj |>.trans (by decide)
  exact parentSquareOut_of_square (a := 0) (b := 0) (z := (0, 1)) (q0 := (0, 0)) (q1 := (1, 0)) (q2 := (1, 1))
    (o := (0, 2)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w00 r01) (clause_white hwu F.w10 r12) (Or.inl F.b11)

/-- **Row Vprev, `η+`:** `(1,−1) → (2,−1) → (2,−2) → (1,−2)`, the root the shifted `Vprev` retaining `(1,−3)`. -/
theorem row_Vprev_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G)
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2))) :
    ParentSquareOut G W.retained (1, -2) := by
  have hn0 : ¬ W.retained (1, -2) (1, -1) := by
    intro h
    have := (shiftVprev_iff hdV hpres F (1, -1)).mp h
    exact absurd this (by decide)
  have r01 : W.retained (1, -1) (2, -1) := (shiftV_iff hdV hpres F (2, -1)).mpr (by decide)
  have r12 : W.retained (2, -1) (2, -2) := by
    have e := (W.quota.1 (2, -1) F.b2m1).1
    have e2 : incomingNeg (2, -1) = (2, -2) := by decide
    rw [e2] at e
    exact e
  have r20 : W.retained (2, -2) (1, -2) := arrow_22 hP hW1 W F hsrc2
  have ro : W.retained (1, -2) (1, -3) := (shiftVprev_iff hdV hpres F (1, -3)).mpr (by decide)
  have huq : ∀ j, W.retained (1, -2) j → j = (1, -3) := fun j hj =>
    (shiftVprev_iff hdV hpres F j).mp hj |>.trans (by decide)
  exact parentSquareOut_of_square (a := 1) (b := -2) (z := (1, -2)) (q0 := (1, -1)) (q1 := (2, -1)) (q2 := (2, -2))
    (o := (1, -3)) (by decide) (by decide) (by decide) (by decide)
    (fun c' hc' hne => by
      revert c' hc' hne
      decide)
    (by decide) (by decide) (by decide)
    (by decide) hn0 (by unfold Edge; decide) (by unfold Edge; decide) (by unfold Edge; decide)
    r01 r12 r20 (by decide) (by decide) ro huq
    (clause_white hwu F.w1m1 r01) (Or.inl F.b2m1) (clause_22 W hwu hsrc2 r20)

/-- Negation keeps the even sites. -/
theorem evenSite_neg_of_even {x : Site} (h : EvenSite x) : EvenSite (-x) := by
  unfold EvenSite at *
  simp only [Prod.fst_neg, Prod.snd_neg]
  omega

/-- **Transport of a parent square along a deck vector** `τ` (even, in the span): the square at `z` gives the square at `z + τ`
when the policy is `τ`-equivariant and the laplacian is `τ`-invariant. -/
theorem parentSquareOut_shift {frame : ChildFrame} {G : Field} {R : Site → Site → Prop} (hP : frame.Packet G) {τ : Site}
    (hτ : EvenSite τ) (hτs : τ ∈ frame.child.modifiedDeck.span) (hR : ∀ x u, R x u ↔ R (x + τ) (u + τ))
    {z z' : Site} (e : z + τ = z') (h : ParentSquareOut G R z) : ParentSquareOut G R z' := by
  have hR' : ∀ x u, R x u ↔ R (x - -τ) (u - -τ) := fun x u => by
    rw [sub_neg_eq_add, sub_neg_eq_add]
    exact hR x u
  have hL' : ∀ w, laplacian G (w - -τ) = laplacian G w := fun w => by
    rw [sub_neg_eq_add]
    exact laplacian_span_inv frame G hP hτs w
  have h2 := FLatticePaper.DeckParentSquare.parentSquareOut_sub (τ := -τ) (evenSite_neg_of_even hτ) hR' hL' h
  rw [sub_neg_eq_add, e] at h2
  exact h2

/-- **The native last H root `hLast = (d, n−1)`**, from the shifted row `(0,−1)` by the kernel `Kdeck = (d,n)`. -/
theorem native_hLast {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed η)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G η W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (F : EndpointFacts frame G)
    (hsrc : laplacian G (-1, -2) = -1 ∨ (laplacian G (-1, -2) = 0 ∧ Nonfree frame (-1, -2))) :
    ParentSquareOut G W.retained frame.hLast := by
  have e : ((0 : ℤ), (-1 : ℤ)) + Kdeck frame = frame.hLast := by
    rw [kdeck_eq]
    unfold ChildFrame.hLast
    simp only [Prod.mk.injEq]
    constructor <;> ring
  exact parentSquareOut_shift hP (evenSite_Kdeck frame) (Kdeck_mem_span frame) hdU e
    (row_Hlast hP hW1 W hwu hpres hdU F hsrc)

/-- **The native last V root `vLast = (n−d+1, n+d−1)`** for `η = +1`, from the shifted row `(1,−1)` by `Vdeck`. -/
theorem native_vLast_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdU : ∀ x u, W.retained x u ↔ W.retained (x + Kdeck frame) (u + Kdeck frame))
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G) (hP : frame.Packet G) :
    ParentSquareOut G W.retained frame.vLast := by
  have e : ((1 : ℤ), (-1 : ℤ)) + Vdeck frame = frame.vLast := by
    rw [vdeck_eq]
    unfold ChildFrame.vLast
    simp only [Prod.mk.injEq]
    constructor <;> ring
  exact parentSquareOut_shift hP (evenSite_Vdeck frame) (Vdeck_mem_span frame) hdV e
    (row_Vend_plus W hwu hpres hdU hdV F)

/-- **The native last V root `vLast = (n−d+1, n+d−1)`** for `η = −1`, from the shifted row `(1,−1)` by `Vdeck`. -/
theorem native_vLast_minus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed (-1))
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G (-1) W.retained)
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G)
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2))) :
    ParentSquareOut G W.retained frame.vLast := by
  have e : ((1 : ℤ), (-1 : ℤ)) + Vdeck frame = frame.vLast := by
    rw [vdeck_eq]
    unfold ChildFrame.vLast
    simp only [Prod.mk.injEq]
    constructor <;> ring
  exact parentSquareOut_shift hP (evenSite_Vdeck frame) (Vdeck_mem_span frame) hdV e
    (row_Vend_minus hP hW1 W hwu hpres hdV F hsrc2)

/-- **The native V root `Vprev = (n−d+1, n+d−2)`** for `η = +1`, from the shifted row `(1,−2)` by `Vdeck`. -/
theorem native_vPrev_plus {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (hP : frame.Packet G)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (W : OldPolicyWitness frame G seed 1)
    (hwu : ∀ c j j', laplacian G c = 0 → W.retained c j → W.retained c j' → j = j')
    (hpres : PrescribedAt frame G 1 W.retained)
    (hdV : ∀ x u, W.retained x u ↔ W.retained (x + Vdeck frame) (u + Vdeck frame))
    (F : EndpointFacts frame G)
    (hsrc2 : laplacian G (2, -2) = -1 ∨ (laplacian G (2, -2) = 0 ∧ Nonfree frame (2, -2))) :
    ParentSquareOut G W.retained (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
  have e : ((1 : ℤ), (-2 : ℤ)) + Vdeck frame =
      (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 2) := by
    rw [vdeck_eq]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  exact parentSquareOut_shift hP (evenSite_Vdeck frame) (Vdeck_mem_span frame) hdV e
    (row_Vprev_plus hP hW1 W hwu hpres hdV F hsrc2)

end FLatticePaper.EndpointRows
