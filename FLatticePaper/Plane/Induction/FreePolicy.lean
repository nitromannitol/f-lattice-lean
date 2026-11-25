import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.DeckSelection
import FLatticePaper.Plane.Induction.CanonicalSigned

/-! hgames, the policy with the free prescription built in (Q1: at a free white the signed H/V direction is prescribed).

For a rank `R` (with deck characters) and a sign `η = ±1`, `freePolicy` keeps, at a black centre, both inputs; at a white centre `c` in the
deck closure `freeClosure`, the prescribed input of its free representative `c + t` (`Presc`, transported by `−t`); at any other white
centre, the selection `selectR R`.

The prescription is well defined on the closure because the free set meets each deck orbit at most once (`FreeOrbit`): the witness `t` is
unique, so `Presc` is a single input. Its span covariance is the reindexing `t ↦ s + t`. -/

namespace FLatticePaper.FreePolicy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.DeckSelection FLatticePaper.FreeClosure FLatticePaper.FreeOrbit
open FLatticePaper.SquareClauses

/-- The prescribed input of the closure: `i = c + prescribed(c + t)` at a free representative `c + t`, `t` in the span. -/
def FreePresc (frame : ChildFrame) (η : ℤ) (c i : Site) : Prop :=
  ∃ t ∈ frame.child.modifiedDeck.span,
    (c + t ∈ frame.freeH ∧ i = c + frame.prescribedH η (c + t)) ∨
      (c + t ∈ frame.freeV ∧ i = c + frame.prescribedV η (c + t))

/-- The policy of a rank `R` with the free prescription. -/
def freePolicy (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) : Site → Site → Prop :=
  fun c i => (laplacian F c = -1 ∧ Edge i c) ∨
    (laplacian F c = 0 ∧
      ((freeClosure frame c ∧ FreePresc frame η c i) ∨ (¬ freeClosure frame c ∧ i = selectR R c)))

theorem zero_span_mem (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩

theorem span_even (frame : ChildFrame) {t : Site} (ht : t ∈ frame.child.modifiedDeck.span) : EvenSite t := by
  obtain ⟨i, j, rfl⟩ := ht
  rw [combine_eq frame i j]
  exact evenSite_span frame i j

theorem inNeg_even {r : Site} (h : EvenSite r) : incomingNeg r = (r.1 - 1, r.2) := by
  unfold incomingNeg
  rw [if_pos h]

theorem inPos_even {r : Site} (h : EvenSite r) : incomingPos r = (r.1 + 1, r.2) := by
  unfold incomingPos
  rw [if_pos h]

theorem inNeg_odd {r : Site} (h : ¬ EvenSite r) : incomingNeg r = (r.1, r.2 - 1) := by
  unfold incomingNeg
  rw [if_neg h]

theorem inPos_odd {r : Site} (h : ¬ EvenSite r) : incomingPos r = (r.1, r.2 + 1) := by
  unfold incomingPos
  rw [if_neg h]

theorem pH_even (frame : ChildFrame) (η : ℤ) {r : Site} (he : EvenSite r) : frame.prescribedH η r = (1, 0) := by
  have h1 : r ≠ hFirst := by
    rintro rfl
    exact absurd he (by unfold EvenSite hFirst; norm_num)
  have h2 : r ≠ frame.hLast := by
    obtain ⟨hco1, hco2⟩ := frame.child_odd
    rintro rfl
    dsimp only [EvenSite, ChildFrame.hLast] at he
    omega
  unfold ChildFrame.prescribedH
  rw [if_neg h1, if_neg h2, if_pos he]

theorem pH_odd (frame : ChildFrame) (η : ℤ) {r : Site} (h1 : r = hFirst) :
    frame.prescribedH η r = (0, -η) := by
  unfold ChildFrame.prescribedH
  rw [if_pos h1]

theorem pH_odd' (frame : ChildFrame) (η : ℤ) {r : Site} (ho : ¬ EvenSite r) (h1 : r ≠ hFirst) :
    frame.prescribedH η r = (0, 1) := by
  unfold ChildFrame.prescribedH
  rw [if_neg h1]
  by_cases h2 : r = frame.hLast
  · rw [if_pos h2]
  · rw [if_neg h2, if_neg ho]

/-- The prescribed H direction is an incoming edge of its centre. -/
theorem prescribedH_input (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1) (r : Site) :
    r + frame.prescribedH η r = incomingNeg r ∨ r + frame.prescribedH η r = incomingPos r := by
  by_cases he : EvenSite r
  · rw [pH_even frame η he, inPos_even he]
    right
    ext <;> simp
  · by_cases h1 : r = hFirst
    · rw [pH_odd frame η h1, inNeg_odd he, inPos_odd he]
      subst h1
      rcases hη with rfl | rfl
      · left
        ext <;> simp [hFirst]
      · right
        ext <;> simp [hFirst]
    · rw [pH_odd' frame η he h1, inPos_odd he]
      right
      ext <;> simp

theorem pV_even (frame : ChildFrame) (η : ℤ) {r : Site} (he : EvenSite r) :
    frame.prescribedV η r = if r = vFirst then (1, 0) else (η, 0) := by
  unfold ChildFrame.prescribedV
  by_cases h1 : r = vFirst
  · simp [h1]
  · by_cases h2 : r = frame.vLast
    · simp [h2]
    · simp [h2, he]

theorem pV_odd (frame : ChildFrame) (η : ℤ) {r : Site} (ho : ¬ EvenSite r) : frame.prescribedV η r = (0, -η) := by
  have hv1 : r ≠ vFirst := by
    rintro rfl
    exact ho (by unfold EvenSite vFirst; norm_num)
  have hv2 : r ≠ frame.vLast := by
    obtain ⟨hco1, hco2⟩ := frame.child_odd
    rintro rfl
    dsimp only [EvenSite, ChildFrame.vLast] at ho
    omega
  unfold ChildFrame.prescribedV
  rw [if_neg hv1, if_neg hv2, if_neg ho]

/-- The prescribed V direction is an incoming edge of its centre. -/
theorem prescribedV_input (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1) (r : Site) :
    r + frame.prescribedV η r = incomingNeg r ∨ r + frame.prescribedV η r = incomingPos r := by
  by_cases he : EvenSite r
  · rw [pV_even frame η he, inNeg_even he, inPos_even he]
    by_cases h1 : r = vFirst
    · rw [if_pos h1]
      right
      subst h1
      ext <;> simp [vFirst]
    · rw [if_neg h1]
      rcases hη with rfl | rfl
      · right
        ext <;> simp
      · left
        ext
        · simp; ring
        · simp
  · rw [pV_odd frame η he, inNeg_odd he, inPos_odd he]
    rcases hη with rfl | rfl
    · left
      ext
      · simp
      · simp; ring
    · right
      ext <;> simp

/-- Adding an even span vector to the centre and the input preserves the input relation. -/
theorem inp_shift {c t p : Site} (hev : EvenSite t)
    (h : c + t + p = incomingNeg (c + t) ∨ c + t + p = incomingPos (c + t)) :
    c + p = incomingNeg c ∨ c + p = incomingPos c := by
  rw [incomingNeg_add_even hev, incomingPos_add_even hev] at h
  rcases h with h | h
  · left
    apply add_right_cancel (b := t)
    rw [show c + p + t = c + t + p by abel]
    exact h
  · right
    apply add_right_cancel (b := t)
    rw [show c + p + t = c + t + p by abel]
    exact h

theorem freePresc_input (frame : ChildFrame) (η : ℤ) (hη : η = 1 ∨ η = -1) {c i : Site}
    (h : FreePresc frame η c i) : Edge i c := by
  obtain ⟨t, ht, h⟩ := h
  have hev := span_even frame ht
  unfold Edge
  rcases h with ⟨-, hi⟩ | ⟨-, hi⟩
  · rw [hi]
    exact inp_shift hev (prescribedH_input frame η hη (c + t))
  · rw [hi]
    exact inp_shift hev (prescribedV_input frame η hη (c + t))

/-- At a free H centre the prescription is exactly the H direction at the centre (the representative is the centre). -/
theorem freePresc_iff_H (frame : ChildFrame) (η : ℤ) {c : Site} (hc : c ∈ frame.freeH) (i : Site) :
    FreePresc frame η c i ↔ i = c + frame.prescribedH η c := by
  constructor
  · rintro ⟨t, ht, h⟩
    rcases h with ⟨hb, hi⟩ | ⟨hb, -⟩
    · have ht0 := freeH_rep_zero frame ht hc hb
      subst ht0
      simpa using hi
    · exact absurd hb (freeH_not_freeV_shift frame ht hc)
  · intro hi
    exact ⟨0, zero_span_mem frame, Or.inl ⟨by simpa using hc, by simpa using hi⟩⟩

theorem freePresc_iff_V (frame : ChildFrame) (η : ℤ) {c : Site} (hc : c ∈ frame.freeV) (i : Site) :
    FreePresc frame η c i ↔ i = c + frame.prescribedV η c := by
  constructor
  · rintro ⟨t, ht, h⟩
    rcases h with ⟨hb, -⟩ | ⟨hb, hi⟩
    · exact absurd hb (freeV_not_freeH_shift frame ht hc)
    · have ht0 := freeV_rep_zero frame ht hc hb
      subst ht0
      simpa using hi
  · intro hi
    exact ⟨0, zero_span_mem frame, Or.inr ⟨by simpa using hc, by simpa using hi⟩⟩

/-- At a closure centre the prescription is a single input. -/
theorem freePresc_single (frame : ChildFrame) (η : ℤ) {c i j : Site}
    (hi : FreePresc frame η c i) (hj : FreePresc frame η c j) : i = j := by
  obtain ⟨t, ht, hi⟩ := hi
  obtain ⟨t', ht', hj⟩ := hj
  have hsp : t' - t ∈ frame.child.modifiedDeck.span := span_sub ht' ht
  have e : c + t + (t' - t) = c + t' := by abel
  rcases hi with ⟨hH, hi⟩ | ⟨hV, hi⟩ <;> rcases hj with ⟨hH', hj⟩ | ⟨hV', hj⟩
  · have h0 : t' - t = 0 := by
      have := freeH_rep_zero frame hsp hH (by rw [e]; exact hH')
      exact this
    have htt : t' = t := sub_eq_zero.mp h0
    subst htt
    rw [hi, hj]
  · have hc' : c + t' ∈ frame.freeV := hV'
    rw [← e] at hc'
    exact absurd hc' (freeH_not_freeV_shift frame hsp hH)
  · have hc' : c + t' ∈ frame.freeH := hH'
    rw [← e] at hc'
    exact absurd hc' (freeV_not_freeH_shift frame hsp hV)
  · have h0 : t' - t = 0 := by
      have := freeV_rep_zero frame hsp hV (by rw [e]; exact hV')
      exact this
    have htt : t' = t := sub_eq_zero.mp h0
    subst htt
    rw [hi, hj]

theorem freePresc_exists (frame : ChildFrame) (η : ℤ) {c : Site} (hc : freeClosure frame c) :
    ∃ i, FreePresc frame η c i := by
  obtain ⟨s, hs, h⟩ := hc
  rcases h with h | h
  · exact ⟨c + frame.prescribedH η (c + s), s, hs, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨c + frame.prescribedV η (c + s), s, hs, Or.inr ⟨h, rfl⟩⟩

/-- The prescription is equivariant under the span: the witness is reindexed by `t ↦ s + t`. -/
theorem freePresc_add_span (frame : ChildFrame) (η : ℤ) {s : Site} (hs : s ∈ frame.child.modifiedDeck.span) (z u : Site) :
    FreePresc frame η (z + s) (u + s) ↔ FreePresc frame η z u := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨s + t, span_add hs ht, ?_⟩
    rw [← add_assoc]
    rcases h with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · left
      refine ⟨hH, ?_⟩
      apply add_right_cancel (b := s)
      rw [hi]
      abel
    · right
      refine ⟨hV, ?_⟩
      apply add_right_cancel (b := s)
      rw [hi]
      abel
  · rintro ⟨t, ht, h⟩
    refine ⟨t - s, span_sub ht hs, ?_⟩
    have e : z + s + (t - s) = z + t := by abel
    rw [e]
    rcases h with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · left
      refine ⟨hH, ?_⟩
      rw [hi]
      abel
    · right
      refine ⟨hV, ?_⟩
      rw [hi]
      abel

theorem freePolicy_closure_iff {frame : ChildFrame} {F : Field} {η : ℤ} {R : Site → ℤ} {c i : Site}
    (hl : laplacian F c = 0) (hc : freeClosure frame c) :
    freePolicy frame F η R c i ↔ FreePresc frame η c i := by
  unfold freePolicy
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ⟨-, h⟩ | ⟨hn, -⟩⟩)
    · exact absurd (hl.symm.trans h) (by norm_num)
    · exact h
    · exact absurd hc hn
  · intro h
    exact Or.inr ⟨hl, Or.inl ⟨hc, h⟩⟩

theorem freePolicy_out_iff {frame : ChildFrame} {F : Field} {η : ℤ} {R : Site → ℤ} {c i : Site}
    (hl : laplacian F c = 0) (hn : ¬ freeClosure frame c) :
    freePolicy frame F η R c i ↔ i = selectR R c := by
  unfold freePolicy
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ⟨hc, -⟩ | ⟨-, h⟩⟩)
    · exact absurd (hl.symm.trans h) (by norm_num)
    · exact absurd hc hn
    · exact h
  · intro h
    exact Or.inr ⟨hl, Or.inr ⟨hn, h⟩⟩

/-- The policy is equivariant under a span translate (the Laplacian, the closure, the prescription and the selection all shift). -/
theorem freePolicy_add_span (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    {η : ℤ} {R : Site → ℤ} {cRU cRV : ℤ}
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cRU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cRV) (i j : ℤ) (z u : Site) :
    freePolicy frame F η R (z + frame.child.modifiedDeck.combine i j) (u + frame.child.modifiedDeck.combine i j) ↔
      freePolicy frame F η R z u := by
  have hev : EvenSite (frame.child.modifiedDeck.combine i j) := span_even frame ⟨i, j, rfl⟩
  have hlap : laplacian F (z + frame.child.modifiedDeck.combine i j) = laplacian F z := by
    rw [combine_eq frame i j]
    exact laplacian_add_span frame hF i j z
  have hEdge : Edge (u + frame.child.modifiedDeck.combine i j) (z + frame.child.modifiedDeck.combine i j) ↔ Edge u z := by
    unfold Edge
    rw [incomingNeg_add_even hev, incomingPos_add_even hev]
    simp
  have hcl : freeClosure frame (z + frame.child.modifiedDeck.combine i j) ↔ freeClosure frame z :=
    freeClosure_add_span frame ⟨i, j, rfl⟩ z
  have hPr := freePresc_add_span frame η (⟨i, j, rfl⟩ : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span) z u
  have hSel : (u + frame.child.modifiedDeck.combine i j = selectR R (z + frame.child.modifiedDeck.combine i j)) ↔
      (u = selectR R z) := by
    rw [combine_eq frame i j, selectR_add_span frame hRU hRV i j z]
    simp
  unfold freePolicy
  simp only [hlap, hEdge, hcl, hPr, hSel]

/-- The deck form: the policy is invariant under every deck translate `−(iU + jV)`. -/
theorem freePolicy_deck (frame : ChildFrame) {F : Field} {cU cV : ℤ} (hF : HasGeneratorPeriods frame.child F cU cV)
    {η : ℤ} {R : Site → ℤ} {cRU cRV : ℤ}
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cRU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cRV) (i j : ℤ) (z u : Site)
    (h : freePolicy frame F η R z u) :
    freePolicy frame F η R (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j) := by
  have e : ∀ x : Site, x - frame.child.modifiedDeck.combine i j = x + frame.child.modifiedDeck.combine (-i) (-j) := by
    intro x
    rw [combine_eq frame i j, combine_eq frame (-i) (-j)]
    ext <;> simp <;> ring
  rw [e z, e u]
  exact (freePolicy_add_span frame hF hRU hRV (-i) (-j) z u).mpr h

/-- The quota of the free policy. -/
theorem freePolicy_quota (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) :
    RetainQuota F (freePolicy frame F η R) := by
  constructor
  · intro c hc
    exact ⟨Or.inl ⟨hc, Or.inl rfl⟩, Or.inl ⟨hc, Or.inr rfl⟩⟩
  · intro c hc
    by_cases hcl : freeClosure frame c
    · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
      have hin := freePresc_input frame η hη hi
      rcases hin with h | h
      · left
        rw [h] at hi
        exact (freePolicy_closure_iff hc hcl).mpr hi
      · right
        rw [h] at hi
        exact (freePolicy_closure_iff hc hcl).mpr hi
    · rcases selectR_input R c with h | h
      · left
        exact (freePolicy_out_iff hc hcl).mpr h.symm
      · right
        exact (freePolicy_out_iff hc hcl).mpr h.symm

theorem freePolicy_edge (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) {c i : Site}
    (h : freePolicy frame F η R c i) : Edge i c := by
  unfold freePolicy at h
  rcases h with ⟨-, he⟩ | ⟨-, ⟨-, hp⟩ | ⟨hn, hs⟩⟩
  · exact he
  · exact freePresc_input frame η hη hp
  · rw [hs]
    unfold Edge
    exact selectR_input R c

/-- The free policy carries the prescription at both free kinds of centre. -/
theorem freePolicy_prescribed (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) :
    PrescribedAt frame F η (freePolicy frame F η R) := by
  constructor
  · intro c hc hl j
    exact (freePolicy_closure_iff hl (mem_freeClosure_of_freeH frame hc)).trans (freePresc_iff_H frame η hc j)
  · intro c hc hl j
    have hcl : freeClosure frame c := ⟨0, zero_span_mem frame, Or.inr (by simpa using hc)⟩
    exact (freePolicy_closure_iff hl hcl).trans (freePresc_iff_V frame η hc j)

/-- At a white the policy keeps at most one input. -/
theorem freePolicy_white_single (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) {c i j : Site}
    (hl : laplacian F c = 0) (hi : freePolicy frame F η R c i) (hj : freePolicy frame F η R c j) : i = j := by
  by_cases hcl : freeClosure frame c
  · exact freePresc_single frame η ((freePolicy_closure_iff hl hcl).mp hi) ((freePolicy_closure_iff hl hcl).mp hj)
  · exact (freePolicy_out_iff hl hcl).mp hi |>.trans ((freePolicy_out_iff hl hcl).mp hj).symm

theorem freePolicy_freePrescribed (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) :
    ∀ c, freeClosure frame c → laplacian F c = 0 →
      ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ ∀ j, freePolicy frame F η R c j ↔ j = i := by
  intro c hc hl
  obtain ⟨i, hi⟩ := freePresc_exists frame η hc
  refine ⟨i, freePresc_input frame η hη hi, fun j => ?_⟩
  rw [freePolicy_closure_iff hl hc]
  constructor
  · intro hj
    exact freePresc_single frame η hj hi
  · intro hj
    rw [hj]
    exact hi

/-- The selection of the free policy: a chosen retained input at each white. -/
noncomputable def freeSel (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) (c : Site) : Site :=
  Classical.epsilon (freePolicy frame F η R c)

theorem freeSel_spec (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) {c : Site}
    (hl : laplacian F c = 0) : freePolicy frame F η R c (freeSel frame F η R c) := by
  have hex : ∃ j, freePolicy frame F η R c j := by
    by_cases hcl : freeClosure frame c
    · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
      exact ⟨i, (freePolicy_closure_iff hl hcl).mpr hi⟩
    · exact ⟨selectR R c, (freePolicy_out_iff hl hcl).mpr rfl⟩
  exact Classical.epsilon_spec hex

/-- The named inputs of the signed policy (the open §4 fields, not yet proved for the free policy). -/
structure FreeNamedInputs (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) : Prop where
  permitted : ∀ c i, freePolicy frame F η R c i → slipPermits F (fun z => F (z + η • frame.shortShift)) c i
  nonincreasingP : ∀ c i, freePolicy frame F η R c i → frame.cutGrade F 1 0 1 i ≤ frame.cutGrade F 1 0 1 c
  nonincreasingJ : ∀ c i, freePolicy frame F η R c i → frame.cutGrade F 0 1 η i ≤ frame.cutGrade F 0 1 η c
  strictRank : ∀ c i, freePolicy frame F η R c i → R i < R c
  squares : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η R) a b
  westAtException : frame.eps = 1 →
    freePolicy frame F η R
      (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)
      (incomingNeg (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1))

/-- The canonical signed policy of the free policy, given the rank characters and the named inputs. -/
noncomputable def canonicalSigned_of_free (frame : ChildFrame) {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1) {R : Site → ℤ}
    (N : FreeNamedInputs frame F η R) : CanonicalSignedPolicy frame F η where
  policy := freePolicy frame F η R
  free := freeClosure frame
  freeInvariant := fun step hstep site => freeClosure_add_span frame hstep site
  quota := freePolicy_quota frame F η hη R
  permitted := N.permitted
  nonincreasingP := N.nonincreasingP
  nonincreasingJ := N.nonincreasingJ
  rank := R
  strictRank := fun c i h _ _ => N.strictRank c i h
  freePrescribed := freePolicy_freePrescribed frame F η hη R
  sel := freeSel frame F η R
  sel_input := fun c hl => by
    have := freeSel_spec frame F η R hl
    exact freePolicy_edge frame F η hη R this |> fun h => by unfold Edge at h; exact h
  white_policy := fun c hl i =>
    ⟨fun h => freePolicy_white_single frame F η R hl h (freeSel_spec frame F η R hl),
      fun h => by rw [h]; exact freeSel_spec frame F η R hl⟩
  squares := N.squares
  prescribed := freePolicy_prescribed frame F η R
  policyEdge := fun c i h => freePolicy_edge frame F η hη R h
  westAtException := N.westAtException

end FLatticePaper.FreePolicy
