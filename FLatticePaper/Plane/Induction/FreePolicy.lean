import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.DeckSelection
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.SquareClauses

/-! hgames: the rank-independent policy graph (the lead's design point).

* blacks keep both inputs;
* a white in the deck closure `freeClosure` keeps its prescribed input (the signed H/V direction at its free representative, `FreePresc`);
* a nonfree white keeps its W1-forced input `forcedSel` (the output of a forcing derivation, `ForcedEdge`).

The graph does not depend on a rank. At a nonfree white the forced output exists (`forcedExists_of`: W1 at a strict-interior translate,
moved back by the span, `forcedEdge_add`). Its uniqueness and span equivariance follow from the squares of the policy, and the squares of
the policy follow from a strict rank on the retained edges (`squares_of_strict`: the corner of least rank has a retained input in the square
of smaller rank). So the only rank input is `strictRank`, named. -/

namespace FLatticePaper.FreePolicy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.DeckSelection FLatticePaper.FreeClosure FLatticePaper.FreeOrbit
open FLatticePaper.SquareClauses FLatticePaper.AndOrRank

/-- The prescribed input of the closure: `i = c + prescribed(c + t)` at a free representative `c + t`, `t` in the span. -/
def FreePresc (frame : ChildFrame) (η : ℤ) (c i : Site) : Prop :=
  ∃ t ∈ frame.child.modifiedDeck.span,
    (c + t ∈ frame.freeH ∧ i = c + frame.prescribedH η (c + t)) ∨
      (c + t ∈ frame.freeV ∧ i = c + frame.prescribedV η (c + t))

/-- The forced input of a nonfree white: an arbitrary forced output (unique once the squares hold, `forced_sound`). -/
noncomputable def forcedSel (F : Field) (c : Site) : Site :=
  Classical.epsilon (fun o => ForcedEdge F (fun _ _ => False) c o)

/-- The forced outputs exist at the nonfree whites. -/
def ForcedExists (frame : ChildFrame) (F : Field) : Prop :=
  ∀ c, ¬ freeClosure frame c → laplacian F c = 0 → ∃ o, ForcedEdge F (fun _ _ => False) c o

/-- The rank-independent policy: black keeps both inputs; a white in the closure keeps its prescribed input; another white keeps its
forced input. -/
def freePolicy (frame : ChildFrame) (F : Field) (η : ℤ) : Site → Site → Prop :=
  fun c i => (laplacian F c = -1 ∧ Edge i c) ∨
    (laplacian F c = 0 ∧
      ((freeClosure frame c ∧ FreePresc frame η c i) ∨ (¬ freeClosure frame c ∧ i = forcedSel F c)))

theorem zero_span_mem (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩

theorem span_even (frame : ChildFrame) {t : Site} (ht : t ∈ frame.child.modifiedDeck.span) : EvenSite t := by
  obtain ⟨i, j, rfl⟩ := ht
  rw [combine_eq frame i j]
  exact evenSite_span frame i j

/-! ### The forced inputs at the nonfree whites -/

/-- The forced outputs exist at each nonfree white: `W1Forced` at a strict-interior translate, moved back by the span. -/
theorem forcedExists_of (frame : ChildFrame) {F : Field} (hP : frame.Packet F)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F) : ForcedExists frame F := by
  intro c hnc hl
  have hnf : Nonfree frame c := by
    intro v hv hmem
    exact hnc ⟨v, hv, (Set.mem_union _ _ _).mp hmem⟩
  obtain ⟨v, hv, hSI⟩ := nonfree_bridge frame c hnf
  have hwv : laplacian F (c + v) = 0 := by
    rw [laplacian_span_inv frame F hP hv c]
    exact hl
  obtain ⟨o, ho⟩ := hW1 (c + v) hSI hwv
  have hf : ForcedEdge F (fun _ _ => False) (c + v) o := FLatticePaper.W1.forcedEdgeIn_forced ho
  have hnv : -v ∈ frame.child.modifiedDeck.span := span_neg_mem hv
  have hfz := forcedEdge_add F (evenSite_of_span frame hnv) (fun y => laplacian_span_inv frame F hP hnv y) hf
  rw [add_neg_cancel_right] at hfz
  exact ⟨o + -v, hfz⟩

/-- A forced edge points to an incoming input of its centre. -/
theorem forcedEdge_input {F : Field} {c o : Site} (h : ForcedEdge F (fun _ _ => False) c o) :
    o = incomingNeg c ∨ o = incomingPos c := by
  cases h with
  | seed hs => exact False.elim hs
  | @unit a b c' o' inside hc hw ho hout hin hforced => exact ho

theorem forcedSel_spec {F : Field} {c : Site} (hex : ∃ o, ForcedEdge F (fun _ _ => False) c o) :
    ForcedEdge F (fun _ _ => False) c (forcedSel F c) :=
  Classical.epsilon_spec hex

theorem forcedSel_input {F : Field} {c : Site} (hex : ∃ o, ForcedEdge F (fun _ _ => False) c o) :
    forcedSel F c = incomingNeg c ∨ forcedSel F c = incomingPos c :=
  forcedEdge_input (forcedSel_spec hex)

/-! ### The prescribed inputs: incoming edges, uniqueness, equivariance -/

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

/-- At a free H centre the prescription is exactly the H direction at the centre. -/
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
  · have h0 : t' - t = 0 := freeH_rep_zero frame hsp hH (by rw [e]; exact hH')
    have htt : t' = t := sub_eq_zero.mp h0
    subst htt
    rw [hi, hj]
  · have hc' : c + t' ∈ frame.freeV := hV'
    rw [← e] at hc'
    exact absurd hc' (freeH_not_freeV_shift frame hsp hH)
  · have hc' : c + t' ∈ frame.freeH := hH'
    rw [← e] at hc'
    exact absurd hc' (freeV_not_freeH_shift frame hsp hV)
  · have h0 : t' - t = 0 := freeV_rep_zero frame hsp hV (by rw [e]; exact hV')
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

/-! ### The policy: its pieces at each kind of white -/

theorem freePolicy_closure_iff {frame : ChildFrame} {F : Field} {η : ℤ} {c i : Site}
    (hl : laplacian F c = 0) (hc : freeClosure frame c) :
    freePolicy frame F η c i ↔ FreePresc frame η c i := by
  unfold freePolicy
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ⟨-, h⟩ | ⟨hn, -⟩⟩)
    · exact absurd (hl.symm.trans h) (by norm_num)
    · exact h
    · exact absurd hc hn
  · intro h
    exact Or.inr ⟨hl, Or.inl ⟨hc, h⟩⟩

theorem freePolicy_out_iff {frame : ChildFrame} {F : Field} {η : ℤ} {c i : Site}
    (hl : laplacian F c = 0) (hn : ¬ freeClosure frame c) :
    freePolicy frame F η c i ↔ i = forcedSel F c := by
  unfold freePolicy
  constructor
  · rintro (⟨h, -⟩ | ⟨-, ⟨hc, -⟩ | ⟨-, h⟩⟩)
    · exact absurd (hl.symm.trans h) (by norm_num)
    · exact absurd hc hn
    · exact h
  · intro h
    exact Or.inr ⟨hl, Or.inr ⟨hn, h⟩⟩

/-- The quota of the policy: blacks keep both inputs; a white keeps the prescribed or the forced input. -/
theorem freePolicy_quota (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hex : ForcedExists frame F) : RetainQuota F (freePolicy frame F η) := by
  constructor
  · intro c hc
    exact ⟨Or.inl ⟨hc, Or.inl rfl⟩, Or.inl ⟨hc, Or.inr rfl⟩⟩
  · intro c hc
    by_cases hcl : freeClosure frame c
    · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
      rcases freePresc_input frame η hη hi with h | h
      · left
        rw [h] at hi
        exact (freePolicy_closure_iff hc hcl).mpr hi
      · right
        rw [h] at hi
        exact (freePolicy_closure_iff hc hcl).mpr hi
    · obtain ⟨o, ho⟩ := hex c hcl hc
      rcases forcedSel_input ⟨o, ho⟩ with h | h
      · left
        exact (freePolicy_out_iff hc hcl).mpr h.symm
      · right
        exact (freePolicy_out_iff hc hcl).mpr h.symm

theorem freePolicy_edge (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hex : ForcedExists frame F) {c i : Site} (h : freePolicy frame F η c i) : Edge i c := by
  unfold freePolicy at h
  rcases h with ⟨-, he⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · exact he
  · exact freePresc_input frame η hη hp
  · obtain ⟨o, ho⟩ := hex c hn hl
    rw [hs]
    exact forcedSel_input ⟨o, ho⟩

/-- The free policy carries the prescription at both free kinds of centre. -/
theorem freePolicy_prescribed (frame : ChildFrame) (F : Field) (η : ℤ) :
    PrescribedAt frame F η (freePolicy frame F η) := by
  constructor
  · intro c hc hl j
    exact (freePolicy_closure_iff hl (mem_freeClosure_of_freeH frame hc)).trans (freePresc_iff_H frame η hc j)
  · intro c hc hl j
    have hcl : freeClosure frame c := ⟨0, zero_span_mem frame, Or.inr (by simpa using hc)⟩
    exact (freePolicy_closure_iff hl hcl).trans (freePresc_iff_V frame η hc j)

/-- At a white the policy keeps at most one input. -/
theorem freePolicy_white_single (frame : ChildFrame) (F : Field) (η : ℤ) {c i j : Site}
    (hl : laplacian F c = 0) (hi : freePolicy frame F η c i) (hj : freePolicy frame F η c j) : i = j := by
  by_cases hcl : freeClosure frame c
  · exact freePresc_single frame η ((freePolicy_closure_iff hl hcl).mp hi) ((freePolicy_closure_iff hl hcl).mp hj)
  · exact ((freePolicy_out_iff hl hcl).mp hi).trans ((freePolicy_out_iff hl hcl).mp hj).symm

theorem freePolicy_freePrescribed (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    ∀ c, freeClosure frame c → laplacian F c = 0 →
      ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ ∀ j, freePolicy frame F η c j ↔ j = i := by
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

/-- The selection of the policy: a retained input at each white (the unique one, `freePolicy_white_single`). -/
noncomputable def freeSel (frame : ChildFrame) (F : Field) (η : ℤ) (c : Site) : Site :=
  Classical.epsilon (freePolicy frame F η c)

theorem freeSel_spec (frame : ChildFrame) (F : Field) (η : ℤ) {c : Site} (hl : laplacian F c = 0) :
    freePolicy frame F η c (freeSel frame F η c) := by
  have hex' : ∃ j, freePolicy frame F η c j := by
    by_cases hcl : freeClosure frame c
    · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
      exact ⟨i, (freePolicy_closure_iff hl hcl).mpr hi⟩
    · exact ⟨forcedSel F c, (freePolicy_out_iff hl hcl).mpr rfl⟩
  exact Classical.epsilon_spec hex'

theorem freeSel_input (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (hex : ForcedExists frame F)
    {c : Site} (hl : laplacian F c = 0) :
    freeSel frame F η c = incomingNeg c ∨ freeSel frame F η c = incomingPos c :=
  freePolicy_edge frame F η hη hex (freeSel_spec frame F η hl)

/-! ### Equivariance, the squares, and the deck form -/

/-- The forced input is equivariant under the span: its translate is a forced output of the translate, and the squares make it unique. -/
theorem forcedSel_add_span (frame : ChildFrame) {F : Field} {η : ℤ} (hP : frame.Packet F) (hex : ForcedExists frame F)
    (hη : η = 1 ∨ η = -1) (hsq : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η) a b)
    {s : Site} (hs : s ∈ frame.child.modifiedDeck.span) (z : Site) (hn : ¬ freeClosure frame z)
    (hl : laplacian F z = 0) : forcedSel F (z + s) = forcedSel F z + s := by
  have hnc' : ¬ freeClosure frame (z + s) := fun h => hn ((freeClosure_add_span frame hs z).mp h)
  have hl' : laplacian F (z + s) = 0 := (laplacian_span_inv frame F hP hs z).trans hl
  have hz : ForcedEdge F (fun _ _ => False) (z + s) (forcedSel F z + s) :=
    forcedEdge_add F (evenSite_of_span frame hs) (fun y => laplacian_span_inv frame F hP hs y)
      (forcedSel_spec (hex z hn hl))
  have hsel : freeSel frame F η (z + s) = forcedSel F z + s :=
    forced_sound F (fun _ _ => False) (freeSel frame F η)
      (fun c hc => freeSel_input frame F η hη hex hc) (fun _ _ h => False.elim h) hsq (z + s) (forcedSel F z + s) hz
  have hfs : forcedSel F (z + s) = freeSel frame F η (z + s) :=
    ((freePolicy_out_iff hl' hnc').mp (freeSel_spec frame F η hl')).symm
  rw [hfs, hsel]

/-- The policy is equivariant under a span translate: the Laplacian and the closure are invariant, the prescription is reindexed, and the
forced input is equivariant (`forcedSel_add_span`). -/
theorem freePolicy_add_span (frame : ChildFrame) {F : Field} {η : ℤ} (hP : frame.Packet F) (hex : ForcedExists frame F)
    (hη : η = 1 ∨ η = -1) (hsq : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η) a b)
    {s : Site} (hs : s ∈ frame.child.modifiedDeck.span) (z u : Site) :
    freePolicy frame F η (z + s) (u + s) ↔ freePolicy frame F η z u := by
  have hz := laplacian_span_inv frame F hP hs z
  have hc := freeClosure_add_span frame hs z
  have he : Edge (u + s) (z + s) ↔ Edge u z := by
    unfold Edge
    rw [incomingNeg_add_even (span_even frame hs), incomingPos_add_even (span_even frame hs)]
    simp
  have hp := freePresc_add_span frame η hs z u
  have hf : ¬ freeClosure frame z → laplacian F z = 0 → (u + s = forcedSel F (z + s) ↔ u = forcedSel F z) := by
    intro hn hl
    rw [forcedSel_add_span frame hP hex hη hsq hs z hn hl]
    constructor
    · intro h
      exact add_right_cancel h
    · intro h
      rw [h]
  unfold freePolicy
  rw [hz, hc, he, hp]
  exact or_congr Iff.rfl (and_congr_right fun hl => or_congr Iff.rfl (and_congr_right fun hn => hf hn hl))

/-- The deck form: the policy is invariant under every deck translate `−(iU + jV)`. -/
theorem freePolicy_deck (frame : ChildFrame) {F : Field} {η : ℤ} (hP : frame.Packet F) (hex : ForcedExists frame F)
    (hη : η = 1 ∨ η = -1) (hsq : ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η) a b) (i j : ℤ) (z u : Site)
    (h : freePolicy frame F η z u) :
    freePolicy frame F η (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j) := by
  have e : ∀ x : Site, x - frame.child.modifiedDeck.combine i j = x + frame.child.modifiedDeck.combine (-i) (-j) := by
    intro x
    rw [combine_eq frame i j, combine_eq frame (-i) (-j)]
    ext <;> simp <;> ring
  rw [e z, e u]
  exact (freePolicy_add_span frame hP hex hη hsq ⟨-i, -j, rfl⟩ z u).mpr h

/-- **The squares from a strict rank.** On the retained edges of the policy, a strict rank excludes every square whose corners all keep an
input inside the square: the corner of least rank has a retained input of smaller rank in the square. -/
theorem squares_of_strict (frame : ChildFrame) {F : Field} {η : ℤ} (hP : frame.Packet F)
    {R : Site → ℤ} (hstrict : ∀ c i, freePolicy frame F η c i → R i < R c) :
    ∀ a b : ℤ, SquareClauseSat F (freeSel frame F η) a b := by
  intro a b
  unfold SquareClauseSat
  intro hall
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image (squareCorners a b) R ⟨(a, b), by simp [squareCorners]⟩
  have hk := hall c0 hc0
  unfold keptInside at hk
  by_cases hb : laplacian F c0 = -1
  · rw [if_pos hb] at hk
    rcases hk with hk | hk
    · have h1 := hstrict c0 (incomingNeg c0) (Or.inl ⟨hb, Or.inl rfl⟩)
      have h2 := hmin _ hk
      linarith
    · have h1 := hstrict c0 (incomingPos c0) (Or.inl ⟨hb, Or.inr rfl⟩)
      have h2 := hmin _ hk
      linarith
  · rw [if_neg hb] at hk
    have hl : laplacian F c0 = 0 := (hP.binary c0).resolve_left hb
    have h1 := hstrict c0 _ (freeSel_spec frame F η hl)
    have h2 := hmin _ hk
    linarith

/-! ### The named inputs and the canonical signed policy -/

/-- The named inputs of the signed policy of a sign and a rank: the permits, the monotonicity of `P` and `J`, the strict rank along all
retained edges (the rank is built over this fixed graph), and the exceptional west input. -/
structure FreeNamedInputs (frame : ChildFrame) (F : Field) (η : ℤ) (R : Site → ℤ) : Prop where
  permitted : ∀ c i, freePolicy frame F η c i → slipPermits F (fun z => F (z + η • frame.shortShift)) c i
  nonincreasingP : ∀ c i, freePolicy frame F η c i → frame.cutGrade F 1 0 1 i ≤ frame.cutGrade F 1 0 1 c
  nonincreasingJ : ∀ c i, freePolicy frame F η c i → frame.cutGrade F 0 1 η i ≤ frame.cutGrade F 0 1 η c
  strictRank : ∀ c i, freePolicy frame F η c i → R i < R c
  westAtException : frame.eps = 1 →
    freePolicy frame F η
      (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)
      (incomingNeg (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1))

/-- The canonical signed policy of the free policy: the squares come from the strict rank, the rest of the fields are the proved ones. -/
noncomputable def canonicalSigned_of_free (frame : ChildFrame) {F : Field} {η : ℤ} (hP : frame.Packet F)
    (hex : ForcedExists frame F) (hη : η = 1 ∨ η = -1) {R : Site → ℤ} (N : FreeNamedInputs frame F η R) :
    CanonicalSignedPolicy frame F η where
  policy := freePolicy frame F η
  free := freeClosure frame
  freeInvariant := fun step hstep site => freeClosure_add_span frame hstep site
  quota := freePolicy_quota frame F η hη hex
  permitted := N.permitted
  nonincreasingP := N.nonincreasingP
  nonincreasingJ := N.nonincreasingJ
  rank := R
  strictRank := fun c i h _ _ => N.strictRank c i h
  freePrescribed := freePolicy_freePrescribed frame F η hη
  sel := freeSel frame F η
  sel_input := fun c hl => freeSel_input frame F η hη hex hl
  white_policy := fun c hl i =>
    ⟨fun h => freePolicy_white_single frame F η hl h (freeSel_spec frame F η hl),
      fun h => by rw [h]; exact freeSel_spec frame F η hl⟩
  squares := squares_of_strict frame hP N.strictRank
  prescribed := freePolicy_prescribed frame F η
  policyEdge := fun c i h => freePolicy_edge frame F η hη hex h
  westAtException := N.westAtException

end FLatticePaper.FreePolicy
