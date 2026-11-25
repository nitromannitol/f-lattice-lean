import FLatticePaper.Plane.Induction.AuxRank
import FLatticePaper.Plane.Induction.FreePolicy

/-! The auxiliary graph of a sign `η ∈ {±1}`, generalising `AuxRank.auxRetained` (sign +1).

`auxS frame F η c i`: blacks keep both inputs; a white in the closure keeps its sign-`η` prescribed input; a nonfree white keeps a
sign-`η` permitted input. The forced permit at a nonfree white is `forced_permitted_S` (from a strict rank on `auxS`), and every
`freePolicy` edge is an `auxS` edge (`freePolicy_aux`), so the rank is strict on the policy edges. -/

namespace FLatticePaper.AuxRankSign

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRank FLatticePaper.FreePolicy FLatticePaper.FreeClosure
  FLatticePaper.SquareClauses

/-- The auxiliary graph of sign `η`. -/
def auxS (frame : ChildFrame) (F : Field) (η : ℤ) (c i : Site) : Prop :=
  (laplacian F c = -1 ∧ Edge i c) ∨
    (laplacian F c = 0 ∧ ((freeClosure frame c ∧ FreePresc frame η c i) ∨
      (¬ freeClosure frame c ∧ Edge i c ∧ slipPermits F (fun z => F (z + η • frame.shortShift)) c i)))

theorem auxS_edge {frame : ChildFrame} {F : Field} {η : ℤ} (hη : η = 1 ∨ η = -1) {c i : Site}
    (h : auxS frame F η c i) : Edge i c := by
  unfold auxS at h
  rcases h with ⟨-, he⟩ | ⟨-, ⟨hcl, hp⟩ | ⟨-, he, -⟩⟩
  · exact he
  · exact freePresc_input frame η hη hp
  · exact he

/-- Every white has an input in the sign-`η` auxiliary graph. -/
theorem auxS_exists (frame : ChildFrame) {F : Field} (η : ℤ) (hη : η = 1 ∨ η = -1) (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift))) (hI : ∀ z, F (reflectionI - z) = F z) {c : Site}
    (hc : laplacian F c = 0) :
    ∃ i, auxS frame F η c i := by
  by_cases hcl : freeClosure frame c
  · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
    exact ⟨i, Or.inr ⟨hc, Or.inl ⟨hcl, hi⟩⟩⟩
  · rcases hη with rfl | rfl
    · obtain ⟨i, hi, hp⟩ := white_permitted_input hσ hbin hU hc
      refine ⟨i, Or.inr ⟨hc, Or.inr ⟨hcl, hi, ?_⟩⟩⟩
      simpa [one_smul] using hp
    · obtain ⟨i, hi, hp⟩ := white_permitted_input_neg hσ hbin hU hI hc
      refine ⟨i, Or.inr ⟨hc, Or.inr ⟨hcl, hi, ?_⟩⟩⟩
      simpa [neg_one_smul] using hp

/-- **The forced permit of sign `η`, from a strict rank on `auxS`**: the forced output of a nonfree white is aux-retained, hence
permitted (`forced_sound`). -/
theorem forced_aux {frame : ChildFrame} {F : Field} (η : ℤ) (hη : η = 1 ∨ η = -1) (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift))) (hI : ∀ z, F (reflectionI - z) = F z)
    {R : Site → ℤ} (hstrict : ∀ c i, auxS frame F η c i → R i < R c)
    {c o : Site} (hl : laplacian F c = 0)
    (hf : ForcedEdge F (fun _ _ => False) c o) :
    auxS frame F η c o := by
  let sel : Site → Site := fun c => Classical.epsilon (auxS frame F η c)
  have hsel : ∀ c, laplacian F c = 0 → auxS frame F η c (sel c) := fun c hc =>
    Classical.epsilon_spec (auxS_exists frame η hη hσ hbin hU hI hc)
  have hblack : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → auxS frame F η c i :=
    fun c i hc hi => Or.inl ⟨hc, hi⟩
  have hsq := squares_gen F (auxS frame F η) sel R hbin hblack hsel hstrict
  have hsi : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c := fun c hc =>
    auxS_edge hη (hsel c hc)
  have hfs := forced_sound F (fun _ _ => False) sel hsi (fun _ _ h => False.elim h) hsq c o hf
  rw [← hfs]
  exact hsel c hl

/-- **The forced permit of sign `η`.** -/
theorem forced_permitted_S {frame : ChildFrame} {F : Field} (η : ℤ) (hη : η = 1 ∨ η = -1) (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift))) (hI : ∀ z, F (reflectionI - z) = F z)
    {R : Site → ℤ} (hstrict : ∀ c i, auxS frame F η c i → R i < R c)
    {c o : Site} (hnc : ¬ freeClosure frame c) (hl : laplacian F c = 0)
    (hf : ForcedEdge F (fun _ _ => False) c o) :
    slipPermits F (fun z => F (z + η • frame.shortShift)) c o := by
  have ho := forced_aux η hη hσ hbin hU hI hstrict hl hf
  unfold auxS at ho
  rcases ho with ⟨hb, -⟩ | ⟨-, ⟨hcl, -⟩ | ⟨-, -, hp⟩⟩
  · exact absurd (hl.symm.trans hb) (by norm_num)
  · exact absurd hcl hnc
  · exact hp

/-- **Every free-policy edge is an aux edge**, so a strict rank on `auxS` is strict on the policy edges. The nonfree white edges use
`forced_aux` (the forced output is aux-retained). -/
theorem freePolicy_aux {frame : ChildFrame} {F : Field} (η : ℤ) (hη : η = 1 ∨ η = -1) (hex : ForcedExists frame F)
    (hσ : EvenSite frame.shortShift) (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift))) (hI : ∀ z, F (reflectionI - z) = F z)
    {R : Site → ℤ} (hstrict : ∀ c i, auxS frame F η c i → R i < R c) {c i : Site}
    (hci : freePolicy frame F η c i) : auxS frame F η c i := by
  unfold freePolicy at hci
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · exact Or.inl ⟨hl, hE⟩
  · exact Or.inr ⟨hl, Or.inl ⟨hcl, hp⟩⟩
  · rw [hs]
    exact forced_aux η hη hσ hbin hU hI hstrict hl (forcedSel_spec (hex c hn hl))

end FLatticePaper.AuxRankSign
