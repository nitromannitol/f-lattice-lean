import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.ForcedArrows

/-! # W3 (hno, step 2): the restricted no-fort is invariant under the deck translation

The translation step of the Q1 no-fort (Q1 l.13: translate the set so that its minimal site lies at the fixed pair) needs the
no-fort property to be translation invariant. This file gives the reusable forms:

* `shiftSet S t = {z | z + t ∈ S}`, the translate of a site set by `−t` (so that `z ∈ shiftSet S t` iff `z + t ∈ S`).
* `isRestrictedFort_shiftSet`: a restricted fort translated by an even shift `t` is a restricted fort, given that the field's
  Laplacian and the permit relation are invariant under `t` (`hL`, `hP`).
* `restrictedNoFort_grade_shift`: `RestrictedNoFort field grade permits` implies `RestrictedNoFort field (grade (· − t)) permits`
  under the same invariance. No drift hypothesis on the grade is needed: a fort for the shifted grade is shifted back.
* `restrictedNoFort_grade_shift_permitsQ1`: the instance for `permitsQ1` and a span element `t`, with the deck invariance
  `hL` of the field. -/

namespace FLatticePaper.RestrictedFortShift

open Farey FLatticePaper FLatticePaper.Induction

/-- The translate of a site set: `z ∈ shiftSet S t` iff `z + t ∈ S`. -/
def shiftSet (S : Set Site) (t : Site) : Set Site := {z | z + t ∈ S}

/-- **A restricted fort is translated to a restricted fort** under an even shift `t` that leaves the Laplacian and the
permit relation invariant. -/
theorem isRestrictedFort_shiftSet {field : Field} {permits : Site → Site → Prop} {t : Site} {S : Set Site}
    (ht : EvenSite t)
    (hL : ∀ z, laplacian field (z + t) = laplacian field z)
    (hP : ∀ c i, permits (c + t) (i + t) ↔ permits c i)
    (hS : IsRestrictedFort field permits S) :
    IsRestrictedFort field permits (shiftSet S t) := by
  intro z hz
  have hzS : z + t ∈ S := hz
  have h := hS (z + t) hzS
  rw [hL z, FLatticePaper.ForcedArrows.incomingNeg_add_even ht, FLatticePaper.ForcedArrows.incomingPos_add_even ht,
    hP z (incomingNeg z), hP z (incomingPos z)] at h
  exact h

/-- **The restricted no-fort is invariant under the grade shift `g ↦ g(· − t)`.** A fort for the shifted grade, translated by
`t`, is a restricted fort for the original grade. -/
theorem restrictedNoFort_grade_shift {field grade : Field} {permits : Site → Site → Prop} {t : Site}
    (ht : EvenSite t)
    (hL : ∀ z, laplacian field (z + t) = laplacian field z)
    (hP : ∀ c i, permits (c + t) (i + t) ↔ permits c i)
    (hno : RestrictedNoFort field grade permits) :
    RestrictedNoFort field (fun z => grade (z - t)) permits := by
  intro level S hne hres hlev
  obtain ⟨a, ha⟩ := hne
  refine hno level (shiftSet S t) ⟨a - t, ?_⟩ (isRestrictedFort_shiftSet ht hL hP hres) ?_
  · show a - t + t ∈ S
    rw [sub_add_cancel]
    exact ha
  · intro z hz
    have h := hlev (z + t) hz
    simpa using h

/-- **The instance for `permitsQ1`.** For a span element `t` of the child deck and the deck invariance `hL` of the field, the
restricted no-fort for `permitsQ1` is invariant under `K ↦ K(· − t)`. -/
theorem restrictedNoFort_grade_shift_permitsQ1 (frame : ChildFrame) (F : Field) (η : ℤ)
    (hL : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c)
    (grade : Field) (hno : RestrictedNoFort F grade (AuxRankQ1.permitsQ1 frame F η))
    {t : Site} (ht : t ∈ frame.child.modifiedDeck.span) :
    RestrictedNoFort F (fun z => grade (z - t)) (AuxRankQ1.permitsQ1 frame F η) := by
  obtain ⟨i, j, rfl⟩ := ht
  have hsp : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span := ⟨i, j, rfl⟩
  exact restrictedNoFort_grade_shift (FreePolicy.span_even frame hsp) (fun z => hL z i j)
    (fun c i' => AuxRankQ1.permitsQ1_shift frame F η hL _ hsp c i') hno

end FLatticePaper.RestrictedFortShift
