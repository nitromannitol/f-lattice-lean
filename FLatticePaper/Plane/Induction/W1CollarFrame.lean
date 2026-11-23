import FLatticePaper.Plane.Induction.W1OffCollarCases
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.Potentials

/-! # Task 90 (hsq): the off-collar lemma in the frame's own sets

The frame's free sets `freeH`, `freeV` (`S3FreeBoundary`) are the bottom and left arcs of the closed polygon. The collar of a site is the set
of strict sites within Chebyshev distance one of a vertex of `freeH`, `freeV`, `freeH + V` (top) or `freeV + U` (right), with the deck
vectors `V = transverse`, `U = kernel` of the child. This module identifies these sets with the grade predicates of
`W1OffCollarCases` and transfers `strict_of_not_collar` to a child frame with `3 ≤ num`. -/

namespace FLatticePaper.W1CollarFrame

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.W1OffCollarCases
open FLatticePaper.W1Exit

/-- The frame's bottom free set is the grade predicate `freeHn`. -/
theorem freeH_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeH ↔ freeHn frame.child.num frame.child.den z := by
  show (z ∈ frame.closedPolygon ∧ (z.1, z.2 - 1) ∉ frame.closedPolygon ∧ frame.hSpectrum (frame.tGrade z)) ↔ _
  rw [closedPolygon_eq_closedRect frame]
  simp only [Set.mem_setOf_eq]
  exact Iff.rfl

/-- The frame's left free set is the grade predicate `freeVn`. -/
theorem freeV_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeV ↔ freeVn frame.child.num frame.child.den z := by
  show (z ∈ frame.closedPolygon ∧ (z.1 - 1, z.2) ∉ frame.closedPolygon ∧ frame.vSpectrum (frame.sGrade z)) ↔ _
  rw [closedPolygon_eq_closedRect frame]
  simp only [Set.mem_setOf_eq]
  exact Iff.rfl

/-- The collar of a site, in the frame's own sets (the top arc is `freeH` translated by the transverse vector `V`, the right arc is `freeV`
translated by the kernel `U`). -/
def CollarFrame (frame : ChildFrame) (z : Site) : Prop :=
  ∃ v : Site, |v.1 - z.1| ≤ 1 ∧ |v.2 - z.2| ≤ 1 ∧
    (v ∈ frame.freeH ∨ v ∈ frame.freeV ∨ (v - frame.child.modifiedDeck.transverse) ∈ frame.freeH ∨
      (v - frame.child.modifiedDeck.kernel) ∈ frame.freeV)

/-- The frame collar is the grade collar `Collar`. -/
theorem collarFrame_iff (frame : ChildFrame) (z : Site) :
    CollarFrame frame z ↔ Collar frame.child.num frame.child.den z := by
  have hT : frame.child.modifiedDeck.transverse =
      (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
    frame.child_modifiedDeck_transverse
  have hK : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := frame.kernel_coords
  have eV : ∀ v : Site, v - frame.child.modifiedDeck.transverse =
      (v.1 - (frame.child.num - frame.child.den), v.2 - (frame.child.den + frame.child.num)) := by
    intro v
    rw [hT]
    ext
    · simp only [Prod.fst_sub]
    · simp only [Prod.snd_sub]; ring
  have eU : ∀ v : Site, v - frame.child.modifiedDeck.kernel =
      (v.1 - frame.child.den, v.2 - frame.child.num) := by
    intro v
    rw [hK]
    rfl
  unfold CollarFrame Collar
  constructor
  · rintro ⟨v, h1, h2, h3⟩
    refine ⟨v, h1, h2, ?_⟩
    rcases h3 with h3 | h3 | h3 | h3
    · exact Or.inl ((freeH_iff frame v).1 h3)
    · exact Or.inr (Or.inl ((freeV_iff frame v).1 h3))
    · rw [eV v] at h3
      exact Or.inr (Or.inr (Or.inl ((freeH_iff frame _).1 h3)))
    · rw [eU v] at h3
      exact Or.inr (Or.inr (Or.inr ((freeV_iff frame _).1 h3)))
  · rintro ⟨v, h1, h2, h3⟩
    refine ⟨v, h1, h2, ?_⟩
    rcases h3 with h3 | h3 | h3 | h3
    · exact Or.inl ((freeH_iff frame v).2 h3)
    · exact Or.inr (Or.inl ((freeV_iff frame v).2 h3))
    · rw [eV v]
      exact Or.inr (Or.inr (Or.inl ((freeH_iff frame _).2 h3)))
    · rw [eU v]
      exact Or.inr (Or.inr (Or.inr ((freeV_iff frame _).2 h3)))

/-- **The off-collar lemma for a child frame** (task 90): a strict site of the frame outside its collar has every corner of a unit square
through it strict, for a child with `3 ≤ num`. -/
theorem strict_corners_of_not_collar (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) (z : Site)
    (hs : frame.openRect z) (hc : ¬ CollarFrame frame z) (w : Site)
    (hw1 : |w.1 - z.1| ≤ 1) (hw2 : |w.2 - z.2| ≤ 1) : frame.openRect w := by
  obtain ⟨hodd_n, hodd_d⟩ := child_parity frame
  have hnd : frame.child.num + 2 ≤ frame.child.den := by
    have := frame.child_facts.2.2.1
    omega
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  rw [openRect_iff] at hs ⊢
  rw [collarFrame_iff] at hc
  exact strict_of_not_collar _ _ hn3 hnd hcop hodd_n hodd_d z hs hc w hw1 hw2

end FLatticePaper.W1CollarFrame
