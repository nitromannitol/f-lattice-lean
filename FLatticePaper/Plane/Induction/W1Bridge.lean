import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1Exit
import FLatticePaper.Plane.Induction.SheetPieces

/-! # Task 90 (bridge): `W1Forced` transfers between fields that agree on the closed polygon

The forced clauses of a derivation in the strict interior `R = StrictInterior n d` involve only the laplacians of the corners of unit squares
in `R`, and a laplacian uses the centre and its two inputs (`laplacian`). A strict-interior site and both its inputs lie in the closed
polygon (`strictInterior_closedRect` for the site, `rectInputs` for the inputs). So fields that agree on the closed polygon have the same
laplacians on the strict interior, and by induction on `ForcedEdgeIn` the same derivations. -/

namespace FLatticePaper.W1Bridge

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1
open FLatticePaper.W1MSheet

/-- The laplacian at a site depends only on the values at the site and its two inputs. -/
theorem laplacian_congr {F F' : Field} {z : Site} (h0 : F z = F' z)
    (h1 : F (incomingNeg z) = F' (incomingNeg z)) (h2 : F (incomingPos z) = F' (incomingPos z)) :
    laplacian F z = laplacian F' z := by
  unfold laplacian
  rw [h0, h1, h2]

/-- A derivation in `R` for `F` is a derivation for `F'`, when the two fields agree at each site of `R` and its inputs. -/
theorem forcedEdgeIn_congr {F F' : Field} {R : Site → Prop} {seed : Site → Site → Prop}
    (hagree : ∀ c, R c → F c = F' c ∧ F (incomingNeg c) = F' (incomingNeg c) ∧ F (incomingPos c) = F' (incomingPos c))
    {c o : Site} (h : ForcedEdgeIn F R seed c o) : ForcedEdgeIn F' R seed c o := by
  induction h with
  | seed hs => exact ForcedEdgeIn.seed hs
  | @unit a b c o inside hR hc hw ho hout hin hforced ih =>
    have hcl : ∀ c' ∈ squareCorners a b, laplacian F c' = laplacian F' c' := fun c' hc' => by
      obtain ⟨e0, e1, e2⟩ := hagree c' (hR c' hc')
      exact laplacian_congr e0 e1 e2
    refine ForcedEdgeIn.unit inside hR hc ?_ ho hout ?_ ?_
    · rw [← hcl c hc]
      exact hw
    · intro c' hc' hne
      rcases hin c' hc' hne with hb | ⟨h0, hi, hi'⟩
      · exact Or.inl (by rw [← hcl c' hc']; exact hb)
      · exact Or.inr ⟨by rw [← hcl c' hc']; exact h0, hi, hi'⟩
    · intro c' hc' hne h0
      exact ih c' hc' hne (by rw [hcl c' hc']; exact h0)

/-- **`W1Forced` transfers** (task 90 bridge): for a frame, fields agreeing on the closed polygon have the same `W1Forced`. -/
theorem w1Forced_congr (frame : ChildFrame) {F F' : Field} (hEq : ∀ s ∈ frame.closedPolygon, F s = F' s)
    (h : W1Forced frame.child.num frame.child.den F) : W1Forced frame.child.num frame.child.den F' := by
  have hn : 1 ≤ frame.child.num := by have := frame.child_facts.1; omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by have := frame.child_facts.2.2.1; omega
  -- the strict-interior sites and their inputs lie in the closed polygon
  have hcl : ∀ c, StrictInterior frame.child.num frame.child.den c →
      F c = F' c ∧ F (incomingNeg c) = F' (incomingNeg c) ∧ F (incomingPos c) = F' (incomingPos c) := by
    intro c hc
    have hcP : c ∈ frame.closedPolygon := by
      rw [FLatticePaper.W1.closedPolygon_eq_closedRect]
      exact FLatticePaper.W1.strictInterior_closedRect hn hnd c hc
    have hi1 : incomingNeg c ∈ frame.closedPolygon :=
      FLatticePaper.W1Exit.rectInputs frame c ((FLatticePaper.W1Exit.openRect_iff frame c).2 hc) _ (Or.inl rfl)
    have hi2 : incomingPos c ∈ frame.closedPolygon :=
      FLatticePaper.W1Exit.rectInputs frame c ((FLatticePaper.W1Exit.openRect_iff frame c).2 hc) _ (Or.inr rfl)
    exact ⟨hEq c hcP, hEq _ hi1, hEq _ hi2⟩
  intro z hz hw
  obtain ⟨o, ho⟩ := h z hz (by
    have hc := hcl z hz
    rw [laplacian_congr hc.1 hc.2.1 hc.2.2] at *
    exact hw)
  refine ⟨o, forcedEdgeIn_congr hcl ho⟩

/-- **The bridge** (task 90): `W1Forced` of the sheet minimum gives `W1Forced` of the standard field of the word. -/
theorem W1Forced_standardField_of_MW (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hW : W1Forced (frameAt word).child.num (frameAt word).child.den (MW word)) :
    W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word) :=
  w1Forced_congr (frameAt word) (fun _ hs => (standardField_eq_sheetMin_of_strong h hSE hs).symm) hW

end FLatticePaper.W1Bridge
