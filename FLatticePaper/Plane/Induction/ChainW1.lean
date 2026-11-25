import FLatticePaper.Plane.Induction.BothFreeRise
import FLatticePaper.Plane.Induction.Q24Instances

/-! Task 72 / Q24: the chain monotonicity from the W1 classification, with the joint representative as the one explicit hypothesis.

The rise of the chain potential `Φ_η` along the sign-`η` game has two roots `z` and `z + ησ`. `rise_roots_not_SI` (from the W1 input
`hW1word`, the W1 forcing of the word's own frame) shows that neither root is a strict-interior centre. The remaining input is the joint
free representative `FreeRiseRep` of the two roots, which is not derived here: the numerical check of a common free deck representative
fails for white pairs of the closed polygon (open question Q28, the counterexample pair `z = (3,1)`, `z + σ = (7,3)` for the word `[1]`,
`η = +1`, `σ = (4,2)`). -/

namespace FLatticePaper.ChainW1

open FLatticePaper FLatticePaper.Induction FLatticePaper.BothFreeRise FLatticePaper.Q24Instances

/-- **The chain monotonicity from the W1 classification (Q28 for the joint representative).** `Φ_η` does not increase along the sign-`η`
game, given the W1 forcing of the word's frame (`hW1word`) and, as the one explicit hypothesis, the joint free representative `hjoint` of
the two roots of every rising edge whose roots are not strict-interior centres (open question Q28). -/
theorem chain_nonincreasing_of_W1 (frame : ChildFrame) {F : Field} (G : CanonicalSignedGames frame F)
    (hS : frame.HasStrips F) {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hc : 3 ≤ frame.child.den - frame.child.num)
    (hlapF : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) (hU : HasUnitPrice frame F)
    (hW1word : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F)
    (hjoint : ∀ z u, (G.game η hη).policy z u → frame.chainPotential F η z < frame.chainPotential F η u →
      ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z →
      ¬ FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + η • frame.shortShift) →
      FreeRiseRep frame η z)
    (hdeck : ∀ z u (i j : ℤ), (G.game η hη).policy z u →
      (G.game η hη).policy (z - frame.child.modifiedDeck.combine i j) (u - frame.child.modifiedDeck.combine i j))
    (hdrift : ∀ i j : ℤ, ∃ c : ℤ, ∀ x,
      frame.chainPotential F η (x - frame.child.modifiedDeck.combine i j) = frame.chainPotential F η x + c) :
    NonincreasingAlong (frame.chainPotential F η) (G.game η hη).policy := by
  have hη' : -η = 1 ∨ -η = -1 := by omega
  refine chain_nonincreasing_of_free_roots frame G hS hη hc hlapF hU ?_ hdeck hdrift
  intro z u hu hrise
  obtain ⟨hn1, hn2⟩ := rise_roots_not_SI (G.game η hη) (G.game (-η) hη') hη hlapF hU hW1word hu hrise
  exact hjoint z u hu hrise hn1 hn2

end FLatticePaper.ChainW1
