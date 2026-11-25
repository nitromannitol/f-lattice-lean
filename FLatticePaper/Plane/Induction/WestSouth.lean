import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.WestNonfree

/-! `hSouth` from the deck equivariance of the conjugate's canonical game.

For `ε = 1`, the parent policy of the conjugate retains, at `zTurn v` (`v` the exceptional vertex), the south input `zTurn(west)`.
Proof: `PrescribedAt` at the free H root `hFirst` gives the south step `(0, −1)`; the deck equivariance of the game (the field
`CanonicalSignedGames.deckEquiv`) with the deck vector `combine (−1) 0 = −U'` transports it to `hFirst + combine (−1) 0`, and
`zTurn v = hFirst + combine (−1) 0`, `zTurn west = zTurn v + (0, −1)` by the conjugate's child fraction (`frameAt_conj_num_den`). -/

namespace FLatticePaper.WestSouth

open Farey FLatticePaper FLatticePaper.Induction

theorem south_of_game {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (heps : (frameAt word).eps = 1) (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {η : ℤ} (hη : η = 1 ∨ η = -1) (heta : η = 1) :
    (G.game η hη).policy (zTurn (FLatticePaper.WestNonfree.excVertex word - (frameAt word).sheetShift))
      (zTurn (incomingNeg (FLatticePaper.WestNonfree.excVertex word) - (frameAt word).sheetShift)) := by
  subst heta
  -- the shift is zero at ε = 1
  have hsh : (frameAt word).sheetShift = 0 := by
    unfold ChildFrame.sheetShift ChildFrame.phaseW
    rw [heps]
    norm_num
  rw [hsh, sub_zero, sub_zero]
  have hF0 : hFirst ∈ (frameAt (conjWord word)).freeH := PsiMonoOffset.hFirst_mem_freeH (frameAt (conjWord word))
  have hlap0 : laplacian (standardField (conjWord word)) hFirst = 0 :=
    laplacian_eq_zero_of_freeH (frameAt (conjWord word)) hSE.packet.strips hF0
  -- the south step at hFirst (PrescribedAt, sign +1)
  have hA : (G.game 1 hη).policy hFirst (hFirst + (0, -1)) := by
    rw [(G.game 1 hη).prescribed.1 hFirst hF0 hlap0 (hFirst + (0, -1))]
    rw [ChildFrame.prescribedH_hFirst]
  -- transport by the deck vector combine (−1) 0 = −U'
  have hB := G.deckEquiv 1 hη (-1) 0 hFirst (hFirst + (0, -1))
  -- the coordinates of the exceptional vertex and its left neighbour in the conjugate frame
  obtain ⟨hnum, hden⟩ := frameAt_conj_num_den h
  have hvE : EvenSite (FLatticePaper.WestNonfree.excVertex word) := by
    unfold EvenSite FLatticePaper.WestNonfree.excVertex
    have e : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 +
        ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) = 2 * (frameAt word).parents.odd.num := by ring
    simp only [e]
    omega
  have e1 : zTurn (FLatticePaper.WestNonfree.excVertex word) = hFirst + (frameAt (conjWord word)).child.modifiedDeck.combine (-1) 0 := by
    rw [ChildFrame.combine_coords]
    unfold zTurn FLatticePaper.WestNonfree.excVertex
    simp only [hnum, hden, Prod.ext_iff, Prod.fst_add, Prod.snd_add, hFirst]
    constructor <;> ring
  have e2 : zTurn (incomingNeg (FLatticePaper.WestNonfree.excVertex word)) =
      (hFirst + (0, -1)) + (frameAt (conjWord word)).child.modifiedDeck.combine (-1) 0 := by
    unfold incomingNeg
    rw [if_pos hvE]
    rw [ChildFrame.combine_coords]
    unfold zTurn FLatticePaper.WestNonfree.excVertex
    simp only [hnum, hden, Prod.ext_iff, Prod.fst_add, Prod.snd_add, hFirst]
    constructor <;> ring
  rw [e1, e2]
  exact hB.mp hA

/-- **`hSouth`**: for a parent datum whose retained policy is the conjugate's canonical policy of sign `η`, the A-policy at the
exceptional vertex retains the west input (`sheetPolicyA P sheetShift v (incomingNeg v)`). -/
theorem hSouth_of_retained {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (heps : (frameAt word).eps = 1) (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    {η : ℤ} (hη : η = 1 ∨ η = -1) (heta : η = 1) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed η)
    (hret : P.retained = (G.game η hη).policy) :
    sheetPolicyA P (frameAt word).sheetShift (FLatticePaper.WestNonfree.excVertex word)
      (incomingNeg (FLatticePaper.WestNonfree.excVertex word)) := by
  unfold sheetPolicyA parentPolicy
  rw [hret]
  exact south_of_game h hSE heps G hη heta

end FLatticePaper.WestSouth
