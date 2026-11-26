import FLatticePaper.Plane.Induction.TieRankPeriods
import FLatticePaper.Plane.Induction.WestException
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.ChainWire
import FLatticePaper.Plane.Induction.PsiCalibration

/-! # The sheet policy keeps the south input at the exceptional vertex (`hSouth` of `hwest_freePolicy`, Q19)

Let `v = (N − D + 1, N + D − 1)` be the exceptional vertex of the word (`N/D` the odd parent), with `ε = +1`, so `lv = 0`. Under the zTurn chart,
`zTurn v = hFirst − K'` and `zTurn (incomingNeg v) = hFirst + (0, −1) − K'`, where `K' = (D + N, D − N)` is the conjugate kernel (Q19:
`Z(v) = (1,0) − U'`). The conjugate policy retains `hFirst + (0, −1)` at the free H origin `hFirst` (its prescription for sign `ε = +1`,
or both inputs if the origin is black), and it is invariant under the conjugate deck (`ChainWire.deck_of_games`). -/

namespace FLatticePaper.SouthPolicy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.TieRankPeriods FLatticePaper.W1Phase

/-- **The south input at the exceptional vertex.** With `ε = +1` and the policy `P.retained` of the canonical game `G`, the sheet policy `A`
at the exceptional vertex `v` keeps its south input `incomingNeg v`. -/
theorem sheetPolicyA_south {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (heps : (frameAt word).eps = 1) :
    sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) := by
  have hη : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  -- the conjugate's free H origin retains its south input `hFirst + (0, −1)`
  have hFree := FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt (conjWord word))
  have hsouth : incomingNeg FLatticePaper.Induction.hFirst = FLatticePaper.Induction.hFirst + (0, -1) := by
    simp [incomingNeg, EvenSite, FLatticePaper.Induction.hFirst]
  have hRet : P.retained FLatticePaper.Induction.hFirst (FLatticePaper.Induction.hFirst + (0, -1)) := by
    rcases hSE.packet.binary FLatticePaper.Induction.hFirst with hb | hw
    · rw [hW]
      rw [← hsouth]
      exact ((G.game (frameAt word).eps (frameAt word).eps_unit).quota.1 FLatticePaper.Induction.hFirst hb).1
    · rw [hW]
      have hp := (G.game (frameAt word).eps (frameAt word).eps_unit).prescribed.1 FLatticePaper.Induction.hFirst hFree hw (FLatticePaper.Induction.hFirst + (0, -1))
      refine hp.mpr ?_
      rw [ChildFrame.prescribedH_hFirst, heps]
  -- the deck invariance of the conjugate policy, with the conjugate kernel `combine 1 0`
  have hdeck := FLatticePaper.ChainWire.deck_of_games G hη P.toOldPolicyWitness hW 1 0
    FLatticePaper.Induction.hFirst (FLatticePaper.Induction.hFirst + (0, -1)) hRet
  have hk : (frameAt (conjWord word)).child.modifiedDeck.combine 1 0 =
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
    simp only [PeriodDeck.combine, conj_kernel word h, one_mul, zero_mul, add_zero]
  rw [hk] at hdeck
  -- the sheet side: lv = 0 at ε = 1, and the exceptional vertex is even
  have hlv : (frameAt word).sheetShift = 0 := FLatticePaper.PsiCalibration.sheetShift_W1 word heps
  have hv : EvenSite ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) := by
    unfold EvenSite
    simp only
    omega
  unfold sheetPolicyA parentPolicy
  rw [hlv, sub_zero, sub_zero]
  unfold incomingNeg
  rw [if_pos hv]
  have e1 : zTurn ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) =
      FLatticePaper.Induction.hFirst - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
    unfold zTurn FLatticePaper.Induction.hFirst
    ext <;> (simp; try ring)
  have e2 : zTurn ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 - 1,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) =
      (FLatticePaper.Induction.hFirst + (0, -1)) - ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
    unfold zTurn FLatticePaper.Induction.hFirst
    ext <;> simp <;> ring
  rw [e1, e2]
  exact hdeck

end FLatticePaper.SouthPolicy
