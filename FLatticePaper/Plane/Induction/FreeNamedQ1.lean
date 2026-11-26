import FLatticePaper.Plane.Induction.GamesAssembly
import FLatticePaper.Plane.Induction.FreePermittedS
import FLatticePaper.Plane.Induction.OddBlackStep
import FLatticePaper.Plane.Induction.ForcedPriceSI
import FLatticePaper.Plane.Induction.HfreePhase1
import FLatticePaper.Plane.Induction.WordPolicy
import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.W1StepAssembly
import FLatticePaper.Plane.Induction.ForcedPermitAll
import FLatticePaper.Plane.Induction.CornerN1
import FLatticePaper.Plane.Induction.RiseInput

/-! # The free-policy named inputs of the games step, from the Q1 rank (`hN` of `gamesWithRank_of_Q1`)

For a sign `η` and a rank `R` that is constrained for `permitsQ1` and strict along `freePolicy`, the four fields of
`FreeNamedInputs` come from:

* `permitted`: `permitted_Q1` (black: `OddBlackNoRise`, free H and V: the proved permits, as in `FreePermittedS.permitted_S`). The
  nonfree white case is the forced permit `hforced`: the slip permit of the forced edge, for both signs. `permitted_S` derived it from the
  aux rank; here it is the named input `hforced` (the Q34 theorem, not yet assembled).
* `nonincreasingP`: `ForcedPriceSI.word_price_nonincreasing_SI` with `hsat` from the Q1 rank (`AuxRankQ1.hasSat_of_constrained`) and
  `hfreeP` from `HfreePhase1.hfreeP_of_phases`, whose corner input is `hcorner`.
* `nonincreasingJ`: `WordPolicy.word_J_nonincreasing` from the slip inequality of the permit.
* `strictRank`: the hypothesis `hstrict` of the Q1 rank.
* `westAtException`: the named input `hwest`.

`gamesStep_of_noFort` is `gamesWithRank_of_Q1` with `hN := freeNamedInputs_of_Q1`; the explicit inputs are `hno` and the three
named inputs `hforced`, `hcorner`, `hwest`, together with the conjugate's data. -/

namespace FLatticePaper.FreeNamedQ1

open FLatticePaper.W1Phase
open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.AuxRankSign FLatticePaper.FreeClosure
  FLatticePaper.AuxRank FLatticePaper.SquareClauses FLatticePaper.FreePermittedS FLatticePaper.AuxRankQ1
  FLatticePaper.GamesAssembly

/-- **The `permitted` field from the Q1 rank.** As `FreePermittedS.permitted_S`, with the nonfree white case given by the forced
permit `hforced`. -/
theorem permitted_Q1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word))
    (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {η : ℤ} (hη : η = 1 ∨ η = -1)
    (hforced : ∀ c o : Site, ¬ freeClosure (frameAt word) c → laplacian (standardField word) c = 0 →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c o) :
    ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c i := by
  intro c i hci
  rw [FreePermitted.slipPermits_iff_slip]
  have hex := forcedExists_of (frameAt word) hW.packet hW1
  have hI := CanonicalPermit.standardField_reflect_core hW
  have hn3 := child_num_ge_three h
  have hσ := evenSite_shortShift (frameAt word)
  unfold freePolicy at hci
  rcases hci with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · -- black edge
    rcases hη with rfl | rfl
    · have key := black_permit_plus (F := standardField word) (σ := (frameAt word).shortShift) hσ hW.packet.binary
        hW.F1_unitSlip hW.F1_noSlipSaddle hOdd hl hE
      unfold slipPermits slipIncrement at key
      dsimp only at key
      unfold ChildFrame.slip
      simp only [one_smul]
      linarith
    · have key := black_permit_neg (F := standardField word) (σ := (frameAt word).shortShift) hσ hW.packet.binary
        hW.F1_unitSlip hW.F1_noSlipSaddle hOdd hI hl hE
      unfold slipPermits slipIncrement at key
      dsimp only at key
      unfold ChildFrame.slip
      simp only [neg_one_smul] at key ⊢
      linarith
  · -- free white
    obtain ⟨t, ht, hcase⟩ := hp
    rcases hcase with ⟨hH, hi⟩ | ⟨hV, hi⟩
    · exact SlipPermitH2.slip_permit_H (frameAt word) hW.packet.periods hW.packet.strips hn3 hη ht hH hi
    · exact FreePermitted.slip_le_of_translate hW η ht rfl (by rw [hi]; abel)
        (freeV_permit_S h hW hSE G hη hV)
  · -- nonfree white: the forced edge, from the named forced permit
    rw [hs]
    have key := hforced c (forcedSel (standardField word) c) hn hl (forcedSel_spec (hex c hn hl))
    exact (FreePermitted.slipPermits_iff_slip η c (forcedSel (standardField word) c)).mp key

/-- **The free-policy named inputs of sign `η` from the Q1 rank.** The only inputs beyond the games data are `hforced`, `hcorner` and
`hwest` (see the module header). -/
theorem freeNamedInputs_of_Q1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hWord : StrongCore word)
    (hSE : StrongEstimates (conjWord word)) (hG : GamesWithRank (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hW1c : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {η : ℤ} (hη : η = 1 ∨ η = -1) {R : Site → ℤ}
    (hcon : IsConstrainedBurningRank (standardField word) R (permitsQ1 (frameAt word) (standardField word) η))
    (hstrict : ∀ c i, freePolicy (frameAt word) (standardField word) η c i → R i < R c)
    (hforced : ∀ c o : Site, ¬ freeClosure (frameAt word) c → laplacian (standardField word) c = 0 →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c o)
    (hcorner : (frameAt word).eps = 1 → η = -1 → (frameAt word).parents.odd.num = 1 →
      FLatticePaper.W1Step.sheetPsi word (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0 ∧
        (frameAt word).sheetA (FLatticePaper.W1MSheet.FqW word)
          (FLatticePaper.ArcPsi.reflH word (FLatticePaper.Induction.hFirst + (0, -η))) = 0)
    (hwest : (frameAt word).eps = 1 → freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1))) :
    FreeNamedInputs (frameAt word) (standardField word) η R := by
  obtain ⟨G⟩ := games_of_gamesWithRank hG
  have hOdd : OddBlackNoRise (standardField word) (frameAt word).shortShift :=
    OddBlackStep.oddBlackNoRise_step h hWord hSE hG hpar hW1c
  obtain ⟨base, hbase⟩ := HfreePhase1.conj_base (frameAt (conjWord word))
  have hperm := permitted_Q1 h hWord hSE G hOdd hW1 hη hforced
  have hslip : ∀ c i, freePolicy (frameAt word) (standardField word) η c i →
      (frameAt word).slip (standardField word) η i ≤ (frameAt word).slip (standardField word) η c := by
    intro c i hci
    exact (FreePermitted.slipPermits_iff_slip η c i).mp (hperm c i hci)
  have hfreeP : ∀ c i, laplacian (standardField word) c = 0 → freeClosure (frameAt word) c →
      FreePresc (frameAt word) η c i →
      (frameAt word).price (standardField word) i ≤ (frameAt word).price (standardField word) c :=
    fun _ _ _ _ hcp => HfreePhase1.hfreeP_of_phases h hSE hG hbase hη hcorner hcp
  have hsat : HasSatSelection (standardField word) :=
    AuxRankQ1.hasSat_of_constrained hWord.packet.binary hcon
  exact
    { permitted := hperm
      nonincreasingP := fun c i hci => by
        have hm := ForcedPriceSI.word_price_nonincreasing_SI word h hSE hWord hW1 hsat η hfreeP c i hci
        rw [cutGrade_one_zero_one, cutGrade_one_zero_one]
        exact hm
      nonincreasingJ := WordPolicy.word_J_nonincreasing word η hslip
      strictRank := hstrict
      westAtException := hwest }

/-- **The games step with the Q1 rank.** `gamesWithRank_of_Q1` with `hN := freeNamedInputs_of_Q1`: the explicit inputs are `hno` and
the named forced, corner and west inputs, for both signs. -/
theorem gamesStep_of_noFort {word : Word} (h2 : ∃ x ∈ word, x ≠ Digit.two) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hcore : StrongCore word) (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (hSE : StrongEstimates (conjWord word)) (hG : GamesWithRank (conjWord word))
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hTr : FLatticePaper.TraceFromPsi.TraceAt (conjWord word))
    (hW1c : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hno : ∀ η : ℤ, (η = 1 ∨ η = -1) →
      RestrictedNoFort (standardField word)
        (fun z => (frameAt word).price (standardField word) z + (frameAt word).roundedSlip (standardField word) η z)
        (permitsQ1 (frameAt word) (standardField word) η))
    (hRow : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy →
          CollarChain.RowFaceStrictHyp word (standardField (conjWord word)) P.retained)
    (hDich : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → CollarChain.WitnessDichotomy word) :
    GamesWithRank word :=
  gamesWithRank_of_Q1 h2 hcore hW1 hno
    (fun η hη _ hcon hstrict => by
      have hsat := AuxRankQ1.hasSat_of_constrained hcore.packet.binary hcon
      obtain ⟨G, P, hWP, hsheet⟩ := FLatticePaper.W1StepAssembly.sheetOut_forced_of_parts hRow hDich word h
        hcore hseed hSE hpar hG hW1c hsat
      have hrise := FLatticePaper.RiseInput.noRise_of_canonical h hSE hTr hW1c P.toOldPolicyWitness G hWP
      exact freeNamedInputs_of_Q1 h hcore hSE hG hpar hW1c hW1 hη hcon hstrict
        (FLatticePaper.ForcedPermitAll.forced_slip_permit h hcore hSE P hsheet hsat hW1 hrise η hη)
        (fun hW1' hη1 hN => FLatticePaper.CornerN1.corner_N1 h hSE hpar hW1' hN η hη1)
        (by
          have hh := FLatticePaper.W1StepAssembly.westFree_of_parts hRow hDich word h hcore hseed hSE hpar hG
            hW1c (AuxRankQ1.hasSat_of_constrained hcore.packet.binary hcon) η
          have e : (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1 =
              (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by ring
          rw [e] at hh
          exact hh))

end FLatticePaper.FreeNamedQ1
