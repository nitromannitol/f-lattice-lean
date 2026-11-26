import FLatticePaper.FlatMinusHeadline
import FLatticePaper.Plane.Induction.StrongCore

/-! # The odometers theorem from the two induction steps

The named inputs `hgames` and `hW1` of `odometersTheorem_no_flat` are statements about every word. Their proofs at a word use
the data of the conjugate word (its strong estimates, seed fields, trace, games and `W1Forced`) and the fields of the strong
estimates of the word that do not depend on its own policy (`StrongCore`). So they are proved inside one word induction.

`GamesStep` and `W1Step` are the two induction steps: at a proper word that is not a two-power, the games with a deck rank and
the W1 forcing of the word, from the conjugate's data and the current core. `bundle_all` runs the induction (the trace step and
the residual are those of `TraceSeedInduction.traceSeeds_of_all`; the pure words and the two-powers are the proved base
families), and `odometersTheorem_of_steps` gives the headline with the two steps as its only named inputs. -/

namespace FLatticePaper.StepHeadline

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.TraceSeedInduction

/-- The W1 forcing of the standard field of a word, at its own child frame. -/
def W1At (w : Word) : Prop :=
  FLatticePaper.W1.W1Forced (frameAt w).child.num (frameAt w).child.den (standardField w)

/-- **The games step**: at a proper word that is not a two-power, the games with a deck rank, from the conjugate's data, the
current core, seed fields and trace, and the W1 forcing of the word and of its conjugate. -/
def GamesStep : Prop :=
  ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
    StrongCore word → W1Seeds.SeedFields word → TraceFromPsi.TraceAt word →
    StrongEstimates (conjWord word) → W1Seeds.SeedFields (conjWord word) → TraceFromPsi.TraceAt (conjWord word) →
    GamesWithRank (conjWord word) → W1At (conjWord word) → W1At word → GamesWithRank word

/-- **The W1 step**: at a proper word that is not a two-power, the W1 forcing of the word, from the conjugate's data and the
current core, seed fields and trace. -/
def W1Step : Prop :=
  ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
    StrongCore word → W1Seeds.SeedFields word → TraceFromPsi.TraceAt word →
    StrongEstimates (conjWord word) → W1Seeds.SeedFields (conjWord word) → TraceFromPsi.TraceAt (conjWord word) →
    GamesWithRank (conjWord word) → W1At (conjWord word) → W1At word

/-- The data carried by the induction: the strong estimates, seeds and traces (with the conjugate's), the games with a deck
rank, and the W1 forcing. -/
def StepBundle (w : Word) : Prop :=
  TraceSeeds w ∧ GamesWithRank w ∧ W1At w

theorem strong_threes (k : ℕ) : StrongEstimates (List.replicate k Digit.three) :=
  StrongEstimates.of_base_pure k (EPolicy.pure_threes_inputs.1 k) (EPolicy.pure_threes_inputs.2 k)

theorem games_twos (k : ℕ) : GamesWithRank (List.replicate (k + 1) Digit.two) :=
  TwosEPolicy.twos_gamesWithRank k (fun _ _ hT hΦ => TwosEPolicy.twos_flat_plus k hT hΦ)
    (fun _ _ hT hΦ => TwosEPolicy.twos_flat_minus k hT hΦ)

theorem strong_twos (k : ℕ) : StrongEstimates (List.replicate (k + 1) Digit.two) :=
  StrongEstimates.of_base_two k (twos_baseSlip k) (strongResidual_twos_of_games k (games_twos k))

theorem w1_threes (k : ℕ) : W1At (List.replicate k Digit.three) :=
  FLatticePaper.W1Reciprocal.w1Forced_threes k

theorem w1_twos (k : ℕ) : W1At (List.replicate (k + 1) Digit.two) := by
  unfold W1At
  rw [(Induction.twos_child_num_den k).1, (Induction.twos_child_num_den k).2]
  exact FLatticePaper.W1Twos.twos_W1Forced k

/-- **The induction**: every word carries its strong estimates, seeds, traces, games with a deck rank and W1 forcing. -/
theorem bundle_all (hG : GamesStep) (hW : W1Step) : ∀ word : Word, StepBundle word := by
  refine word_induction (P := StepBundle) ?_ ?_
  · intro k
    have hc : conjWord (List.replicate k Digit.three) = [] := ConjBase.conjWord_threes k
    refine ⟨⟨strong_threes k, W1BaseSeeds.seedFields_threes k, PureTrace.traceAt_threes k, ?_, ?_⟩,
      gamesWithRank_threes k, w1_threes k⟩
    · rw [hc]
      exact strong_threes 0
    · rw [hc]
      exact PureTrace.traceAt_threes 0
  · intro word hproper ih
    obtain ⟨⟨hS, hpar, hTW, hSE', hTrace'⟩, hGc, hW1c⟩ := ih
    by_cases hI : IsTwoPow word
    · obtain ⟨k, rfl⟩ := hI
      have hc : conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three :=
        conjWord_replicate_two k
      refine ⟨⟨strong_twos k, W1BaseSeeds.seedFields_two_succ k (strong_threes k), TwosTrace.traceAt_twos k, ?_, ?_⟩,
        games_twos k, w1_twos k⟩
      · rw [hc]
        exact strong_threes k
      · rw [hc]
        exact PureTrace.traceAt_threes k
    · -- the trace step (as in `traceSeeds_of_all`), with the conjugate's games from the induction
      obtain ⟨base, hbase⟩ := PsiArc.conj_base_exists word
      obtain ⟨H, N, hN2, hNd, hHmem, hHabs, hcover⟩ := ConjBase.freeH_enum_N (frameAt word)
      have hN : (N : ℤ) ≤ (frameAt word).child.den := le_of_eq hNd
      have hrowM : StepTwoC.RawRow
          (fun i => EndpointDeck.Dq (frameAt (conjWord word)) (standardField (conjWord word)) (-1)
            (FreeEnum.vAt (frameAt (conjWord word)) base i)) (-1)
          ((frameAt (conjWord word)).parents.odd.den + (frameAt (conjWord word)).parents.odd.num)
          (FreeEnum.period (frameAt (conjWord word))) := by
        by_cases hX : ∃ x ∈ conjWord word, x ≠ Digit.three
        · exact RowMinus.rowMinus hX hS hSE' hTrace' base hbase
        · exact PureRow.rowThrees_of_conj (conjWord word) (fun x hx => by by_contra hne; exact hX ⟨x, hx, hne⟩) base hbase
      obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ := policy_of_gamesWithRank_prescribed hGc
      have hEnd := fun (hη : (frameAt word).eps = 1) =>
        ChainEnd.hEnd_of_chain_row hproper hS hTW hη base hbase hrowM H N hHmem hHabs P hPres hNon
      have hT : TraceFromPsi.TraceAt word :=
        TraceStep.traceAt_step_row hproper hS hTW base hbase hrowM H N hHmem hHabs hcover hN2 hN hEnd
      have hbd := TraceStep.hbd_of_traceAt hproper hS hT
      have h2 := exists_ne_two_of_not_twoPow hproper hI
      -- the core, the seeds, the W1 forcing and the games of the word, then its residual
      have hcore : StrongCore word := strongCore_of_conj hproper h2 hS hbd hpar
      have hseed : W1Seeds.SeedFields word := W1SeedFields.seedFields_of_conj hproper hS hpar
      have hW1w : W1At word := hW word hproper hI hcore hseed hT hS hpar hTW hGc hW1c
      have hGw : GamesWithRank word := hG word hproper hI hcore hseed hT hS hpar hTW hGc hW1c hW1w
      have hR : StrongResidual word :=
        strongResidual_of_conj hproper h2 hS hbd hpar (policy_of_gamesWithRank hGw)
      exact ⟨⟨strongEstimates_step_strong hproper hS hR, hseed, hT, hS, hTW⟩, hGw, hW1w⟩

/-- **The odometers theorem from the two induction steps.** -/
theorem odometersTheorem_of_steps (hG : GamesStep) (hW : W1Step) : OdometersTheorem :=
  odometersTheorem_no_flat (fun word _ _ => (bundle_all hG hW word).2.1)
    (fun word _ _ _ _ => (bundle_all hG hW (conjWord word)).2.2)

end FLatticePaper.StepHeadline
