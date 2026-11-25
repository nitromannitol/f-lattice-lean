import FLatticePaper.Plane.Induction.StrongSeedInduction
import FLatticePaper.Plane.Induction.TraceStep
import FLatticePaper.Plane.Induction.ChainEnd
import FLatticePaper.Plane.Induction.ConjBase
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.PsiArc
import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.TwosField
import FLatticePaper.Plane.Induction.PureRow
import FLatticePaper.Plane.Induction.ThreesGames
import FLatticePaper.Plane.Induction.TwosTrace
import FLatticePaper.Plane.Induction.PureTrace

/-! Task w3, step D: the strong estimates, the seed fields and the trace of every word, by one induction, with the boundary
bound `hbd` derived from the trace (no `hbd` input).

The predicate `TraceSeeds w` is `StrongEstimates w ∧ SeedFields w ∧ TraceAt w ∧ StrongEstimates (conjWord w) ∧ TraceAt (conjWord w)`:
`word_induction` supplies the last two components of the conjugate, which the step needs (`hSE'`, `hTrace'`).

Named inputs (the base and the all-threes row, to be discharged by B):
* the traces of the pure words (`PureTrace.traceAt_threes`) and of the two-powers (`TwosTrace.traceAt_twos`) are proved;
The minus row at a pure conjugate (`PureRow.rowThrees_of_conj`) and the games at the pure words (`gamesWithRank_threes`) are
proved; they are not inputs. -/

namespace FLatticePaper.TraceSeedInduction

open Farey FLatticePaper FLatticePaper.Induction

/-- The strong estimates, the seeds and the traces of a word, with those of its conjugate. -/
def TraceSeeds (w : Word) : Prop :=
  StrongEstimates w ∧ W1Seeds.SeedFields w ∧ TraceFromPsi.TraceAt w ∧
    StrongEstimates (conjWord w) ∧ TraceFromPsi.TraceAt (conjWord w)

/-- Games with a deck rank at every word that is not pure and not a two-power; at the pure and two-power words they are
given by their own families. -/
theorem gamesWithRank_any (hgames : ∀ X : Word, (∃ x ∈ X, x ≠ Digit.three) → ¬ IsTwoPow X → GamesWithRank X)
    (htwoGames : ∀ k : ℕ, GamesWithRank (List.replicate (k + 1) Digit.two))
    (X : Word) : GamesWithRank X := by
  by_cases hp : ∃ k : ℕ, X = List.replicate k Digit.three
  · obtain ⟨k, rfl⟩ := hp
    exact gamesWithRank_threes k
  · by_cases hq : IsTwoPow X
    · obtain ⟨k, rfl⟩ := hq
      exact htwoGames k
    · exact hgames X (exists_ne_three_of_not_replicate_three X hp) hq

/-- **The strong estimates, the seeds and the traces of every word.** -/
theorem traceSeeds_of_all
    (hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two))
    (hgames : ∀ X : Word, (∃ x ∈ X, x ≠ Digit.three) → ¬ IsTwoPow X → GamesWithRank X)
    (htwoGames : ∀ k : ℕ, GamesWithRank (List.replicate (k + 1) Digit.two))
    : ∀ word : Word, TraceSeeds word := by
  refine word_induction (P := TraceSeeds) ?_ ?_
  · intro k
    have hc : conjWord (List.replicate k Digit.three) = [] := ConjBase.conjWord_threes k
    refine ⟨hpure k, W1BaseSeeds.seedFields_threes k, PureTrace.traceAt_threes k, ?_, ?_⟩
    · rw [hc]
      exact hpure 0
    · rw [hc]
      exact PureTrace.traceAt_threes 0
  · intro word hproper ih
    obtain ⟨hS, hpar, hTW, hSE', hTrace'⟩ := ih
    by_cases hI : IsTwoPow word
    · obtain ⟨k, rfl⟩ := hI
      have hc : conjWord (List.replicate (k + 1) Digit.two) = List.replicate k Digit.three :=
        conjWord_replicate_two k
      refine ⟨htwo k, W1BaseSeeds.seedFields_two_succ k (hpure k), TwosTrace.traceAt_twos k, ?_, ?_⟩
      · rw [hc]
        exact hpure k
      · rw [hc]
        exact PureTrace.traceAt_threes k
    · -- the proper, non-two-power word: the trace step, then the residual and the estimates
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
      obtain ⟨P, R, cU, cV, hPres, -, hNon, -, -, -, -, -⟩ :=
        policy_of_gamesWithRank_prescribed (gamesWithRank_any hgames htwoGames (conjWord word))
      have hEnd := fun (hη : (frameAt word).eps = 1) =>
        ChainEnd.hEnd_of_chain_row hproper hS hTW hη base hbase hrowM H N hHmem hHabs P hPres hNon
      have hT : TraceFromPsi.TraceAt word :=
        TraceStep.traceAt_step_row hproper hS hTW base hbase hrowM H N hHmem hHabs hcover hN2 hN hEnd
      have hbd := TraceStep.hbd_of_traceAt hproper hS hT
      have hR : StrongResidual word :=
        strongResidual_of_conj hproper (exists_ne_two_of_not_twoPow hproper hI) hS hbd hpar
          (policy_of_gamesWithRank (hgames word hproper hI))
      exact ⟨strongEstimates_step_strong hproper hS hR, W1SeedFields.seedFields_of_conj hproper hS hpar, hT, hS, hTW⟩

/-- **The boundary bound of every proper non-two-power word, from the trace induction** (no `hbd` input). -/
theorem hbd_of_traceSeeds
    (hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three))
    (htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two))
    (hgames : ∀ X : Word, (∃ x ∈ X, x ≠ Digit.three) → ¬ IsTwoPow X → GamesWithRank X)
    (htwoGames : ∀ k : ℕ, GamesWithRank (List.replicate (k + 1) Digit.two))
    : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → ¬ IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice := by
  intro word hw hn
  have hT := traceSeeds_of_all hpure htwo hgames htwoGames word
  exact TraceStep.hbd_of_traceAt hw hT.2.2.2.1 hT.2.2.1

end FLatticePaper.TraceSeedInduction
