import FLatticePaper.CanonicalHeadline
import FLatticePaper.Plane.Induction.TraceSeedInduction
import FLatticePaper.Plane.Induction.ThreesGames

/-! Task w3, step D end: the odometers headline with the boundary bound `hbd` derived from the trace induction.

`odometersTheorem_no_hbd` is `odometersTheorem_of_canonical` with its `hbd` argument supplied by
`TraceSeedInduction.hbd_of_traceSeeds`. The named input is the trace at the two-power words (`hTraceTwos`). The trace at the pure words, the all-threes conjugate row and
the games at the pure words are proved. The existing inputs of the headline (`hflatP`, `hflatM`, `hgames`, `hW1`) are unchanged.
-/

namespace FLatticePaper

open Farey Induction

theorem odometersTheorem_no_hbd
    (hflatP : ∀ k : ℕ, ∀ c i : Site, TwosEPolicy.TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) 1 i < TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) 1 c)
    (hflatM : ∀ k : ℕ, ∀ c i : Site, TwosEPolicy.TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) i < TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) c)
    (hgames : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → GamesWithRank word)
    (hTraceThrees : ∀ k : ℕ, TraceFromPsi.TraceAt (List.replicate k Digit.three))
    (hTraceTwos : ∀ k : ℕ, TraceFromPsi.TraceAt (List.replicate (k + 1) Digit.two))
    (hW1 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      ¬ (∃ k : ℕ, conjWord word = List.replicate (k + 1) Digit.two) →
      W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word))) :
    OdometersTheorem := by
  have htwoGames : ∀ k : ℕ, GamesWithRank (List.replicate (k + 1) Digit.two) :=
    fun k => TwosEPolicy.twos_gamesWithRank k (hflatP k) (hflatM k)
  have hpure : ∀ k : ℕ, StrongEstimates (List.replicate k Digit.three) :=
    fun k => StrongEstimates.of_base_pure k (EPolicy.pure_threes_inputs.1 k) (EPolicy.pure_threes_inputs.2 k)
  have htwo : ∀ k : ℕ, StrongEstimates (List.replicate (k + 1) Digit.two) :=
    fun k => StrongEstimates.of_base_two k (twos_baseSlip k) (strongResidual_twos_of_games k (htwoGames k))
  have hbd := TraceSeedInduction.hbd_of_traceSeeds hpure htwo hTraceThrees hTraceTwos hgames htwoGames
  exact odometersTheorem_of_canonical EPolicy.pure_threes_inputs.1 EPolicy.pure_threes_inputs.2 htwoGames hgames hbd hW1

end FLatticePaper
