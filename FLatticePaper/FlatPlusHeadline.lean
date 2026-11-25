import FLatticePaper.TraceHeadline
import FLatticePaper.Plane.Induction.TwosFlatPlus

/-! The odometers theorem with the sign `+1` flatness input supplied by the proof: `hflatP` is `TwosEPolicy.twos_flat_plus`
(the tile claim of sign `+1` at every centre). The named inputs are `hflatM`, `hgames` and `hW1`. -/

namespace FLatticePaper

open Farey Induction

theorem odometersTheorem_no_flatP
    (hflatM : ∀ k : ℕ, ∀ c i : Site, TwosEPolicy.TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) i < TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) c)
    (hgames : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → GamesWithRank word)
    (hW1 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      ¬ (∃ k : ℕ, conjWord word = List.replicate (k + 1) Digit.two) →
      W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word))) :
    OdometersTheorem :=
  odometersTheorem_no_hbd (fun k _ _ hT hΦ => TwosEPolicy.twos_flat_plus k hT hΦ) hflatM hgames hW1

end FLatticePaper
