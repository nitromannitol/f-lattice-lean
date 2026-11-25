import FLatticePaper.TraceHeadline
import FLatticePaper.Plane.Induction.TwosFlatMinus

/-! The odometers theorem with both twos flatness inputs supplied by the proof: `hflatP` is `TwosEPolicy.twos_flat_plus` and
`hflatM` is `TwosEPolicy.twos_flat_minus`. The named inputs are `hgames` and `hW1`. -/

namespace FLatticePaper

open Farey Induction

theorem odometersTheorem_no_flat
    (hgames : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word → GamesWithRank word)
    (hW1 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      ¬ (∃ k : ℕ, conjWord word = List.replicate (k + 1) Digit.two) →
      W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word))) :
    OdometersTheorem :=
  odometersTheorem_no_hbd (fun k _ _ hT hΦ => TwosEPolicy.twos_flat_plus k hT hΦ)
    (fun k _ _ hT hΦ => TwosEPolicy.twos_flat_minus k hT hΦ) hgames hW1

end FLatticePaper
