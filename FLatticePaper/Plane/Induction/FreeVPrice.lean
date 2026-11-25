import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.WordPolicy

/-! hfreeP, the V case, on the star. For a free V white `r` whose prescribed input `r + prescribedV η r` lies on the same star as `r`
(`StarS` on both sgrades), the primitive price is equal at the two sites: `price_const_on_star_of_word`. The star condition fails for about
12% of the free V whites (numerically, proper words of length at most five); those are the whole-star cases of Q13, not covered here. -/

namespace FLatticePaper.FreeVPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.BothFreeGrades

/-- **The V prescribed neighbour has the price of the free V white, on the star.** -/
theorem freeV_price_star (word : Farey.Word) (hprop : ∃ x ∈ word, x ≠ Digit.three) (hnot : ¬ IsTwoPow word)
    (hS : (frameAt word).HasStrips (standardField word)) {η : ℤ} {r : Site}
    (hzs : StarS (frameAt word) ((frameAt word).sGrade r))
    (hus : StarS (frameAt word) ((frameAt word).sGrade (r + (frameAt word).prescribedV η r))) :
    (frameAt word).price (standardField word) (r + (frameAt word).prescribedV η r) =
      (frameAt word).price (standardField word) r :=
  price_const_on_star_of_word word hprop hnot (standardField word) hS hzs hus

end FLatticePaper.FreeVPrice
