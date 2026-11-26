import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.StrongCore

/-! # The word's field is `h₀` on the sites of the opposite collar (word frame)

For the word `u` itself (not its conjugate), with `StrongCore u` (packet, price range, price drift) and `SeedFields u`:

* odd `z` with `2 − 3 den + num ≤ s(z) ≤ 1 − 2 den`: `W1Lower.lower_odd_h0` on the word frame;
* odd `z` with `den + num − 2 < s(z) ≤ 3 den + num − 2`: `W1Strips.V_side_full` on the word frame, with the reflection
  `iRefl_core` (the packet alone gives it);
* any `z` with `1 − 2 den ≤ s(z) ≤ 2 (den + num) − 1`: the harmonic strip of the packet (`HasStrips.2`).

Together: odd `z` with `2 − 3 den + num ≤ s(z) ≤ 3 den + num − 2` has `F z = h₀ z`. -/

namespace FLatticePaper.OppWordCover

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1Seeds

/-- The reflection of the word's field, from its packet alone (the core of `standardField_iRefl`). -/
theorem iRefl_core {u : Word} (h : StrongCore u) (z : Site) :
    standardField u (iRefl z) = standardField u z := by
  rw [iRefl_eq_sub]
  exact packet_reflection_I (frameAt u) h.packet z

/-- The word's lower odd `h₀` interval. -/
theorem word_odd_lower {word : Word} (hS : StrongCore word) (hpar : SeedFields word) (z : Site) (hz : ¬ EvenSite z)
    (hlo : 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z)
    (hhi : (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den) :
    standardField word z = harmonicGrid z :=
  W1Lower.lower_odd_h0 (frameAt word) hS.packet.strips hS.priceRange
    (fun w => by have := (hS.priceDrift w).1; linarith)
    (fun w => by have := (hS.priceDrift w).2; linarith)
    (fun w hw hs => SeedFields.odd_bottom hpar w hw hs) z hz hlo hhi

/-- The word's upper odd `h₀` interval `(den + num − 2, 3 den + num − 2]`, from the lower one by the reflection. -/
theorem word_odd_upper {word : Word} (hS : StrongCore word) (hpar : SeedFields word) (z : Site) (hz : ¬ EvenSite z)
    (hlo : (frameAt word).child.den + (frameAt word).child.num - 2 < (frameAt word).sGrade z)
    (hhi : (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    standardField word z = harmonicGrid z :=
  W1Strips.V_side_full (frameAt word) (F := standardField word) hS.packet.strips (iRefl_core hS)
    (fun z hz' h1 h2 => word_odd_lower hS hpar z hz' h1 h2) z hz hlo hhi

/-- The word's harmonic strip (any parity). -/
theorem word_strip {word : Word} (hS : StrongCore word) (z : Site)
    (h1 : 1 - 2 * (frameAt word).child.den ≤ (frameAt word).sGrade z)
    (h2 : (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    standardField word z = harmonicGrid z :=
  hS.packet.strips.2 z h1 h2

/-- **The odd sites of the opposite collar.** An odd site whose `s` lies in `[2 − 3 den + num, 3 den + num − 2]` has
the word's field equal to `h₀`. -/
theorem word_odd_cover {word : Word} (hS : StrongCore word) (hpar : SeedFields word) (z : Site) (hz : ¬ EvenSite z)
    (hL : -1 ≤ (frameAt word).child.den + (frameAt word).child.num)
    (hlo : 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z)
    (hhi : (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    standardField word z = harmonicGrid z := by
  by_cases h1 : (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den
  · exact word_odd_lower hS hpar z hz hlo h1
  · by_cases h2 : (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1
    · exact word_strip hS z (by omega) h2
    · exact word_odd_upper hS hpar z hz (by omega) hhi

end FLatticePaper.OppWordCover
