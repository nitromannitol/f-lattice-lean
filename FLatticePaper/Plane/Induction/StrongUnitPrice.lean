import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.StrongHSpan

/-! Task 67, STRONG_PRICE §§1–3 (the unit and no-saddle fields): `HasUnitPrice` and `NoPriceSaddle` of the primitive price.

Both fields follow from one statement about each full star: the three sites of the star of `c` (`c`, `incomingNeg c`, `incomingPos c`)
have their primitive prices in an interval of length one. Then every edge increment lies in `[−1, 1]`, and a saddle (opposite unit increments
at the centre) would force two star values at distance `2`, which is impossible.

Each site of a star is of one of three kinds, and each kind gives `P ∈ [c₀ − 1, c₀]`:
* an interior site of `E` (the price range, `StrongPriceRange.priceRange_of_recurrent`);
* an H-band site (`StrongHSpan.price_on_HStar`, the single two-level span);
* a V site whose two sources are the harmonic grid (`StrongPriceValues.price_eq_cutPrice_of_harmonic`, the value `c₀`).
The classification of the sites of the full stars into these kinds is the named input (STRONG_PRICE §3). -/

namespace FLatticePaper.StrongUnitPrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.StrongHSpan FLatticePaper.StrongPriceValues

/-- The V source condition at a site: `F` equals the harmonic grid at the site and at its parent shift. -/
def VSource (frame : ChildFrame) (F : Field) (x : Site) : Prop :=
  F x = harmonicGrid x ∧ F (x - frame.parentShift) = harmonicGrid (x - frame.parentShift)

/-- Every site of the full star of `c` is an interior site of `E`, an H-band site, or a V source site. -/
def StarClassified (frame : ChildFrame) (F : Field) : Prop :=
  ∀ c x, (x = c ∨ x = FLatticePaper.incomingNeg c ∨ x = FLatticePaper.incomingPos c) →
    x ∈ frame.closedPolygon ∨ HStarBand frame x ∨ VSource frame F x

/-- **The price on a full star.** Under the classification, the price of every site of a full star lies in `[c₀ − 1, c₀]`. -/
theorem price_mem_of_star (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hcls : StarClassified frame F) (c x : Site)
    (hx : x = c ∨ x = FLatticePaper.incomingNeg c ∨ x = FLatticePaper.incomingPos c) :
    frame.cutPrice - 1 ≤ frame.price F x ∧ frame.price F x ≤ frame.cutPrice := by
  rcases hcls c x hx with hE | hH | ⟨h1, h2⟩
  · exact hPR x hE
  · exact StrongHSpan.price_mem_of_sRange frame F hPR hPV x (StrongHSpan.sRange_of_HStarBand frame x hH)
  · have hc := StrongPriceValues.price_eq_cutPrice_of_harmonic frame F x h1 h2
    constructor <;> linarith

/-- **`HasUnitPrice` and `NoPriceSaddle`.** Under the star classification, the primitive price has unit increments on every edge and no
saddle at any star. -/
theorem unitPrice_and_noSaddle (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (hcls : StarClassified frame F) :
    HasUnitPrice frame F ∧ NoPriceSaddle frame F := by
  constructor
  · intro center input hE
    have hin : input = FLatticePaper.incomingNeg center ∨ input = FLatticePaper.incomingPos center := hE
    have hi := price_mem_of_star frame F hPR hPV hcls center input (Or.inr hin)
    have hc := price_mem_of_star frame F hPR hPV hcls center center (Or.inl rfl)
    unfold priceIncrement
    constructor <;> linarith [hi.1, hi.2, hc.1, hc.2]
  · intro site
    have hn := price_mem_of_star frame F hPR hPV hcls site (FLatticePaper.incomingNeg site)
      (Or.inr (Or.inl rfl))
    have hp := price_mem_of_star frame F hPR hPV hcls site (FLatticePaper.incomingPos site)
      (Or.inr (Or.inr rfl))
    have hs := price_mem_of_star frame F hPR hPV hcls site site (Or.inl rfl)
    unfold priceIncrement
    simp only
    omega

end FLatticePaper.StrongUnitPrice
