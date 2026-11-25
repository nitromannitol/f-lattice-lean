import FLatticePaper.Plane.Induction.UnitBound
import FLatticePaper.Plane.Induction.StrongDeckSpan
import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.RotatedMono

/-! # The conjugate's price on a V-translate of the closed polygon (W4, class (iii))

For the conjugate frame `F` of a word `u` with strong estimates:

* (1) **coverage:** a site `m` whose `s`-grade lies in the closed polygon's `s`-range for its parity has a
  transverse translate `m + l V` in the closed polygon (`V` keeps `s`, and `exists_transverse_t_window` puts `t` in the window);
* (3) **price on the translate:** `P` has zero `V` character (`priceDrift`), so `P(m) = P(m + l V)`, and `P(m + l V) ∈ [c − 1, c]`
  by `priceRange` at a point of the polygon.

Hence `c − 1 ≤ P(m) ≤ c` for every such `m`. Step (2), the `s`-range of the star members of a `freeH` point, is not proved here
(it needs the lattice argument); it enters as the hypothesis `hs` of `price_range_of_srange`. -/

namespace FLatticePaper.StarPrice

open Farey FLatticePaper FLatticePaper.Induction

/-- **(1) Coverage by a transverse translate.** -/
theorem vtranslate_mem (frame : ChildFrame) (m : Site)
    (hs : (EvenSite m → 0 ≤ frame.sGrade m ∧ frame.sGrade m ≤ frame.child.periodDenominator + 2 * frame.child.num) ∧
      (¬ EvenSite m → 2 - frame.child.den + frame.child.num ≤ frame.sGrade m ∧
        frame.sGrade m ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2)) :
    ∃ l : ℤ, m + l • frame.child.modifiedDeck.transverse ∈ frame.closedPolygon := by
  obtain ⟨l, hpar, hw⟩ := StrongPriceRange.exists_transverse_t_window frame m
  refine ⟨l, ?_⟩
  have hsG : frame.sGrade (m + l • frame.child.modifiedDeck.transverse) = frame.sGrade m := by
    rw [UnitBound.sGrade_add_smul, RotatedMono.sGrade_transverse]
    ring
  rw [ChildFrame.mem_closedPolygon_iff, hsG]
  by_cases he : EvenSite m
  · left
    exact ⟨hpar.mpr he, (hw.1 he).1, (hw.1 he).2, (hs.1 he).1, (hs.1 he).2⟩
  · right
    exact ⟨fun hh => he (hpar.mp hh), (hw.2 he).1, (hw.2 he).2, (hs.2 he).1, (hs.2 he).2⟩

/-- **(3) The price on a transverse translate of the polygon is in the price range.** `P` has zero `V` character. -/
theorem price_range_of_vtranslate {u : Word} (hS : StrongEstimates u) (m : Site)
    (hcov : ∃ l : ℤ, m + l • (frameAt u).child.modifiedDeck.transverse ∈ (frameAt u).closedPolygon) :
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) m ∧
      (frameAt u).price (standardField u) m ≤ (frameAt u).cutPrice := by
  obtain ⟨l, hl⟩ := hcov
  have hPV : ∀ s : Site, (frameAt u).price (standardField u) (s + (frameAt u).child.modifiedDeck.transverse) =
      (frameAt u).price (standardField u) s := fun s => by linarith [(hS.priceDrift s).2]
  have hp := StrongHSpan.price_zsmul_transverse (frameAt u) (standardField u) hPV m l
  have hr := hS.priceRange _ hl
  constructor <;> linarith [hr.1, hr.2, hp]

/-- **(1)+(3) combined:** a site whose `s`-grade lies in the parity range has its price in `[c − 1, c]`. Step (2) supplies the
`s`-range hypothesis `hs` for the star members of a `freeH` point. -/
theorem price_range_of_srange {u : Word} (hS : StrongEstimates u) (m : Site)
    (hs : (EvenSite m → 0 ≤ (frameAt u).sGrade m ∧
        (frameAt u).sGrade m ≤ (frameAt u).child.periodDenominator + 2 * (frameAt u).child.num) ∧
      (¬ EvenSite m → 2 - (frameAt u).child.den + (frameAt u).child.num ≤ (frameAt u).sGrade m ∧
        (frameAt u).sGrade m ≤ (frameAt u).child.periodDenominator + (frameAt u).child.den + (frameAt u).child.num - 2)) :
    (frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) m ∧
      (frameAt u).price (standardField u) m ≤ (frameAt u).cutPrice :=
  price_range_of_vtranslate hS m (vtranslate_mem (frameAt u) m hs)

end FLatticePaper.StarPrice
