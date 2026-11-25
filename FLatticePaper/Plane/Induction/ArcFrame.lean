import FLatticePaper.Plane.Induction.ArcBounds
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.StarPrice
import FLatticePaper.Plane.Induction.UnitBound

/-! # The H-arc bounds in a frame, and the star of a freeH point (step 2 of the H full star price span)

For a child frame `F` with `n = F.child.num`, `d = F.child.den` both odd (the conjugate frame of a word, `D ± N`):

* `freeH_vertex_bounds`: a freeH point `z` has `2L ≤ s ≤ T − 2d` (even) and `L ≤ s ≤ T − c` (odd), `L = d + n`, `c = d − n`;
* `freeH_star_SRange`: every star member `p, incomingNeg p, incomingPos p` has its `s`-grade in the closed polygon's range
  for its own parity (the inputs move `s` by `±L` or `±c`);
* the price range `c − 1 ≤ P ≤ c` on the star then follows from `StarPrice.price_range_of_srange`. -/

namespace FLatticePaper.ArcFrame

open Farey FLatticePaper FLatticePaper.Induction

/-- The closed polygon's `s`-range for the parity of `m`. -/
def SRangeOK (F : ChildFrame) (m : Site) : Prop :=
  (EvenSite m → 0 ≤ F.sGrade m ∧ F.sGrade m ≤ F.child.periodDenominator + 2 * F.child.num) ∧
    (¬ EvenSite m → 2 - F.child.den + F.child.num ≤ F.sGrade m ∧
      F.sGrade m ≤ F.child.periodDenominator + F.child.den + F.child.num - 2)

/-- **The vertex bounds of a freeH point.** -/
theorem freeH_vertex_bounds (F : ChildFrame) (hn : F.child.num % 2 = 1) (hd : F.child.den % 2 = 1)
    {z : Site} (hz : z ∈ F.freeH) :
    (EvenSite z → 2 * (F.child.den + F.child.num) ≤ F.sGrade z ∧
        F.sGrade z ≤ F.child.periodDenominator - 2 * F.child.den) ∧
      (¬ EvenSite z → F.child.den + F.child.num ≤ F.sGrade z ∧
        F.sGrade z ≤ F.child.periodDenominator - (F.child.den - F.child.num)) := by
  obtain ⟨hn0, hnd, h2, hd3, hT⟩ := F.child_facts
  have hTd : F.child.periodDenominator = F.child.den ^ 2 + 2 * F.child.den * F.child.num - F.child.num ^ 2 := hT
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨hE, -, hSpec⟩ := hz
  have hpar : (F.tGrade z) % 2 = (z.1 + z.2) % 2 := by
    unfold ChildFrame.tGrade
    have e1 : (F.child.num * z.1) % 2 = z.1 % 2 := by
      rw [Int.mul_emod, hn]; simp
    have e2 : (F.child.den * z.2) % 2 = z.2 % 2 := by
      rw [Int.mul_emod, hd]; simp
    omega
  rw [ChildFrame.mem_closedPolygon_iff] at hE
  unfold ChildFrame.tGrade at hSpec hpar
  rcases hE with ⟨he, ht1, ht2, hs1, hs2⟩ | ⟨ho, ht1, ht2, hs1, hs2⟩
  · refine ⟨fun _ => ?_, fun hne => absurd he hne⟩
    have hz2 : (z.1 + z.2) % 2 = 0 := he
    have hspec : 2 ≤ F.child.num * z.1 - F.child.den * z.2 ∧
        F.child.num * z.1 - F.child.den * z.2 ≤ F.child.den + F.child.num - 2 := by
      rcases hSpec with ⟨-, a, b⟩ | ⟨h1, -, -⟩
      · exact ⟨a, b⟩
      · omega
    unfold ChildFrame.sGrade at hs1 hs2 ⊢
    rw [hTd] at hs2 ⊢
    obtain ⟨-, -, -, -, hlo, hhi⟩ :=
      ArcBounds.arc_even_bounds F.child.num F.child.den z.1 z.2 hn0 (by omega) hd hn hz2
        hspec.1 hspec.2 hs1 (by linarith)
    exact ⟨by linarith, by linarith⟩
  · refine ⟨fun he => absurd he ho, fun _ => ?_⟩
    have ho' : (z.1 + z.2) % 2 ≠ 0 := ho
    have hspec : F.child.num ≤ F.child.num * z.1 - F.child.den * z.2 ∧
        F.child.num * z.1 - F.child.den * z.2 ≤ F.child.den := by
      rcases hSpec with ⟨h1, -, -⟩ | ⟨-, a, b⟩
      · omega
      · exact ⟨a, b⟩
    unfold ChildFrame.sGrade at hs1 hs2 ⊢
    rw [hTd] at hs2 ⊢
    obtain ⟨-, -, -, -, hlo, hhi⟩ :=
      ArcBounds.arc_odd_bounds F.child.num F.child.den z.1 z.2 hn0 hnd (by omega)
        hspec.1 hspec.2 (by linarith) (by linarith)
    exact ⟨by linarith, by linarith⟩

/-- **The star of a freeH point lies in the parity `s`-ranges.** The inputs move `s` by `±L` (from an even centre) or `±c`
(from an odd centre); the vertex bounds then place every member in its own parity range. -/
theorem freeH_star_SRange (F : ChildFrame) (hn : F.child.num % 2 = 1) (hd : F.child.den % 2 = 1)
    {p : Site} (hp : p ∈ F.freeH) :
    SRangeOK F p ∧ SRangeOK F (incomingNeg p) ∧ SRangeOK F (incomingPos p) := by
  have hv := freeH_vertex_bounds F hn hd hp
  obtain ⟨hn0, hnd, h2, hd3, hT⟩ := F.child_facts
  by_cases he : EvenSite p
  · have hpe := hv.1 he
    have hineg : incomingNeg p = (p.1 - 1, p.2) := by
      unfold incomingNeg; rw [if_pos he]
    have hipos : incomingPos p = (p.1 + 1, p.2) := by
      unfold incomingPos; rw [if_pos he]
    have hodd1 : ¬ EvenSite (incomingNeg p) := by
      rw [hineg]; unfold EvenSite; have := he; unfold EvenSite at this; omega
    have hodd2 : ¬ EvenSite (incomingPos p) := by
      rw [hipos]; unfold EvenSite; have := he; unfold EvenSite at this; omega
    have sN : F.sGrade (incomingNeg p) = F.sGrade p - (F.child.den + F.child.num) := by
      rw [hineg]; unfold ChildFrame.sGrade; ring
    have sP : F.sGrade (incomingPos p) = F.sGrade p + (F.child.den + F.child.num) := by
      rw [hipos]; unfold ChildFrame.sGrade; ring
    refine ⟨?_, ?_, ?_⟩
    · unfold SRangeOK
      refine ⟨fun _ => ⟨by linarith, by linarith⟩, fun hne => absurd he hne⟩
    · unfold SRangeOK
      refine ⟨fun h => absurd h hodd1, fun _ => ⟨by linarith, by linarith⟩⟩
    · unfold SRangeOK
      refine ⟨fun h => absurd h hodd2, fun _ => ⟨by linarith, by linarith⟩⟩
  · have hpo := hv.2 he
    have hineg : incomingNeg p = (p.1, p.2 - 1) := by
      unfold incomingNeg; rw [if_neg he]
    have hipos : incomingPos p = (p.1, p.2 + 1) := by
      unfold incomingPos; rw [if_neg he]
    have hev1 : EvenSite (incomingNeg p) := by
      rw [hineg]; unfold EvenSite; have := he; unfold EvenSite at this; omega
    have hev2 : EvenSite (incomingPos p) := by
      rw [hipos]; unfold EvenSite; have := he; unfold EvenSite at this; omega
    have sN : F.sGrade (incomingNeg p) = F.sGrade p - (F.child.den - F.child.num) := by
      rw [hineg]; unfold ChildFrame.sGrade; ring
    have sP : F.sGrade (incomingPos p) = F.sGrade p + (F.child.den - F.child.num) := by
      rw [hipos]; unfold ChildFrame.sGrade; ring
    refine ⟨?_, ?_, ?_⟩
    · unfold SRangeOK
      refine ⟨fun h => absurd h he, fun _ => ⟨by linarith, by linarith⟩⟩
    · unfold SRangeOK
      refine ⟨fun _ => ⟨by linarith, by linarith⟩, fun h => absurd hev1 h⟩
    · unfold SRangeOK
      refine ⟨fun _ => ⟨by linarith, by linarith⟩, fun h => absurd hev2 h⟩

/-- **The price on the star of a freeH point lies in the price range** (each member: `c − 1 ≤ P ≤ c`). -/
theorem freeH_star_price {u : Word} (hS : StrongEstimates u)
    (hn : (frameAt u).child.num % 2 = 1) (hd : (frameAt u).child.den % 2 = 1)
    {p : Site} (hp : p ∈ (frameAt u).freeH) :
    ((frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) p ∧
        (frameAt u).price (standardField u) p ≤ (frameAt u).cutPrice) ∧
      ((frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) (incomingNeg p) ∧
        (frameAt u).price (standardField u) (incomingNeg p) ≤ (frameAt u).cutPrice) ∧
      ((frameAt u).cutPrice - 1 ≤ (frameAt u).price (standardField u) (incomingPos p) ∧
        (frameAt u).price (standardField u) (incomingPos p) ≤ (frameAt u).cutPrice) := by
  obtain ⟨h1, h2, h3⟩ := freeH_star_SRange (frameAt u) hn hd hp
  exact ⟨StarPrice.price_range_of_srange hS p h1, StarPrice.price_range_of_srange hS _ h2,
    StarPrice.price_range_of_srange hS _ h3⟩

/-- The conjugate child's numerator and denominator are both odd (`D − N`, `D + N` with `D + N` odd for the odd parent). -/
theorem conj_child_parity {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    (frameAt (conjWord word)).child.num % 2 = 1 ∧ (frameAt (conjWord word)).child.den % 2 = 1 := by
  obtain ⟨h1, h2⟩ := UnitBound.conj_child_sums h
  have ho : (frameAt word).parents.odd.Odd := (parentsAt_valid word).odd_parity
  unfold Fraction.Odd at ho
  rw [h1, h2]
  omega

/-- **The star span for the conjugate (class (iii)'s price input).** For a freeH point `p` of the conjugate frame, the price of
`p` and of both its inputs lies in `[c − 1, c]`. -/
theorem freeH_star_price_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {p : Site} (hp : p ∈ (frameAt (conjWord word)).freeH) :
    ((frameAt (conjWord word)).cutPrice - 1 ≤ (frameAt (conjWord word)).price (standardField (conjWord word)) p ∧
        (frameAt (conjWord word)).price (standardField (conjWord word)) p ≤ (frameAt (conjWord word)).cutPrice) ∧
      ((frameAt (conjWord word)).cutPrice - 1 ≤
          (frameAt (conjWord word)).price (standardField (conjWord word)) (incomingNeg p) ∧
        (frameAt (conjWord word)).price (standardField (conjWord word)) (incomingNeg p) ≤
          (frameAt (conjWord word)).cutPrice) ∧
      ((frameAt (conjWord word)).cutPrice - 1 ≤
          (frameAt (conjWord word)).price (standardField (conjWord word)) (incomingPos p) ∧
        (frameAt (conjWord word)).price (standardField (conjWord word)) (incomingPos p) ≤
          (frameAt (conjWord word)).cutPrice) :=
  freeH_star_price hS (conj_child_parity h).1 (conj_child_parity h).2 hp

end FLatticePaper.ArcFrame
