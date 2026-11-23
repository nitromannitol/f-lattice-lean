import FLatticePaper.Plane.Induction.FanTerminal
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.BaseRecurrent
import FLatticePaper.Plane.Induction.W1MSheet

/-! # Task 99 (2): the field of the fort is the recurrent comparison chart `M = MW word` (ALL_SLOPE_STEP, "true fort")

The true fort `S` is an incoming fort of the sheet minimum `M = MW word`, the recurrent comparison chart (`sheetMin_recurrent_of_strong`,
`sheetMin_binary_recurrent_of_strong`). `RecurrentField M` (no nonempty finite incoming fort, `recurrentField_of_recurrent`) excludes the
finite forts.

* `interior_fort_of_no_boundary`: if no boundary point of the closed polygon lies in `S`, the points of `S` in the open rectangle form an
  incoming fort (the inputs of an interior point are on the closed polygon, `rectInputs`, so they are interior).
* `sheet_fort_no_interior`: for the recurrent `M` such a fort has no interior point (the interior part is finite and recurrence excludes it).
* `sheet_fan_contradiction`, `sheet_fan_north_contradiction`: the fan contradiction of the fort for `M` against the parabola of an interior
  contact, with the north start (`MW v₀ = 0 = m(0)`, `MW (north) = 0 = m(1)`, the height-zero midpoint of ALL_SLOPE_STEP), under the window
  `m ≤ M` on the closed polygon and the paid exclusion of boundary contacts. -/

namespace FLatticePaper.SheetFort

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ContactCone FLatticePaper.FanPropagation FLatticePaper.FanTerminal
open FLatticePaper.W1MSheet FLatticePaper.QuadraticCap

/-- The points of a fort in the open rectangle form a fort, when no boundary point of the closed polygon lies in the fort. -/
theorem interior_fort_of_no_boundary (frame : ChildFrame) {F : Field} {S : Set Site} (hfort : IsIncomingFort F S)
    (hbd : ∀ b, b ∈ frame.closedPolygon → ¬ frame.openRect b → b ∉ S) :
    IsIncomingFort F {x | x ∈ S ∧ frame.openRect x} := by
  intro x hx
  obtain ⟨hxS, hxo⟩ := hx
  have inner : ∀ i, (i = incomingNeg x ∨ i = incomingPos x) → i ∈ S → frame.openRect i := by
    intro i hi hiS
    by_contra hnot
    exact hbd i (FLatticePaper.W1Exit.rectInputs frame x hxo i hi) hnot hiS
  rcases hfort x hxS with ⟨hl, hsome⟩ | ⟨hl, hn, hp⟩
  · rcases hsome with hn | hp
    · exact Or.inl ⟨hl, Or.inl ⟨hn, inner _ (Or.inl rfl) hn⟩⟩
    · exact Or.inl ⟨hl, Or.inr ⟨hp, inner _ (Or.inr rfl) hp⟩⟩
  · exact Or.inr ⟨hl, ⟨hn, inner _ (Or.inl rfl) hn⟩, ⟨hp, inner _ (Or.inr rfl) hp⟩⟩

/-- A finite incoming fort of a recurrent field is empty. -/
theorem no_finite_fort_of_recurrent {M : Field} (hrec : FLatticePaper.RecurrentField M) {T : Set Site}
    (hT : IsIncomingFort M T) (hfin : T.Finite) : T = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hF : hfin.toFinset.Nonempty := ⟨x, hfin.mem_toFinset.mpr hx⟩
  apply hrec hfin.toFinset hF
  rw [Set.Finite.coe_toFinset]
  exact hT

/-- The sheet minimum is a recurrent binary field: its finite incoming forts are empty. -/
theorem sheetMin_recurrentField {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    FLatticePaper.RecurrentField (MW word) :=
  FLatticePaper.recurrentField_of_recurrent (FLatticePaper.StrongPriceValues.sheetMin_recurrent_of_strong hw hSE)
    (FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong hw hSE).1

/-- **The fort of the recurrent sheet minimum has no interior point** when no boundary point of the closed polygon lies in it. -/
theorem sheet_fort_no_interior {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {S : Set Site} (hfort : IsIncomingFort (MW word) S)
    (hbd : ∀ b, b ∈ (frameAt word).closedPolygon → ¬ (frameAt word).openRect b → b ∉ S) :
    ∀ x ∈ S, ¬ (frameAt word).openRect x := by
  intro x hxS hxo
  have hT := interior_fort_of_no_boundary (frameAt word) hfort hbd
  have hfin : {y | y ∈ S ∧ (frameAt word).openRect y}.Finite :=
    (openRect_finite (frameAt word)).subset (fun y hy => hy.2)
  have hempty := no_finite_fort_of_recurrent (sheetMin_recurrentField hw hSE) hT hfin
  have hmem : x ∈ {y | y ∈ S ∧ (frameAt word).openRect y} := ⟨hxS, hxo⟩
  rw [hempty] at hmem
  exact hmem

/-- **The fan contradiction for the sheet fort** (ALL_SLOPE_STEP): a fort of the sheet minimum with an interior contact of the parabola
`m(z) = capMin(z.2 − b)` is impossible, under the window `m ≤ M` on the closed polygon and the paid exclusion of boundary contacts. -/
theorem sheet_fan_contradiction {word : Word} {S : Set Site} (hfort : IsIncomingFort (MW word) S) (b : ℤ)
    (hwin : ∀ i ∈ (frameAt word).closedPolygon, parabolaField b i ≤ MW word i)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0c : MW word v0 = parabolaField b v0) (hv0 : (frameAt word).openRect v0)
    (hpaid : ∀ w : Site, w ∈ (frameAt word).closedPolygon → ¬ (frameAt word).openRect w → w ∈ S →
      MW word w = parabolaField b w → False) : False :=
  fan_terminal_contradiction (frameAt word) hfort (parabola_binary b) (fun z hz => parabola_lap_even b z hz) hwin v0 hv0S
    hv0c hv0 hpaid

/-- **The north-start fan contradiction at height zero** (ALL_SLOPE_STEP, the H midpoint `b` with `F = 0 = m(0)` and north input
`F = 0 = m(1)`): the parabola is `m(z) = capMin(z.2 − b.2)`, so `m(b) = 0` and `m(north) = 0`. -/
theorem sheet_fan_north_contradiction {word : Word} {S : Set Site} (hfort : IsIncomingFort (MW word) S)
    (v0 : Site) (hv0S : v0 ∈ S) (hv0 : (frameAt word).openRect v0) (hodd : ¬ EvenSite v0)
    (hwin : ∀ i ∈ (frameAt word).closedPolygon, parabolaField v0.2 i ≤ MW word i)
    (hv0c : MW word v0 = 0) (hnS : incomingPos v0 ∈ S) (hnc : MW word (incomingPos v0) = 0)
    (hpaid : ∀ w : Site, w ∈ (frameAt word).closedPolygon → ¬ (frameAt word).openRect w → w ∈ S →
      MW word w = parabolaField v0.2 w → False) : False := by
  have hm0 : parabolaField v0.2 v0 = 0 := by
    unfold parabolaField
    rw [sub_self]
    exact capMin_zero
  have hmn : parabolaField v0.2 (incomingPos v0) = 0 := by
    unfold parabolaField incomingPos
    rw [if_neg hodd]
    simp only
    have e : v0.2 + 1 - v0.2 = 1 := by ring
    rw [e]
    exact capMin_one
  have hc0 : MW word v0 = parabolaField v0.2 v0 := by rw [hm0, hv0c]
  have hnc' : MW word (incomingPos v0) = parabolaField v0.2 (incomingPos v0) := by rw [hmn, hnc]
  exact fan_terminal_north_contradiction (frameAt word) hfort (parabola_binary v0.2) (fun z hz => parabola_lap_even v0.2 z hz)
    hwin v0 hv0S hc0 hv0 hodd hnS hnc' hpaid

end FLatticePaper.SheetFort
