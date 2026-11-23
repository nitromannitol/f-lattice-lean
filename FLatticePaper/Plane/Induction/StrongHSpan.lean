import FLatticePaper.Plane.Induction.ChartGrades
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Strips

/-! Task 67, STRONG_PRICE §1 (the H star): the single two-level span of the primitive price on the H input star.

The transverse period `V = (n − d, n + d)` has `s(V) = 0` and `t(V) = −T`, and `P(z + V) = P(z)`. So a site whose `s`-grade lies in the
`s`-range of the closed polygon `E` (at its parity) is moved into `E` by a `V`-shift alone (`exists_transverse_shift_mem`), and then
`P z ∈ {c₀ − 1, c₀}` (`price_mem_of_sRange`, from the price range on `E`). The H star lies in those `s`-ranges (`HStarBand`, the native H
bounds of H_FULL_STAR_PRICE_SPAN §2, a named geometric input): `price_on_HStar`.
No endpoint argument is needed: `V` does not change `s`. -/

namespace FLatticePaper.StrongHSpan

open Farey FLatticePaper FLatticePaper.Induction

/-- The `s`-range of the closed polygon `E` at the parity of `z`. -/
def sRangeE (frame : ChildFrame) (z : Site) : Prop :=
  (EvenSite z → 0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∧
  (¬ EvenSite z → 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
    frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2)

/-- The transverse period `(n − d, n + d)` has `t`-grade `−T`. -/
theorem tGrade_transverse_eq (frame : ChildFrame) :
    frame.tGrade frame.child.modifiedDeck.transverse = -frame.child.periodDenominator := by
  obtain ⟨-, -, -, -, hT⟩ := frame.child_facts
  rw [frame.child_modifiedDeck_transverse, hT]
  unfold ChildFrame.tGrade
  ring

/-- The transverse period has `s`-grade `0`. -/
theorem sGrade_transverse_eq (frame : ChildFrame) :
    frame.sGrade frame.child.modifiedDeck.transverse = 0 := by
  rw [frame.child_modifiedDeck_transverse]
  unfold ChildFrame.sGrade
  ring

/-- A transverse shift preserves the parity of a site (the period `V` has even coordinate sum `2n`). -/
theorem evenSite_add_transverse (frame : ChildFrame) (z : Site) (l : ℤ) :
    EvenSite (z + l • frame.child.modifiedDeck.transverse) ↔ EvenSite z := by
  rw [frame.child_modifiedDeck_transverse]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have key : z.1 + l * (frame.child.num - frame.child.den) + (z.2 + l * (frame.child.num + frame.child.den)) =
      (z.1 + z.2) + 2 * (l * frame.child.num) := by ring
  rw [key]
  generalize l * frame.child.num = q
  omega

/-- **The covering by a transverse shift.** If the `s`-grade of `z` lies in the `s`-range of `E` at its parity, some transverse shift of
`z` lies in the closed polygon `E`: the shift changes `t` by multiples of `T` and does not change `s`. -/
theorem exists_transverse_shift_mem (frame : ChildFrame) (z : Site) (hs : sRangeE frame z) :
    ∃ l : ℤ, z + l • frame.child.modifiedDeck.transverse ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hTpos : 0 < frame.child.periodDenominator := by rw [hT]; nlinarith
  have hsV : ∀ l : ℤ, frame.sGrade (z + l • frame.child.modifiedDeck.transverse) = frame.sGrade z := by
    intro l
    rw [frame.sGrade_add_pt, frame.sGrade_smul, sGrade_transverse_eq]
    ring
  have htV : ∀ l : ℤ, frame.tGrade (z + l • frame.child.modifiedDeck.transverse) =
      frame.tGrade z - l * frame.child.periodDenominator := by
    intro l
    rw [frame.tGrade_add_pt, frame.tGrade_smul, tGrade_transverse_eq]
    ring
  by_cases he : EvenSite z
  · obtain ⟨hs1, hs2⟩ := hs.1 he
    have hm := Int.emod_def (frame.tGrade z - (2 - frame.child.periodDenominator)) frame.child.periodDenominator
    have hr0 := Int.emod_nonneg (frame.tGrade z - (2 - frame.child.periodDenominator)) hTpos.ne'
    have hr1 := Int.emod_lt_of_pos (frame.tGrade z - (2 - frame.child.periodDenominator)) hTpos
    refine ⟨(frame.tGrade z - (2 - frame.child.periodDenominator)) / frame.child.periodDenominator, ?_⟩
    apply frame.mem_closedPolygon_of_even ((evenSite_add_transverse frame z _).mpr he)
    · rw [htV]
      constructor <;> nlinarith
    · rw [hsV]
      exact ⟨hs1, hs2⟩
  · obtain ⟨hs1, hs2⟩ := hs.2 he
    have hm := Int.emod_def (frame.tGrade z - (frame.child.num - frame.child.periodDenominator))
      frame.child.periodDenominator
    have hr0 := Int.emod_nonneg (frame.tGrade z - (frame.child.num - frame.child.periodDenominator)) hTpos.ne'
    have hr1 := Int.emod_lt_of_pos (frame.tGrade z - (frame.child.num - frame.child.periodDenominator)) hTpos
    refine ⟨(frame.tGrade z - (frame.child.num - frame.child.periodDenominator)) / frame.child.periodDenominator, ?_⟩
    apply frame.mem_closedPolygon_of_odd (fun h => he ((evenSite_add_transverse frame z _).mp h))
    · rw [htV]
      constructor <;> nlinarith
    · rw [hsV]
      exact ⟨hs1, hs2⟩

/-- The price is constant along the transverse period: `P(z + l V) = P z`. -/
theorem price_zsmul_transverse (frame : ChildFrame) (F : Field)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w) (z : Site) (l : ℤ) :
    frame.price F (z + l • frame.child.modifiedDeck.transverse) = frame.price F z := by
  induction l using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [add_smul, one_smul, ← add_assoc, hPV]
    exact ih
  | pred i ih =>
    have e : z + (-(i : ℤ) - 1) • frame.child.modifiedDeck.transverse + frame.child.modifiedDeck.transverse =
        z + (-(i : ℤ)) • frame.child.modifiedDeck.transverse := by
      rw [sub_smul, one_smul]
      abel
    have h := hPV (z + (-(i : ℤ) - 1) • frame.child.modifiedDeck.transverse)
    rw [e] at h
    rw [← h]
    exact ih

/-- **The price on the `s`-range of `E`.** If `s(z)` lies in the `s`-range of `E` at its parity, then `c₀ − 1 ≤ P z ≤ c₀`. -/
theorem price_mem_of_sRange (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (z : Site) (hs : sRangeE frame z) :
    frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice := by
  obtain ⟨l, hmem⟩ := exists_transverse_shift_mem frame z hs
  have hr := hPR _ hmem
  rw [price_zsmul_transverse frame F hPV z l] at hr
  exact hr

/-- The H input star, by the `s`-grades of its sites (roots and both physical inputs): even sites `2n ≤ s ≤ T`, odd sites
`L ≤ s ≤ T − c` (`L = d + n`, `c = d − n`). Its geometric source is the native H path (H_FULL_STAR_PRICE_SPAN §2), a named input. -/
def HStarBand (frame : ChildFrame) (z : Site) : Prop :=
  (EvenSite z → 2 * frame.child.num ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator) ∧
  (¬ EvenSite z → frame.child.den + frame.child.num ≤ frame.sGrade z ∧
    frame.sGrade z ≤ frame.child.periodDenominator - (frame.child.den - frame.child.num))

/-- The H-star band lies in the `s`-range of `E`. -/
theorem sRange_of_HStarBand (frame : ChildFrame) (z : Site) (h : HStarBand frame z) : sRangeE frame z := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := frame.child_facts
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := h.1 he
    constructor <;> omega
  · intro he
    obtain ⟨h1, h2⟩ := h.2 he
    constructor <;> omega

/-- **The single two-level span on the H star.** On every site of an H input star (a set `S` of sites in the H band), the primitive
price lies in `{c₀ − 1, c₀}`. -/
theorem price_on_HStar (frame : ChildFrame) (F : Field)
    (hPR : ∀ w ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price F w ∧ frame.price F w ≤ frame.cutPrice)
    (hPV : ∀ w, frame.price F (w + frame.child.modifiedDeck.transverse) = frame.price F w)
    (S : Set Site) (hS : ∀ z ∈ S, HStarBand frame z) :
    ∀ z ∈ S, frame.cutPrice - 1 ≤ frame.price F z ∧ frame.price F z ≤ frame.cutPrice :=
  fun z hz => price_mem_of_sRange frame F hPR hPV z (sRange_of_HStarBand frame z (hS z hz))

end FLatticePaper.StrongHSpan
