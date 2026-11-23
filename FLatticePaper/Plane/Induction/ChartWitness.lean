import FLatticePaper.Plane.Induction.ChartCommon
import FLatticePaper.Plane.Induction.ChartShift
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.ExitSlip
import FLatticePaper.Plane.Induction.InputExit
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! Task 66 (2)(d): the chart witnesses `FirstChartEdge`, `AdjacentChartEdge` from the sheets, and the cover.

* `F (c + σ) = F (c − ε U_q)` (the zero `U`-period of `F`; `c + σ = (c − εU_q) + εU`).
* First chart: `c + σ ∈ E`, so `F (c + σ) = min(A(c+σ), C(c+σ)) = min(A c, C c − 2)`, i.e. `F(c+σ) − A c = min 0 (Ψ c − 2)`.
* Adjacent chart: `c − εU_q ∈ E`, so `F (c+σ) = min(A(c−εU_q), C(c−εU_q))`, with `A(c−εU_q) − A c = p(c − l_v)` and
  `C(c−εU_q) − A c = Ψ c + p(c − l_v − e)`.
* `noBlackPairRise_of_chart_cover`: the centre and input exits are closed; for non-exit edges the common chart
  (`common_chart_option`) gives the first or the adjacent chart, excluded by `first_chart_excluded` and
  `adjacent_chart_excluded`. Named: the deck representative `hrep` (paragraph 2), the strict root and target `hstrict` (the
  tie and `C`-cases, which the paper reflects), and the matched-policy retention `hret`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem ChildFrame.F_add_child_kernel {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + (frame.child.den, frame.child.num)) = F x := by
  obtain ⟨hper, -⟩ := hP.periods
  rw [frame.child_kernel] at hper
  have h := hper x
  rw [frame.coherentConstantU_eq_zero] at h
  linarith

theorem ChildFrame.F_add_eps_kernel {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (x : Site) :
    F (x + (frame.eps * frame.child.den, frame.eps * frame.child.num)) = F x := by
  rcases frame.eps_unit with he | he
  · rw [he, one_mul, one_mul]
    exact frame.F_add_child_kernel hP x
  · rw [he]
    have h := frame.F_add_child_kernel hP (x + (-frame.child.den, -frame.child.num))
    have e : x + (-frame.child.den, -frame.child.num) + (frame.child.den, frame.child.num) = x := by
      ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
    rw [e] at h
    have e2 : (-1 : ℤ) * frame.child.den = -frame.child.den := by ring
    have e3 : (-1 : ℤ) * frame.child.num = -frame.child.num := by ring
    rw [e2, e3]
    exact h.symm

/-- `c + σ = (c − ε U_q) + ε U` (with `U = (d, n) = U_p + U_q`). -/
theorem ChildFrame.shift_eq_Uq (frame : ChildFrame) (c : Site) :
    c + frame.shortShift =
      (c - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) +
        (frame.eps * frame.child.den, frame.eps * frame.child.num) := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  unfold ChildFrame.shortShift
  rw [hd, hn]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring

/-- The shifted value equals the value at the adjacent representative: `F(c + σ) = F(c − ε U_q)`. -/
theorem ChildFrame.F_shift_eq_Uq {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (c : Site) :
    F (c + frame.shortShift) =
      F (c - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) := by
  rw [frame.shift_eq_Uq, frame.F_add_eps_kernel hP]

theorem min_sub_left_eq (a b : ℤ) : min a b - a = min 0 (b - a) := by
  rw [← min_sub_sub_right, sub_self]

/-- The first common chart witness (`η = +1`): both ends in `A` (strict root), the shifted values from the sheets. -/
theorem firstChart_witness {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) {c i : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (hi : i ∈ (frameAt word).closedPolygon)
    (hEdge : Edge i c) (hcs : c + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (his : i + (frameAt word).shortShift ∈ (frameAt word).closedPolygon)
    (hΨc : 1 ≤ sheetDiffW word c) (hret : sheetPolicyA P (frameAt word).sheetShift c i) :
    FirstChartEdge P c i := by
  have hΨc' := hΨc
  unfold sheetDiffW at hΨc'
  refine ⟨?_, ?_, ?_, ?_, hret⟩
  · rw [standardField_eq_sheetMin_of_strong h hSE hc]
    unfold ChildFrame.sheetMin
    exact min_eq_left (by linarith)
  · rw [standardField_eq_sheetMin_of_strong h hSE hi]
    exact sheetMin_A_of_strict_root h hSE hEdge hΨc
  · rw [standardField_eq_sheetMin_of_strong h hSE hcs]
    unfold ChildFrame.sheetMin
    rw [sheetA_add_shortShift h hSE c, sheetC_add_shortShift h hSE c, min_sub_left_eq]
    congr 1
    unfold sheetDiffW
    ring
  · rw [standardField_eq_sheetMin_of_strong h hSE his]
    unfold ChildFrame.sheetMin
    rw [sheetA_add_shortShift h hSE i, sheetC_add_shortShift h hSE i, min_sub_left_eq]
    congr 1
    unfold sheetDiffW
    ring

/-- The adjacent chart witness (`η = +1`): the shifted values from the representative `c − εU_q` in `E`. -/
theorem adjacentChart_witness {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed) {c i : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (hi : i ∈ (frameAt word).closedPolygon)
    (hcq : c - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hiq : i - ((frameAt word).eps * (frameAt word).parents.even.den,
      (frameAt word).eps * (frameAt word).parents.even.num) ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ sheetDiffW word c) (hΨi : 1 ≤ sheetDiffW word i)
    (hret : sheetPolicyA P (frameAt word).sheetShift c i) :
    AdjacentChartEdge P c i := by
  have hΨc' := hΨc
  unfold sheetDiffW at hΨc'
  have hΨi' := hΨi
  unfold sheetDiffW at hΨi'
  refine ⟨?_, ?_, hΨi, ?_, ?_, hret⟩
  · rw [standardField_eq_sheetMin_of_strong h hSE hc]
    unfold ChildFrame.sheetMin
    exact min_eq_left (by linarith)
  · rw [standardField_eq_sheetMin_of_strong h hSE hi]
    unfold ChildFrame.sheetMin
    exact min_eq_left (by linarith)
  · rw [(frameAt word).F_shift_eq_Uq hpk c, standardField_eq_sheetMin_of_strong h hSE hcq]
    unfold ChildFrame.sheetMin
    rw [← min_sub_sub_right, sheetA_sub_eps_Uq h hSE c, sheetC_sub_eps_Uq h hSE c,
      sheetStep_eq_sheetOffset word]
  · rw [(frameAt word).F_shift_eq_Uq hpk i, standardField_eq_sheetMin_of_strong h hSE hiq]
    unfold ChildFrame.sheetMin
    rw [← min_sub_sub_right, sheetA_sub_eps_Uq h hSE i, sheetC_sub_eps_Uq h hSE i,
      sheetStep_eq_sheetOffset word]

/-- The input exit is not a rise (the input analogue of `not_rising_of_centre_exit`). -/
theorem ChildFrame.not_rising_of_input_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hn3 : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hexit : InputLowerExit frame c i) :
    ¬ RisingBlackPair F frame.shortShift c i := by
  intro hr
  obtain ⟨-, -, -, -, hone⟩ := hr
  have h0 := frame.slip_increment_zero_of_input_exit hP hn3 hnd hexit
  simp only [slipIncrement] at hone
  linarith

/-- **The cover with the centre and input exits closed.** `NoBlackPairRise` for the word field from the deck representative
`hrep` (paragraph 2), the strict root and target `hstrict` (the tie and `C` cases are named), and the matched-policy
retention `hret`. -/
theorem noBlackPairRise_of_chart_cover {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hrep : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon ∧ i ∈ (frameAt word).closedPolygon)
    (hstrict : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      1 ≤ sheetDiffW word c ∧ 1 ≤ sheetDiffW word i)
    (hret : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      sheetPolicyA P (frameAt word).sheetShift c i) :
    NoBlackPairRise (standardField word) (frameAt word).shortShift := by
  have hn3 : 3 ≤ (frameAt word).child.num := child_num_ge_three h
  have hnd : (frameAt word).child.num + 2 ≤ (frameAt word).child.den := by
    have := (frameAt word).child_facts.2.2.1
    omega
  intro c hc hpar hbs i hi hone
  have hr : RisingBlackPair (standardField word) (frameAt word).shortShift c i := ⟨hi, hc, hpar, hbs, hone⟩
  obtain ⟨hcE, hiE⟩ := hrep c i hr
  obtain ⟨hΨc, hΨi⟩ := hstrict c i hr
  have hEdge : Edge i c := hi
  by_cases hnc : (frameAt word).tGrade c - 2 ≥
      (if EvenSite c then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
  · by_cases hni : (frameAt word).tGrade i - 2 ≥
        (if EvenSite i then 2 else (frameAt word).child.num) - (frameAt word).child.periodDenominator
    · rcases common_chart_option (frameAt word) hn3 hnd hcE hiE hEdge hnc hni with ⟨hcs, his⟩ | ⟨hcq, hiq⟩
      · exact first_chart_excluded h hSE P
          (firstChart_witness h hSE P hcE hiE hEdge hcs his hΨc (hret c i hr)) hr
      · exact adjacent_chart_excluded h hSE P
          (adjacentChart_witness h hSE hpk P hcE hiE hcq hiq (by linarith) hΨi (hret c i hr)) hr
    · exact (frameAt word).not_rising_of_input_exit hpk hn3 hnd
        ⟨hcE, hiE, hEdge, not_le.mp hni⟩ hr
  · exact (frameAt word).not_rising_of_centre_exit hpk hn3 hnd
      ⟨hcE, hiE, hEdge, not_le.mp hnc⟩ hr

end FLatticePaper.Induction
