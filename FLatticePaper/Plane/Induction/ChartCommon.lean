import FLatticePaper.Plane.Induction.ChartGrades
import FLatticePaper.Plane.Induction.ChartSeparation
import FLatticePaper.Plane.Induction.InputExit

/-! Task 66 (2)(c): the common chart. For a non-exit input edge `(c, i)` with `c, i ∈ E`, the shifted points `c + σ`, `i + σ`
lie both in `E` (chart `k = 0`) or both `c − εU_q`, `i − εU_q` lie in `E` (chart `k = ε`, the adjacent representative).
The proof is the `s`-separation (`ChartSeparation`) transported through the grades of the shifted points (`ChartGrades`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem ChildFrame.evenSite_add_iff_even_shift {p q : Site} (hq : EvenSite q) : EvenSite (p + q) ↔ EvenSite p := by
  unfold EvenSite at hq ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

theorem ChildFrame.evenSite_sub_iff_of_even {p q : Site} (hq : EvenSite q) : EvenSite (p - q) ↔ EvenSite p := by
  unfold EvenSite at hq ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

theorem ChildFrame.evenSite_shortShift' (frame : ChildFrame) : EvenSite frame.shortShift := by
  unfold EvenSite ChildFrame.shortShift
  show (2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num) % 2 = 0
  have : 2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num =
      2 * (frame.eps * (frame.parents.odd.den + frame.parents.odd.num)) := by ring
  rw [this]
  simp

theorem ChildFrame.evenSite_Uq' (frame : ChildFrame) :
    EvenSite (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) := by
  unfold EvenSite
  show (frame.eps * frame.parents.even.den + frame.eps * frame.parents.even.num) % 2 = 0
  have hev : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  rcases frame.eps_unit with he | he
  · rw [he]
    omega
  · rw [he]
    omega

/-- The grades of the shifted centre and its translate `c − εU_q`. -/
theorem ChildFrame.tGrade_shortShift_add (frame : ChildFrame) (p : Site) :
    frame.tGrade (p + frame.shortShift) = frame.tGrade p - 2 := by
  rw [frame.tGrade_add, frame.tGrade_shortShift]
  ring

theorem ChildFrame.sGrade_shortShift_add (frame : ChildFrame) (p : Site) :
    frame.sGrade (p + frame.shortShift) = frame.sGrade p + 2 * frame.eps * frame.Cconst := by
  rw [frame.sGrade_add, frame.sGrade_shortShift_val]

theorem ChildFrame.T_sub_two_C (frame : ChildFrame) :
    frame.child.periodDenominator - 2 * frame.Cconst =
      (frame.child.den + frame.child.num) * frame.parents.even.den +
        (frame.child.den - frame.child.num) * frame.parents.even.num := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  unfold Fraction.periodDenominator ChildFrame.Cconst
  rw [hd, hn]
  ring

theorem ChildFrame.tGrade_Uq (frame : ChildFrame) (p : Site) :
    frame.tGrade (p - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) =
      frame.tGrade p - 2 := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  have hdet := frame.eps_det_even
  have hsq := frame.eps_sq_one
  unfold ChildFrame.tGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [hd, hn]
  linear_combination (-2 * frame.eps) * hdet - 2 * hsq

theorem ChildFrame.sGrade_Uq (frame : ChildFrame) (p : Site) :
    frame.sGrade (p - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num)) =
      frame.sGrade p + 2 * frame.eps * frame.Cconst - frame.eps * frame.child.periodDenominator := by
  have h := frame.T_sub_two_C
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  linear_combination frame.eps * h

theorem ChildFrame.closedPolygon_even_bounds {frame : ChildFrame} {z : Site} (he : EvenSite z)
    (hz : z ∈ frame.closedPolygon) :
    (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∧
      (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) := by
  unfold ChildFrame.closedPolygon at hz
  simp only [Set.mem_setOf_eq, if_pos he] at hz
  exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩

theorem ChildFrame.closedPolygon_odd_bounds {frame : ChildFrame} {z : Site} (ho : ¬ EvenSite z)
    (hz : z ∈ frame.closedPolygon) :
    (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den) ∧
      (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
  unfold ChildFrame.closedPolygon at hz
  simp only [Set.mem_setOf_eq, if_neg ho] at hz
  exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩

/-- The `E`-membership of the centre `c` and of its input `i` (both in `E`) and the step: the `s`-separation. -/
theorem common_chart_option (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hc : c ∈ frame.closedPolygon) (hi : i ∈ frame.closedPolygon) (hEdge : Edge i c)
    (hnc : frame.tGrade c - 2 ≥ (if EvenSite c then 2 else frame.child.num) - frame.child.periodDenominator)
    (hni : frame.tGrade i - 2 ≥ (if EvenSite i then 2 else frame.child.num) - frame.child.periodDenominator) :
    (c + frame.shortShift ∈ frame.closedPolygon ∧ i + frame.shortShift ∈ frame.closedPolygon) ∨
      (c - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon ∧
        i - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon) := by
  have hC := frame.Cconst_bounds
  have hT2 : frame.child.periodDenominator % 2 = 0 := by
    obtain ⟨hn, hd⟩ := frame.child_odd
    have e : frame.child.periodDenominator = (frame.child.den - frame.child.num) *
        (frame.child.den + frame.child.num) + 2 * frame.child.den * frame.child.num := by
      unfold Fraction.periodDenominator
      ring
    have hD : (frame.child.den - frame.child.num) % 2 = 0 := by omega
    have e2 : 2 * frame.child.den * frame.child.num = 2 * (frame.child.den * frame.child.num) := by ring
    rw [e, Int.add_emod, Int.mul_emod, hD, e2]
    simp
  have hsig := frame.evenSite_shortShift'
  have hUq := frame.evenSite_Uq'
  have hε := frame.eps_unit
  have hn := hn3
  have hnd' := hnd
  have hn1 : 1 ≤ frame.child.num := by omega
  by_cases he : EvenSite c
  · -- the centre is even, so the input is odd
    have hio : ¬ EvenSite i := fun h' => ((evenSite_input_iff hEdge).mp h') he
    have hcb := frame.closedPolygon_even_bounds he hc
    have hib := frame.closedPolygon_odd_bounds hio hi
    have hnc' := hnc
    have hni' := hni
    rw [if_pos he] at hnc'
    rw [if_neg hio] at hni'
    have hstep : frame.sGrade i = frame.sGrade c + (frame.child.den + frame.child.num) ∨
        frame.sGrade i = frame.sGrade c - (frame.child.den + frame.child.num) ∨
        frame.sGrade i = frame.sGrade c + (frame.child.den - frame.child.num) ∨
        frame.sGrade i = frame.sGrade c - (frame.child.den - frame.child.num) := by
      rcases frame.sGrade_input_even he hEdge with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hsep := sep_even_centre frame.child.periodDenominator frame.Cconst frame.child.num frame.child.den
      (frame.sGrade c) (frame.sGrade i) frame.eps hε hn1 hnd' hT2 hC.1 hC.2 (frame.sGrade_even c)
      (frame.sGrade_even i) hstep hcb.2 ⟨by omega, by omega⟩
    rcases hsep with ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ | ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    · left
      refine ⟨?_, ?_⟩
      · refine frame.mem_closedPolygon_of_even ((ChildFrame.evenSite_add_iff_even_shift hsig).mpr he) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
      · refine frame.mem_closedPolygon_of_odd (fun h' => hio ((ChildFrame.evenSite_add_iff_even_shift hsig).mp h')) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
    · right
      refine ⟨?_, ?_⟩
      · refine frame.mem_closedPolygon_of_even ((ChildFrame.evenSite_sub_iff_of_even hUq).mpr he) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
      · refine frame.mem_closedPolygon_of_odd (fun h' => hio ((ChildFrame.evenSite_sub_iff_of_even hUq).mp h')) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
  · -- the centre is odd, so the input is even
    have hie : EvenSite i := (evenSite_input_iff hEdge).mpr he
    have hcb := frame.closedPolygon_odd_bounds he hc
    have hib := frame.closedPolygon_even_bounds hie hi
    have hnc' := hnc
    have hni' := hni
    rw [if_neg he] at hnc'
    rw [if_pos hie] at hni'
    have hstep : frame.sGrade i = frame.sGrade c + (frame.child.den + frame.child.num) ∨
        frame.sGrade i = frame.sGrade c - (frame.child.den + frame.child.num) ∨
        frame.sGrade i = frame.sGrade c + (frame.child.den - frame.child.num) ∨
        frame.sGrade i = frame.sGrade c - (frame.child.den - frame.child.num) := by
      rcases frame.sGrade_input_odd he hEdge with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    have hsep := sep_odd_centre frame.child.periodDenominator frame.Cconst frame.child.num frame.child.den
      (frame.sGrade c) (frame.sGrade i) frame.eps hε hn1 hnd' hT2 hC.1 hC.2 (frame.sGrade_even c)
      (frame.sGrade_even i) hstep ⟨by omega, by omega⟩ hib.2
    rcases hsep with ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ | ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    · left
      refine ⟨?_, ?_⟩
      · refine frame.mem_closedPolygon_of_odd (fun h' => he ((ChildFrame.evenSite_add_iff_even_shift hsig).mp h')) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
      · refine frame.mem_closedPolygon_of_even ((ChildFrame.evenSite_add_iff_even_shift hsig).mpr hie) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.tGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
        · rw [frame.sGrade_shortShift_add]; omega
    · right
      refine ⟨?_, ?_⟩
      · refine frame.mem_closedPolygon_of_odd (fun h' => he ((ChildFrame.evenSite_sub_iff_of_even hUq).mp h')) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
      · refine frame.mem_closedPolygon_of_even ((ChildFrame.evenSite_sub_iff_of_even hUq).mpr hie) ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.tGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega
        · rw [frame.sGrade_Uq]; omega

end FLatticePaper.Induction
