import FLatticePaper.Plane.Induction.BaseUpper

/-! The range on the halo: the inputs of the sites of `E` that lie outside `E` (task 37, item 2).

Given the range `0 ≤ D ≤ 2` on `E`, the zero strip, the transverse drift and the reflection, every input `u` of a site of
`E` satisfies `0 ≤ D u ≤ 2`. Each input is covered by one of six facts, checked by linear arithmetic on the `t`-grades:

* `TWin z`: some kernel translate of `z` lies in `E` (its `t`-grade is in the parity window of `E`), so `D z ∈ [0, 2]`;
* `TWin (c − σ − u)`: the same for the reflected site, so `D u = 2 − D (c − σ − u) ∈ [0, 2]`;
* the zero strip at `u`, at `c − σ − u`: `D = 0`, and the strip at `u + T` (i.e. at `u − V`), at `c − σ − u + T`: `D = 2`.

The range on `E` is the hypothesis `base`; nothing here uses the V arcs beyond it. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame

/-- The `t`-window of the parity of a site of `E`. -/
def TWin (frame : ChildFrame) (z : Site) : Prop :=
  (EvenSite z ∧ 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∨
    (¬ EvenSite z ∧ frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den)

theorem tGrade_reflect (frame : ChildFrame) (w : Site) :
    frame.tGrade (frame.centre - frame.shortShift - w) =
      (frame.child.num + frame.child.den - frame.child.periodDenominator) + 2 - frame.tGrade w := by
  rw [frame.tGrade_sub_pt, frame.tGrade_sub_pt, frame.tGrade_centre_eq, frame.tGrade_shortShift]
  ring

theorem evenSite_reflect_iff (frame : ChildFrame) (w : Site) :
    EvenSite (frame.centre - frame.shortShift - w) ↔ EvenSite w := by
  have hc := frame.evenSite_centre
  have hs := evenSite_shortShift frame
  unfold EvenSite at hc hs ⊢
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- A site of the window has a kernel translate in `E`. -/
theorem exists_kernel_mem (frame : ChildFrame) {z : Site} (hz : frame.TWin z) :
    ∃ k : ℤ, z + k • frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  rcases hz with ⟨he, h1, h2⟩ | ⟨ho, h1, h2⟩
  · obtain ⟨k, e, he0, heT, hse⟩ := frame.exists_kernel_shift z 0
    refine ⟨k, ?_⟩
    rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨(frame.evenSite_add_smul_kernel z k).mpr he, ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_smul_kernel]; omega
    · rw [frame.tGrade_add_smul_kernel]; omega
    · rw [hse]; omega
    · rw [hse]; omega
  · obtain ⟨k, e, he0, heT, hse⟩ :=
      frame.exists_kernel_shift z (2 - frame.child.den + frame.child.num)
    refine ⟨k, ?_⟩
    rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨fun h => ho ((frame.evenSite_add_smul_kernel z k).mp h), ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_smul_kernel]; omega
    · rw [frame.tGrade_add_smul_kernel]; omega
    · rw [hse]; omega
    · rw [hse]; omega

end ChildFrame

/-- A site of the window has `D ∈ [0, 2]`, from the range on `E`. -/
theorem starDiff_mem_of_window (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (base : ∀ y ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift y ∧ starDiff F frame.shortShift y ≤ 2)
    {z : Site} (hz : frame.TWin z) :
    0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2 := by
  obtain ⟨k, hk⟩ := frame.exists_kernel_mem hz
  have hK := starDiff_add_zsmul_kernel (σ := frame.shortShift)
    (K := frame.child.modifiedDeck.kernel) hper.1 k z
  rw [← hK]
  exact base _ hk

/-- A site of the zero strip has `D = 0`, with no reference to `E`. -/
theorem starDiff_zero_of_strip_window (frame : ChildFrame) {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) {z : Site}
    (h1 : 3 - frame.child.den ≤ frame.tGrade z) (h2 : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    starDiff F frame.shortShift z = 0 :=
  starDiff_zero_of_zero_strip frame hS hagree hper0 z h1 h2

/-- A site whose `t`-grade plus the period lies in the zero strip has `D = 2`: it is `z − V` shifted by `V`. -/
theorem starDiff_two_of_strip_window (frame : ChildFrame) {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) {z : Site}
    (h1 : 3 - frame.child.den ≤ frame.tGrade z + frame.child.periodDenominator)
    (h2 : frame.tGrade z + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1) :
    starDiff F frame.shortShift z = 2 := by
  have hlo : 3 - frame.child.den ≤ frame.tGrade (z - frame.child.modifiedDeck.transverse) := by
    rw [frame.tGrade_sub_modTransverse]; exact h1
  have hhi : frame.tGrade (z - frame.child.modifiedDeck.transverse) ≤
      frame.child.num + 2 * frame.child.den - 1 := by
    rw [frame.tGrade_sub_modTransverse]; exact h2
  have h0 := starDiff_zero_of_zero_strip frame hS hagree hper0 _ hlo hhi
  have hdrift := frame.starDiff_add_transverse_two hper0 (z - frame.child.modifiedDeck.transverse)
  rw [sub_add_cancel] at hdrift
  rw [hdrift, h0]
  norm_num

/-- The inputs of a site of `E` are one of the four unit steps. -/
theorem edge_cases {u e : Site} (hu : Edge u e) :
    (EvenSite e ∧ (u = e + (-1, 0) ∨ u = e + (1, 0))) ∨
      (¬ EvenSite e ∧ (u = e + (0, -1) ∨ u = e + (0, 1))) := by
  unfold Edge incomingNeg incomingPos at hu
  by_cases h : EvenSite e
  · simp only [h, if_true] at hu
    left
    refine ⟨h, ?_⟩
    rcases hu with rfl | rfl
    · left; exact Prod.ext (by simp [sub_eq_add_neg]) (by simp)
    · right; exact Prod.ext (by simp) (by simp)
  · simp only [h, if_false] at hu
    right
    refine ⟨h, ?_⟩
    rcases hu with rfl | rfl
    · left; exact Prod.ext (by simp) (by simp [sub_eq_add_neg])
    · right; exact Prod.ext (by simp) (by simp)

/-- The six facts that cover an input `u` of a site of `E`. -/
theorem halo_window_cases (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num) {e : Site}
    (he : e ∈ frame.closedPolygon) {u : Site} (hu : Edge u e) :
    frame.TWin u ∨ frame.TWin (frame.centre - frame.shortShift - u) ∨
      (3 - frame.child.den ≤ frame.tGrade u ∧ frame.tGrade u ≤ frame.child.num + 2 * frame.child.den - 1) ∨
      (3 - frame.child.den ≤ frame.tGrade u + frame.child.periodDenominator ∧
        frame.tGrade u + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1) ∨
      (3 - frame.child.den ≤ frame.tGrade (frame.centre - frame.shortShift - u) ∧
        frame.tGrade (frame.centre - frame.shortShift - u) ≤ frame.child.num + 2 * frame.child.den - 1) ∨
      (3 - frame.child.den ≤ frame.tGrade (frame.centre - frame.shortShift - u) + frame.child.periodDenominator ∧
        frame.tGrade (frame.centre - frame.shortShift - u) + frame.child.periodDenominator ≤
          frame.child.num + 2 * frame.child.den - 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  rw [frame.mem_closedPolygon_iff] at he
  rw [frame.tGrade_reflect]
  rcases edge_cases hu with ⟨hpe, h | h⟩ | ⟨hpo, h | h⟩ <;> subst h <;>
    simp only [ChildFrame.TWin, frame.tGrade_addW, frame.tGrade_addE, frame.tGrade_addS, frame.tGrade_addN,
      frame.evenSite_reflect_iff, ChildFrame.evenSite_addW, ChildFrame.evenSite_addE,
      ChildFrame.evenSite_addS, ChildFrame.evenSite_addN] <;>
    unfold EvenSite at * <;> omega

/-- The range `0 ≤ D ≤ 2` on every input of a site of `E`, from the range on `E` and the window covering. -/
theorem halo_range (frame : ChildFrame) {F M : Field} {cU cV : ℤ} (hn3 : 3 ≤ frame.child.num)
    (hS : frame.StripInputs M) (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (base : ∀ y ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift y ∧ starDiff F frame.shortShift y ≤ 2)
    {e : Site} (he : e ∈ frame.closedPolygon) {u : Site} (hu : Edge u e) :
    0 ≤ starDiff F frame.shortShift u ∧ starDiff F frame.shortShift u ≤ 2 := by
  rcases halo_window_cases frame hn3 he hu with h | h | h | h | h | h
  · exact starDiff_mem_of_window frame hper base h
  · have h1 := starDiff_mem_of_window frame hper base h
    have h2 := frame.starDiff_reflect hrefl u
    omega
  · have h1 := starDiff_zero_of_strip_window frame hS hagree hper0 h.1 h.2
    omega
  · have h1 := starDiff_two_of_strip_window frame hS hagree hper0 h.1 h.2
    omega
  · have h1 := starDiff_zero_of_strip_window frame hS hagree hper0 h.1 h.2
    have h2 := frame.starDiff_reflect hrefl u
    omega
  · have h1 := starDiff_two_of_strip_window frame hS hagree hper0 h.1 h.2
    have h2 := frame.starDiff_reflect hrefl u
    omega

/-- The star argument inputs: the range on `E` and on its inputs, from `halo_range`. -/
theorem starArgumentInputs_of_base (frame : ChildFrame) {F M : Field} {cU cV : ℤ} (hn3 : 3 ≤ frame.child.num)
    (hS : frame.StripInputs M) (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (base : ∀ y ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift y ∧ starDiff F frame.shortShift y ≤ 2) :
    StarArgumentInputs frame F :=
  ⟨fun e he x hx => by
    rcases hx with h | h | h
    · rw [h]; exact base e he
    · rw [h]; exact halo_range frame hn3 hS hagree hper0 hper hrefl base he (Or.inl rfl)
    · rw [h]; exact halo_range frame hn3 hS hagree hper0 hper hrefl base he (Or.inr rfl)⟩

/-- S1 and S2 for `F` from the base range on `E` and the zero strip: the halo is derived, not assumed. -/
theorem S1S2_of_base (frame : ChildFrame) {F M : Field} {cU cV : ℤ} (hn3 : 3 ≤ frame.child.num)
    (hS : frame.StripInputs M) (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (hbinF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (base : ∀ y ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift y ∧ starDiff F frame.shortShift y ≤ 2) :
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
      NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) :=
  starRange_S1S2_of_argument frame hper hbinF
    (starArgumentInputs_of_base frame hn3 hS hagree hper0 hper hrefl base)

end FLatticePaper.Induction
