import FLatticePaper.Plane.Induction.BaseInputsProof

/-! The lower bound `D ≥ 0` on `E` from the upper bound `D ≤ 2` on `E` (task 36, item 3).

Let `σ` be the short shift, `K` the kernel and `V` the transverse deck of the child. The sewn field `F` has the global
reflection `F (c − z) = F z − t z + k` with `c` the centre, so `D (c − σ − x) = 2 − D x` for every `x`. The kernel
translation leaves `D` unchanged, and the transverse translation adds `2`. For every `x ∈ E` the reflected site
`c − σ − x` has a representative `c − σ − x + k K + j V ∈ E` with `j ∈ {0, 1}`, which gives `D x ≥ 2 j ≥ 0`.
No recurrence of `F` is used. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame

theorem tGrade_sub_pt (frame : ChildFrame) (a b : Site) :
    frame.tGrade (a - b) = frame.tGrade a - frame.tGrade b := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem sGrade_sub_pt (frame : ChildFrame) (a b : Site) :
    frame.sGrade (a - b) = frame.sGrade a - frame.sGrade b := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_sub, Prod.snd_sub]; ring

theorem tGrade_add_smul_transverse (frame : ChildFrame) (z : Site) (p : ℤ) :
    frame.tGrade (z + p • frame.child.modifiedDeck.transverse) =
      frame.tGrade z - p * frame.child.periodDenominator := by
  rw [frame.modTransverse_eq]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem tGrade_centre_eq (frame : ChildFrame) :
    frame.tGrade frame.centre = frame.child.num + frame.child.den - frame.child.periodDenominator := by
  unfold ChildFrame.centre
  rw [frame.tGrade_add_pt, frame.tGrade_add_pt, frame.tGrade_kernel_zero]
  have hV := frame.tGrade_add_smul_transverse 0 1
  simp only [zero_add, one_smul] at hV
  have h0 : frame.tGrade 0 = 0 := by
    unfold ChildFrame.tGrade
    show frame.child.num * 0 - frame.child.den * 0 = 0
    ring
  have h1 : frame.tGrade (1, -1) = frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade
    show frame.child.num * 1 - frame.child.den * (-1) = frame.child.num + frame.child.den
    ring
  rw [hV, h0, h1]
  ring

theorem transverseGrade_add_shortShift (frame : ChildFrame) (z : Site) :
    frame.child.transverseGrade (z + frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade frame.shortShift := by
  unfold Fraction.transverseGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem transverseGrade_shortShift (frame : ChildFrame) :
    frame.child.transverseGrade frame.shortShift = 2 := by
  rw [frame.transverseGrade_child, frame.tGrade_shortShift]
  norm_num

/-- The reflection of `D`: `D (c − σ − x) = 2 − D x`, from the global reflection of `F`. -/
theorem starDiff_reflect (frame : ChildFrame) {F : Field}
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant) (x : Site) :
    starDiff F frame.shortShift (frame.centre - frame.shortShift - x) = 2 - starDiff F frame.shortShift x := by
  unfold starDiff
  have e1 : frame.centre - frame.shortShift - x + frame.shortShift = frame.centre - x := by abel
  have e2 : frame.centre - frame.shortShift - x = frame.centre - (x + frame.shortShift) := by abel
  rw [e1, e2, hrefl (x + frame.shortShift), hrefl x, frame.tGrade_add_shortShift]
  ring

/-- The kernel shift that puts the `s`-grade into the window `[lo, lo + T)`. -/
theorem exists_kernel_shift (frame : ChildFrame) (r : Site) (lo : ℤ) :
    ∃ k : ℤ, ∃ e : ℤ, 0 ≤ e ∧ e < frame.child.periodDenominator ∧
      frame.sGrade (r + k • frame.child.modifiedDeck.kernel) = lo + e := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT : 0 < frame.child.periodDenominator := by
    have := frame.two_mul_L_le_periodDenominator; omega
  refine ⟨-((frame.sGrade r - lo) / frame.child.periodDenominator),
    (frame.sGrade r - lo) % frame.child.periodDenominator,
    Int.emod_nonneg _ hT.ne', Int.emod_lt_of_pos _ hT, ?_⟩
  rw [frame.sGrade_add_pt, frame.sGrade_smul, frame.sGrade_kernel_eq, Int.emod_def]
  ring

/-- An even site with `t` in `[4 − T, L]` and `s` in the window `[lo, lo + T)` has a representative in `E`. -/
theorem exists_representative_even (frame : ChildFrame) {r : Site} (hr : EvenSite r)
    (ht : 4 - frame.child.periodDenominator ≤ frame.tGrade r ∧
      frame.tGrade r ≤ frame.child.den + frame.child.num) :
    ∃ k : ℤ, ∃ j : ℤ, (j = 0 ∨ j = 1) ∧
      (r + k • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  obtain ⟨k, e, he0, heT, hse⟩ := frame.exists_kernel_shift r 0
  have hk : EvenSite (r + k • frame.child.modifiedDeck.kernel) := (frame.evenSite_add_smul_kernel r k).mpr hr
  have hyE : EvenSite (r + k • frame.child.modifiedDeck.kernel + 0 • frame.child.modifiedDeck.transverse) := by
    rw [zero_smul, add_zero]; exact hk
  by_cases hj : frame.tGrade r ≤ frame.child.den + frame.child.num - 2
  · refine ⟨k, 0, Or.inl rfl, ?_⟩
    rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨hyE, ?_, ?_, ?_, ?_⟩
    · rw [zero_smul, add_zero, frame.tGrade_add_smul_kernel]; omega
    · rw [zero_smul, add_zero, frame.tGrade_add_smul_kernel]; omega
    · rw [zero_smul, add_zero, hse]; omega
    · rw [zero_smul, add_zero, hse]; omega
  · refine ⟨k, 1, Or.inr rfl, ?_⟩
    have hyE1 : EvenSite (r + k • frame.child.modifiedDeck.kernel + 1 • frame.child.modifiedDeck.transverse) :=
      (frame.evenSite_add_smul_transverse _ 1).mpr hk
    rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨hyE1, ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_smul_transverse, frame.tGrade_add_smul_kernel]; omega
    · rw [frame.tGrade_add_smul_transverse, frame.tGrade_add_smul_kernel]; omega
    · rw [frame.sGrade_add_smul_transverse, hse]; omega
    · rw [frame.sGrade_add_smul_transverse, hse]; omega

/-- An odd site with `t` in `[n − T + 2, d + 2]` has a representative in `E`, with the window `[2 − d + n, T + L − 2)`. -/
theorem exists_representative_odd (frame : ChildFrame) {r : Site} (hr : ¬ EvenSite r)
    (ht : frame.child.num - frame.child.periodDenominator + 2 ≤ frame.tGrade r ∧
      frame.tGrade r ≤ frame.child.den + 2) :
    ∃ k : ℤ, ∃ j : ℤ, (j = 0 ∨ j = 1) ∧
      (r + k • frame.child.modifiedDeck.kernel + j • frame.child.modifiedDeck.transverse) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  obtain ⟨k, e, he0, heT, hse⟩ := frame.exists_kernel_shift r (2 - frame.child.den + frame.child.num)
  have hk : ¬ EvenSite (r + k • frame.child.modifiedDeck.kernel) := fun h =>
    hr ((frame.evenSite_add_smul_kernel r k).mp h)
  by_cases hj : frame.tGrade r ≤ frame.child.den
  · refine ⟨k, 0, Or.inl rfl, ?_⟩
    have hyO : ¬ EvenSite (r + k • frame.child.modifiedDeck.kernel + 0 • frame.child.modifiedDeck.transverse) := by
      rw [zero_smul, add_zero]; exact hk
    rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨hyO, ?_, ?_, ?_, ?_⟩
    · rw [zero_smul, add_zero, frame.tGrade_add_smul_kernel]; omega
    · rw [zero_smul, add_zero, frame.tGrade_add_smul_kernel]; omega
    · rw [zero_smul, add_zero, hse]; omega
    · rw [zero_smul, add_zero, hse]; omega
  · refine ⟨k, 1, Or.inr rfl, ?_⟩
    have hyO1 : ¬ EvenSite (r + k • frame.child.modifiedDeck.kernel + 1 • frame.child.modifiedDeck.transverse) := by
      intro h
      exact hk ((frame.evenSite_add_smul_transverse _ 1).mp h)
    rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨hyO1, ?_, ?_, ?_, ?_⟩
    · rw [frame.tGrade_add_smul_transverse, frame.tGrade_add_smul_kernel]; omega
    · rw [frame.tGrade_add_smul_transverse, frame.tGrade_add_smul_kernel]; omega
    · rw [frame.sGrade_add_smul_transverse, hse]; omega
    · rw [frame.sGrade_add_smul_transverse, hse]; omega

/-- Every site `x` of `E` has a representative of the reflected site `c − σ − x` in `E`, shifted by `k K + j V`, with
`j ∈ {0, 1}`. -/
theorem exists_representative (frame : ChildFrame) {x : Site} (hx : x ∈ frame.closedPolygon) :
    ∃ k : ℤ, ∃ j : ℤ, (j = 0 ∨ j = 1) ∧
      (frame.centre - frame.shortShift - x + k • frame.child.modifiedDeck.kernel +
        j • frame.child.modifiedDeck.transverse) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  obtain ⟨r, hr⟩ : ∃ r, r = frame.centre - frame.shortShift - x := ⟨_, rfl⟩
  have htr : frame.tGrade r = (frame.child.num + frame.child.den - frame.child.periodDenominator) + 2 -
      frame.tGrade x := by
    rw [hr, frame.tGrade_sub_pt, frame.tGrade_sub_pt, frame.tGrade_centre_eq, frame.tGrade_shortShift]
    ring
  have hpar : EvenSite r ↔ EvenSite x := by
    have hc := frame.evenSite_centre
    have hs := evenSite_shortShift frame
    rw [hr]
    unfold EvenSite at hc hs ⊢
    simp only [Prod.fst_sub, Prod.snd_sub] at ⊢
    omega
  rw [← hr]
  rw [frame.mem_closedPolygon_iff] at hx
  rcases hx with ⟨hxe, h1, h2, h3, h4⟩ | ⟨hxo, h1, h2, h3, h4⟩
  · exact frame.exists_representative_even (hpar.mpr hxe) ⟨by omega, by omega⟩
  · exact frame.exists_representative_odd (fun h => hxo (hpar.mp h)) ⟨by omega, by omega⟩

end ChildFrame

/-- The lower bound `D ≥ 0` on `E`, from the upper bound `D ≤ 2` on `E`, the global reflection of `F`, and the periods.
No recurrence of `F` is used. -/
theorem lower_of_upper (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (hup : ∀ y ∈ frame.closedPolygon, starDiff F frame.shortShift y ≤ 2) :
    ∀ x ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift x := by
  intro x hx
  obtain ⟨k, j, hj, hmem⟩ := frame.exists_representative hx
  have hK : ∀ z, F (z + frame.child.modifiedDeck.kernel) = F z + cU := hper.1
  have hV : ∀ z, F (z + frame.child.modifiedDeck.transverse) =
      F z - frame.child.transverseGrade z + cV := hper.2
  have hD := starDiff_add_zsmul_transverse (σ := frame.shortShift)
    (V := frame.child.modifiedDeck.transverse) (g := frame.child.transverseGrade) hV
    frame.transverseGrade_add_shortShift j (frame.centre - frame.shortShift - x + k • frame.child.modifiedDeck.kernel)
  have hK' := starDiff_add_zsmul_kernel (σ := frame.shortShift) (K := frame.child.modifiedDeck.kernel) hK k
    (frame.centre - frame.shortShift - x)
  have hup' := hup _ hmem
  have href := frame.starDiff_reflect hrefl x
  rw [hD, hK', frame.transverseGrade_shortShift, href] at hup'
  rcases hj with rfl | rfl <;> omega

end FLatticePaper.Induction
