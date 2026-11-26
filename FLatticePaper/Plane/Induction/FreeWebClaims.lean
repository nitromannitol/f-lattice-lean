import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.ShortRoute
import FLatticePaper.Plane.Induction.FreeOrbit
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeClosure

/-! # The staircase claims of the free H and V cuts (Q39, Protected Web Lemma)

For a child frame with `n = num`, `d = den` (odd, coprime, `n + 2 ≤ d`), `L = d + n`, `p = d - n`, `T = periodDenominator`, the
claims `H1L`, `H1R`, `H2F`, `H2B`, `V1D`, `V1U`, `V2F`, `V2B` say that the neighbours of a free site are free up to the deck
span (`freeClosure`). They are the grade arithmetic behind the web lemma. -/

namespace FLatticePaper.FreeWebClaims

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeClosure

theorem zero_mem_span (frame : ChildFrame) : (0 : Site) ∈ frame.child.modifiedDeck.span :=
  ⟨0, 0, by ext <;> simp [PeriodDeck.combine]⟩

/-- The span vector `i K + j V`, with `K = (d, n)` and `V = (n - d, n + d)`. -/
theorem span_comb (frame : ChildFrame) (i j : ℤ) :
    (i * frame.child.den + j * (frame.child.num - frame.child.den),
      i * frame.child.num + j * (frame.child.num + frame.child.den)) ∈ frame.child.modifiedDeck.span :=
  ⟨i, j, by ext <;> simp [PeriodDeck.combine, ChildFrame.child_modifiedDeck_kernel,
    ChildFrame.child_modifiedDeck_transverse]⟩

theorem fc_of_freeH (frame : ChildFrame) {z : Site} (h : z ∈ frame.freeH) : freeClosure frame z :=
  mem_freeClosure_of_freeH frame h

theorem fc_of_freeV (frame : ChildFrame) {z : Site} (h : z ∈ frame.freeV) : freeClosure frame z :=
  ⟨0, zero_mem_span frame, Or.inr (by simpa using h)⟩

theorem hT_two (frame : ChildFrame) : 2 ≤ frame.child.periodDenominator := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  rw [hTd]
  nlinarith

/-! ### Membership constructors -/

theorem memH_even (frame : ChildFrame) {w : Site} (hw : EvenSite w) (h1 : 2 ≤ frame.tGrade w)
    (h2 : frame.tGrade w ≤ frame.child.den + frame.child.num - 2) (h3 : 0 ≤ frame.sGrade w)
    (h4 : frame.sGrade w ≤ frame.child.periodDenominator + 2 * frame.child.num) : w ∈ frame.freeH := by
  have hT := hT_two frame
  refine mem_freeH_of frame w ?_ (not_mem_below_even frame w hw h1) (hSpec_even frame w hw h1 h2)
  exact (frame.mem_closedPolygon_iff w).mpr (Or.inl ⟨hw, by omega, h2, h3, h4⟩)

theorem memH_odd (frame : ChildFrame) {w : Site} (hw : ¬ EvenSite w) (h1 : frame.child.num ≤ frame.tGrade w)
    (h2 : frame.tGrade w ≤ frame.child.den) (h3 : 2 - frame.child.den + frame.child.num ≤ frame.sGrade w)
    (h4 : frame.sGrade w ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :
    w ∈ frame.freeH := by
  have hT := hT_two frame
  refine mem_freeH_of frame w ?_ (not_mem_below_odd frame w hw h1) (hSpec_odd frame w hw h1 h2)
  exact (frame.mem_closedPolygon_iff w).mpr (Or.inr ⟨hw, by omega, h2, h3, h4⟩)

theorem memV_even (frame : ChildFrame) {w : Site} (hw : EvenSite w)
    (h1 : 2 - frame.child.periodDenominator ≤ frame.tGrade w)
    (h2 : frame.tGrade w ≤ frame.child.den + frame.child.num - 2) (h3 : 0 ≤ frame.sGrade w)
    (h4 : frame.sGrade w ≤ 2 * frame.child.num) : w ∈ frame.freeV := by
  have hT := hT_two frame
  refine mem_freeV_of frame w ?_ (not_mem_left_even frame w hw h4) (vSpec_even frame w (Or.inl ⟨h3, h4⟩))
  exact (frame.mem_closedPolygon_iff w).mpr (Or.inl ⟨hw, h1, h2, h3, by omega⟩)

theorem memV_odd (frame : ChildFrame) {w : Site} (hw : ¬ EvenSite w)
    (h1 : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade w)
    (h2 : frame.tGrade w ≤ frame.child.den) (h3 : 2 - frame.child.den + frame.child.num ≤ frame.sGrade w)
    (h4 : frame.sGrade w ≤ frame.child.den + frame.child.num - 2) : w ∈ frame.freeV := by
  have hT := hT_two frame
  refine mem_freeV_of frame w ?_ (not_mem_left_odd frame w hw h4) (vSpec_even frame w (Or.inr ⟨h3, h4⟩))
  exact (frame.mem_closedPolygon_iff w).mpr (Or.inr ⟨hw, h1, h2, h3, by omega⟩)

theorem freeV_origin (frame : ChildFrame) : (0 : Site) ∈ frame.freeV := by
  have hT := hT_two frame
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have h0t : frame.tGrade 0 = 0 := by unfold ChildFrame.tGrade; simp
  have h0s : frame.sGrade 0 = 0 := by unfold ChildFrame.sGrade; simp
  refine mem_freeV_of frame 0 ?_ ?_ ?_
  · exact (frame.mem_closedPolygon_iff 0).mpr
      (Or.inl ⟨by unfold EvenSite; simp, by omega, by omega, by omega, by omega⟩)
  · exact not_mem_left_even frame 0 (by unfold EvenSite; simp) (by omega)
  · exact vSpec_even frame 0 (Or.inl ⟨by omega, by omega⟩)

/-! ### The shifts of the grades -/

theorem tGrade_shift (frame : ChildFrame) (x : Site) (a b : ℤ) :
    frame.tGrade (x.1 + a, x.2 + b) = frame.tGrade x + frame.child.num * a - frame.child.den * b := by
  unfold ChildFrame.tGrade; ring

theorem sGrade_shift (frame : ChildFrame) (x : Site) (a b : ℤ) :
    frame.sGrade (x.1 + a, x.2 + b) =
      frame.sGrade x + (frame.child.den + frame.child.num) * a + (frame.child.den - frame.child.num) * b := by
  unfold ChildFrame.sGrade; ring

/-- The identity `n s = T y_2 + L t` (the inverse of the grade map on the second coordinate). -/
theorem num_sGrade_eq (frame : ChildFrame) (x : Site) :
    frame.child.num * frame.sGrade x =
      frame.child.periodDenominator * x.2 + (frame.child.den + frame.child.num) * frame.tGrade x := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  unfold ChildFrame.sGrade ChildFrame.tGrade
  rw [hTd]; ring

/-! ### Odd and even window facts for the free cuts -/

/-- The even free H site has `t` in the H spectrum with `2 ≤ t ≤ L - 2`. -/
theorem freeH_even_t (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
  have hsp : frame.hSpectrum (frame.tGrade z) := hz.2.2
  have hpar := tGrade_parity frame z
  unfold ChildFrame.hSpectrum at hsp
  unfold EvenSite at hev
  rcases hsp with h | h <;> omega

theorem freeH_odd_t (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) :
    frame.child.num ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
  have hsp : frame.hSpectrum (frame.tGrade z) := hz.2.2
  have hpar := tGrade_parity frame z
  unfold ChildFrame.hSpectrum at hsp
  unfold EvenSite at hodd
  rcases hsp with h | h <;> omega

/-- The box of the H cut: `1 ≤ z_1 ≤ d`, `0 ≤ z_2 ≤ n - 1`. -/
theorem freeH_bounds (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    1 ≤ z.1 ∧ z.1 ≤ frame.child.den ∧ 0 ≤ z.2 ∧ z.2 ≤ frame.child.num - 1 :=
  FLatticePaper.Induction.FreeTraceBox.freeH_box frame hz

theorem freeV_even_s (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) :
    0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num :=
  FLatticePaper.FreeVWindow.freeV_even_window frame hz hev

theorem freeV_odd_s (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.den + frame.child.num - 2 :=
  FLatticePaper.FreeVWindow.freeV_odd_window frame hz hodd

/-- The closed polygon membership of a free V site. -/
theorem freeV_mem_E (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) : z ∈ frame.closedPolygon := by
  have hz' := hz
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz'
  exact hz'.1

theorem freeH_mem_E (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) : z ∈ frame.closedPolygon := by
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  exact hz'.1

/-- `s` of a free H site: `L ≤ s ≤ T - (d - n)`. -/
theorem freeH_s (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator - (frame.child.den - frame.child.num) :=
  FLatticePaper.ShortRoute.freeH_sGrade_bounds frame hz

/-- The `y_2` bound of an odd free V site: `y_2 ≤ L - 2`. -/
theorem freeV_odd_y_le (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    z.2 ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hz hodd
  have hyr := FLatticePaper.FreeOrbit.freeV_y_range frame hz
  by_contra hcon
  have hz2 : z.2 = frame.child.den + frame.child.num - 1 := by omega
  have hid : (frame.child.den + frame.child.num) * (z.1 + (frame.child.den - frame.child.num)) =
      frame.sGrade z + (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade
    rw [hz2]; ring
  have hk1 : 1 ≤ z.1 + (frame.child.den - frame.child.num) := by
    by_contra h
    push Not at h
    nlinarith
  have hk2 : z.1 + (frame.child.den - frame.child.num) ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hk : z.1 + (frame.child.den - frame.child.num) = 1 := by omega
  apply hodd
  unfold EvenSite
  omega

/-- An odd free V site has `y_2 ≥ 1`. -/
theorem freeV_odd_y_pos (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    1 ≤ z.2 := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hz hodd
  have hyr := FLatticePaper.FreeOrbit.freeV_y_range frame hz
  by_contra hcon
  have hz2 : z.2 = 0 := by omega
  have hs : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 := by
    unfold ChildFrame.sGrade; rw [hz2]; ring
  have hz1 : z.1 = 0 := by
    have h1 : -(frame.child.den + frame.child.num) < (frame.child.den + frame.child.num) * z.1 := by omega
    have h2 : (frame.child.den + frame.child.num) * z.1 < (frame.child.den + frame.child.num) := by omega
    have h3 : -1 < z.1 := by
      by_contra h; push Not at h; nlinarith
    have h4 : z.1 < 1 := by
      by_contra h; push Not at h; nlinarith
    omega
  apply hodd
  unfold EvenSite
  omega

/-- The bound `s ≤ T - 2(d - n)` on a free H site with `t ≥ d - n + 2` (its `y_2 ≤ n - 2`). -/
theorem freeH_s_high (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (ht : frame.child.den - frame.child.num + 2 ≤ frame.tGrade z) :
    frame.sGrade z ≤ frame.child.periodDenominator - 2 * (frame.child.den - frame.child.num) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨hz1, hzd, hz2, hzn⟩ := freeH_bounds frame hz
  have hid := num_sGrade_eq frame z
  have hpar := tGrade_parity frame z
  have hnodd := frame.child_odd
  have hz2' : z.2 ≤ frame.child.num - 2 := by
    by_contra h
    have hz2e : z.2 = frame.child.num - 1 := by omega
    have htz : frame.tGrade z = frame.child.num * z.1 - frame.child.den * (frame.child.num - 1) := by
      unfold ChildFrame.tGrade; rw [hz2e]
    have hz1d : frame.child.den ≤ z.1 := by
      rw [htz] at ht
      nlinarith
    have hz1e : z.1 = frame.child.den := by omega
    apply absurd hev
    unfold EvenSite
    rw [hz1e, hz2e]
    omega
  have htle : frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := (freeH_even_t frame hz hev).2
  have hT0 : 0 ≤ frame.child.periodDenominator := by omega
  have hA : frame.child.num * frame.sGrade z ≤
      frame.child.periodDenominator * (frame.child.num - 2) + (frame.child.den + frame.child.num) *
        (frame.child.den + frame.child.num - 2) := by
    rw [hid]
    have h1 : frame.child.periodDenominator * z.2 ≤ frame.child.periodDenominator * (frame.child.num - 2) :=
      mul_le_mul_of_nonneg_left hz2' hT0
    have h2 : (frame.child.den + frame.child.num) * frame.tGrade z ≤
        (frame.child.den + frame.child.num) * (frame.child.den + frame.child.num - 2) :=
      mul_le_mul_of_nonneg_left htle (by omega)
    linarith
  have hB : frame.child.num * (frame.child.periodDenominator - 2 * (frame.child.den - frame.child.num)) ≥
      frame.child.periodDenominator * (frame.child.num - 2) + (frame.child.den + frame.child.num) *
        (frame.child.den + frame.child.num - 2) := by
    rw [hTd]
    nlinarith
  by_contra hcon
  push Not at hcon
  have : frame.child.num * (frame.child.periodDenominator - 2 * (frame.child.den - frame.child.num)) <
      frame.child.num * frame.sGrade z :=
    mul_lt_mul_of_pos_left hcon hn0
  linarith

/-- The bound `s ≥ 2d` on a free H site with `t ≤ 2n - 2` (its `y_2 ≥ 1`). -/
theorem freeH_s_low (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (ht : frame.tGrade z ≤ 2 * frame.child.num - 2) :
    2 * frame.child.den ≤ frame.sGrade z := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨hz1, hzd, hz2, hzn⟩ := freeH_bounds frame hz
  have hte := freeH_even_t frame hz hev
  have hid := num_sGrade_eq frame z
  have hnodd := frame.child_odd
  have hz2p : 1 ≤ z.2 := by
    by_contra h
    have hz2e : z.2 = 0 := by omega
    have htz : frame.tGrade z = frame.child.num * z.1 := by
      unfold ChildFrame.tGrade; rw [hz2e]; ring
    have hz1e : z.1 = 1 := by
      have h1 : z.1 < 2 := by
        by_contra h2; push Not at h2; nlinarith
      omega
    apply absurd hev
    unfold EvenSite
    rw [hz1e, hz2e]
    omega
  have hTz : frame.child.periodDenominator ≤ frame.child.periodDenominator * z.2 := by
    nlinarith
  have hLt : 2 * (frame.child.den + frame.child.num) ≤ (frame.child.den + frame.child.num) * frame.tGrade z := by
    nlinarith
  have hns : frame.child.periodDenominator + 2 * (frame.child.den + frame.child.num) ≤
      frame.child.num * frame.sGrade z := by
    rw [hid]; linarith
  by_contra hcon
  push Not at hcon
  have hlt : frame.child.num * frame.sGrade z ≤ frame.child.num * (2 * frame.child.den - 1) :=
    mul_le_mul_of_nonneg_left (by omega) hn0.le
  have hfin : frame.child.periodDenominator + 2 * (frame.child.den + frame.child.num) ≤
      frame.child.num * (2 * frame.child.den - 1) := le_trans hns hlt
  have hTd' : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num -
      frame.child.num ^ 2 := hTd
  nlinarith

/-! ### The H claims -/

theorem H1L (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (ho : ¬ EvenSite z) :
    freeClosure frame (z.1 - 1, z.2) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  obtain ⟨hz1, hzd, hz2, hzn⟩ := freeH_bounds frame hz
  obtain ⟨hsL, hsT⟩ := freeH_s frame hz
  obtain ⟨ht1, ht2⟩ := freeH_odd_t frame hz ho
  have hpw : frame.tGrade (z.1 - 1, z.2) % 2 = (z.1 - 1 + z.2) % 2 := tGrade_parity frame _
  have hpar := tGrade_parity frame z
  have hodd : (z.1 + z.2) % 2 = 1 := by unfold EvenSite at ho; omega
  have htw : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade; ring
  by_cases hcase : frame.tGrade z = frame.child.num
  · -- z = (1, 0): the H_0 site, its west neighbour is the origin
    have hEq : frame.child.num * z.1 - frame.child.den * z.2 = frame.child.num := by
      unfold ChildFrame.tGrade at hcase; exact hcase
    have hdv : frame.child.num ∣ frame.child.den * z.2 := ⟨z.1 - 1, by linarith⟩
    have hz2d : frame.child.num ∣ z.2 := hcop.dvd_of_dvd_mul_left hdv
    obtain ⟨c, hc⟩ := hz2d
    have hc1 : c < 1 := by
      by_contra h; push Not at h; nlinarith
    have hc2 : 0 ≤ c := by
      by_contra h; push Not at h; nlinarith
    have hc0 : c = 0 := by omega
    have hz2z : z.2 = 0 := by rw [hc, hc0]; ring
    have hz1e : z.1 = 1 := by
      have h1 : frame.child.num * z.1 = frame.child.num * 1 := by
        rw [hz2z] at hEq; linarith
      exact mul_left_cancel₀ hn0.ne' h1
    rw [hz1e, hz2z]
    have e : ((1 : ℤ) - 1, (0 : ℤ)) = (0, 0) := by norm_num
    rw [e]
    exact fc_of_freeV frame (freeV_origin frame)
  · have hwev : EvenSite (z.1 - 1, z.2) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    have ht2' : 2 ≤ frame.tGrade (z.1 - 1, z.2) := by omega
    have ht3 : frame.tGrade (z.1 - 1, z.2) ≤ frame.child.den + frame.child.num - 2 := by omega
    have hsw : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
      unfold ChildFrame.sGrade; ring
    have hs0 : 0 ≤ frame.sGrade (z.1 - 1, z.2) := by omega
    have hs1 : frame.sGrade (z.1 - 1, z.2) ≤ frame.child.periodDenominator + 2 * frame.child.num := by omega
    exact fc_of_freeH frame (memH_even frame hwev ht2' ht3 hs0 hs1)

theorem H1R (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (ho : ¬ EvenSite z) :
    freeClosure frame (z.1 + 1, z.2) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  obtain ⟨hz1, hzd, hz2, hzn⟩ := freeH_bounds frame hz
  obtain ⟨hsL, hsT⟩ := freeH_s frame hz
  obtain ⟨ht1, ht2⟩ := freeH_odd_t frame hz ho
  have hpar := tGrade_parity frame z
  have hodd : (z.1 + z.2) % 2 = 1 := by unfold EvenSite at ho; omega
  have hnodd := frame.child_odd
  have htw : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have hsw : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  by_cases hcase : frame.tGrade z = frame.child.den
  · -- z = (d, n - 1): the far H site
    have hEq : frame.child.num * z.1 - frame.child.den * z.2 = frame.child.den := by
      unfold ChildFrame.tGrade at hcase; exact hcase
    have hdv : frame.child.den ∣ frame.child.num * z.1 := ⟨z.2 + 1, by linarith⟩
    have hz1d : frame.child.den ∣ z.1 := hcop.symm.dvd_of_dvd_mul_left hdv
    obtain ⟨c, hc⟩ := hz1d
    have hc1 : c ≤ 1 := by
      by_contra h; push Not at h; nlinarith
    have hc2 : 1 ≤ c := by
      by_contra h; push Not at h; nlinarith
    have hc0 : c = 1 := by omega
    have hz1e : z.1 = frame.child.den := by rw [hc, hc0]; ring
    have hz2e : z.2 = frame.child.num - 1 := by
      have h2 : frame.child.den * (frame.child.num - 1 - z.2) = 0 := by
        rw [hz1e] at hEq; linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · omega
      · linarith
    refine ⟨(frame.child.num - 2 * frame.child.den, frame.child.den), ?_, Or.inr ?_⟩
    · have e : ((-1 : ℤ) * frame.child.den + 1 * (frame.child.num - frame.child.den),
          (-1 : ℤ) * frame.child.num + 1 * (frame.child.num + frame.child.den)) =
          (frame.child.num - 2 * frame.child.den, frame.child.den) := by
        ext <;> dsimp <;> ring
      have h := span_comb frame (-1) 1
      rw [e] at h
      exact h
    · rw [Prod.mk_add_mk, hz1e, hz2e]
      apply memV_even frame
      · unfold EvenSite; simp only; omega
      · have e1 : frame.tGrade (frame.child.den + 1 + (frame.child.num - 2 * frame.child.den),
            frame.child.num - 1 + frame.child.den) =
            frame.child.num + frame.child.den - frame.child.periodDenominator := by
          unfold ChildFrame.tGrade; rw [hTd]; ring
        omega
      · have e1 : frame.tGrade (frame.child.den + 1 + (frame.child.num - 2 * frame.child.den),
            frame.child.num - 1 + frame.child.den) =
            frame.child.num + frame.child.den - frame.child.periodDenominator := by
          unfold ChildFrame.tGrade; rw [hTd]; ring
        omega
      · have e2 : frame.sGrade (frame.child.den + 1 + (frame.child.num - 2 * frame.child.den),
            frame.child.num - 1 + frame.child.den) = 2 * frame.child.num := by
          unfold ChildFrame.sGrade; ring
        omega
      · have e2 : frame.sGrade (frame.child.den + 1 + (frame.child.num - 2 * frame.child.den),
            frame.child.num - 1 + frame.child.den) = 2 * frame.child.num := by
          unfold ChildFrame.sGrade; ring
        omega
  · have hodd' : frame.tGrade z ≤ frame.child.den - 2 := by omega
    have hwev : EvenSite (z.1 + 1, z.2) := by
      unfold EvenSite at hodd ⊢
      simp only at hodd ⊢
      omega
    have h1 : 2 ≤ frame.tGrade (z.1 + 1, z.2) := by omega
    have h2 : frame.tGrade (z.1 + 1, z.2) ≤ frame.child.den + frame.child.num - 2 := by omega
    have h3 : 0 ≤ frame.sGrade (z.1 + 1, z.2) := by omega
    have h4 : frame.sGrade (z.1 + 1, z.2) ≤ frame.child.periodDenominator + 2 * frame.child.num := by omega
    exact fc_of_freeH frame (memH_even frame hwev h1 h2 h3 h4)

theorem H2F (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    (frame.tGrade z ≤ frame.child.den - frame.child.num ∧ freeClosure frame (z.1 + 1, z.2)) ∨
      (frame.child.den - frame.child.num + 2 ≤ frame.tGrade z ∧
        freeClosure frame (z.1 + 1, z.2 + 1)) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨ht1, ht2⟩ := freeH_even_t frame hz hev
  obtain ⟨hsL, hsT⟩ := freeH_s frame hz
  have hnodd := frame.child_odd
  have hpar := tGrade_parity frame z
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hodd1 : ¬ EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
  have htw : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have hsw : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  by_cases hle : frame.tGrade z ≤ frame.child.den - frame.child.num
  · refine Or.inl ⟨hle, fc_of_freeH frame (memH_odd frame hodd1 ?_ ?_ ?_ ?_)⟩
    · omega
    · omega
    · omega
    · omega
  · have hgt : frame.child.den - frame.child.num + 2 ≤ frame.tGrade z := by omega
    have hev2 : EvenSite (z.1 + 1, z.2 + 1) := by
      unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
    have htw2 : frame.tGrade (z.1 + 1, z.2 + 1) = frame.tGrade z + frame.child.num - frame.child.den := by
      unfold ChildFrame.tGrade; ring
    have hsw2 : frame.sGrade (z.1 + 1, z.2 + 1) = frame.sGrade z + 2 * frame.child.den := by
      unfold ChildFrame.sGrade; ring
    have hs2 := freeH_s_high frame hz hev hgt
    refine Or.inr ⟨hgt, fc_of_freeH frame (memH_even frame hev2 ?_ ?_ ?_ ?_)⟩
    · omega
    · omega
    · omega
    · omega

theorem H2B (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    (2 * frame.child.num ≤ frame.tGrade z ∧ freeClosure frame (z.1 - 1, z.2)) ∨
      (frame.tGrade z ≤ 2 * frame.child.num - 2 ∧ freeClosure frame (z.1 - 1, z.2 - 1)) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨ht1, ht2⟩ := freeH_even_t frame hz hev
  obtain ⟨hsL, hsT⟩ := freeH_s frame hz
  have hnodd := frame.child_odd
  have hpar := tGrade_parity frame z
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hodd1 : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
  have htw : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have hsw : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  by_cases h : 2 * frame.child.num ≤ frame.tGrade z
  · refine Or.inl ⟨h, fc_of_freeH frame (memH_odd frame hodd1 ?_ ?_ ?_ ?_)⟩
    · omega
    · omega
    · omega
    · omega
  · have hlt : frame.tGrade z ≤ 2 * frame.child.num - 2 := by omega
    have hev2 : EvenSite (z.1 - 1, z.2 - 1) := by
      unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
    have htw2 : frame.tGrade (z.1 - 1, z.2 - 1) = frame.tGrade z + frame.child.den - frame.child.num := by
      unfold ChildFrame.tGrade; ring
    have hsw2 : frame.sGrade (z.1 - 1, z.2 - 1) = frame.sGrade z - 2 * frame.child.den := by
      unfold ChildFrame.sGrade; ring
    have hs2 := freeH_s_low frame hz hev hlt
    refine Or.inr ⟨hlt, fc_of_freeH frame (memH_even frame hev2 ?_ ?_ ?_ ?_)⟩
    · omega
    · omega
    · omega
    · omega

/-! ### The V claims for odd free V sites -/

theorem V2F (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    (frame.sGrade z ≤ 3 * frame.child.num - frame.child.den ∧ freeClosure frame (z.1, z.2 + 1)) ∨
      (3 * frame.child.num - frame.child.den + 2 ≤ frame.sGrade z ∧
        freeClosure frame (z.1 - 1, z.2 + 1)) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hz hodd
  have hy2 := freeV_odd_y_le frame hz hodd
  have hy0 := (FLatticePaper.FreeOrbit.freeV_y_range frame hz).1
  have hE := freeV_mem_E frame hz
  have hpar := sGrade_even frame z
  have hnodd := frame.child_odd
  have hid := num_sGrade_eq frame z
  rw [frame.mem_closedPolygon_iff z] at hE
  rcases hE with ⟨he, -⟩ | ⟨-, ht1, ht2, -, -⟩
  · exact absurd he hodd
  by_cases hs3 : frame.sGrade z ≤ 3 * frame.child.num - frame.child.den
  · -- the forward neighbour (z_1, z_2 + 1) is even and in freeV
    have htw : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
      unfold ChildFrame.tGrade; ring
    have hsw : frame.sGrade (z.1, z.2 + 1) = frame.sGrade z + (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade; ring
    have hwev : EvenSite (z.1, z.2 + 1) := by
      unfold EvenSite at hodd ⊢; simp only at hodd ⊢; omega
    have hlow : frame.child.num * (2 - (frame.child.den - frame.child.num)) ≤ frame.child.num * frame.sGrade z :=
      mul_le_mul_of_nonneg_left (by omega) hn0.le
    have hz2le : frame.child.periodDenominator * z.2 ≤ frame.child.periodDenominator *
        (frame.child.den + frame.child.num - 2) := mul_le_mul_of_nonneg_left hy2 (by omega)
    have hLt : frame.tGrade z ≥ frame.child.den + 2 - frame.child.periodDenominator := by
      by_contra hcon
      push Not at hcon
      have hLc : (frame.child.den + frame.child.num) * frame.tGrade z ≤
          (frame.child.den + frame.child.num) * (frame.child.den + 1 - frame.child.periodDenominator) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have key : frame.child.num * (2 - (frame.child.den - frame.child.num)) -
          frame.child.periodDenominator * ((frame.child.den + frame.child.num) - 2) -
          (frame.child.den + frame.child.num) * (frame.child.den + 1 - frame.child.periodDenominator) =
          frame.child.periodDenominator + frame.child.num - frame.child.den := by
        rw [hTd]; ring
      have hTpos : 0 < frame.child.periodDenominator + frame.child.num - frame.child.den := by
        rw [hTd]; nlinarith
      nlinarith
    refine Or.inl ⟨hs3, fc_of_freeV frame (memV_even frame hwev ?_ ?_ ?_ ?_)⟩
    · rw [htw]; omega
    · rw [htw]; omega
    · rw [hsw]; omega
    · rw [hsw]; omega
  · -- the backward-left neighbour (z_1 - 1, z_2 + 1) is odd and in freeV
    have hs4 : 3 * frame.child.num - frame.child.den + 2 ≤ frame.sGrade z := by omega
    have hw : ¬ EvenSite (z.1 - 1, z.2 + 1) := by
      unfold EvenSite at hodd ⊢; simp only at hodd ⊢; omega
    have htw : frame.tGrade (z.1 - 1, z.2 + 1) = frame.tGrade z - (frame.child.den + frame.child.num) := by
      unfold ChildFrame.tGrade; ring
    have hsw : frame.sGrade (z.1 - 1, z.2 + 1) = frame.sGrade z - 2 * frame.child.num := by
      unfold ChildFrame.sGrade; ring
    have hlow : frame.child.num * (3 * frame.child.num - frame.child.den + 2) ≤
        frame.child.num * frame.sGrade z := mul_le_mul_of_nonneg_left (by omega) hn0.le
    have hz2le : frame.child.periodDenominator * z.2 ≤ frame.child.periodDenominator *
        (frame.child.den + frame.child.num - 2) := mul_le_mul_of_nonneg_left hy2 (by omega)
    have hLt : frame.tGrade z ≥ frame.child.num + (frame.child.den + frame.child.num) -
        frame.child.periodDenominator := by
      by_contra hcon
      push Not at hcon
      have hLc : (frame.child.den + frame.child.num) * frame.tGrade z ≤
          (frame.child.den + frame.child.num) * (frame.child.num + (frame.child.den + frame.child.num) -
            frame.child.periodDenominator - 1) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have key : frame.child.num * (3 * frame.child.num - frame.child.den + 2) -
          frame.child.periodDenominator * ((frame.child.den + frame.child.num) - 2) -
          (frame.child.den + frame.child.num) * (frame.child.num + (frame.child.den + frame.child.num) -
            frame.child.periodDenominator - 1) =
          frame.child.den ^ 2 - frame.child.num ^ 2 + 3 * frame.child.num + frame.child.den := by
        rw [hTd]; ring
      have hpos : 0 < frame.child.den ^ 2 - frame.child.num ^ 2 + 3 * frame.child.num + frame.child.den := by
        nlinarith
      nlinarith
    refine Or.inr ⟨hs4, fc_of_freeV frame (memV_odd frame hw ?_ ?_ ?_ ?_)⟩
    · rw [htw]; omega
    · rw [htw]; omega
    · omega
    · omega

theorem V2B (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    (frame.child.den - frame.child.num ≤ frame.sGrade z ∧ freeClosure frame (z.1, z.2 - 1)) ∨
      (frame.sGrade z ≤ frame.child.den - frame.child.num - 2 ∧
        freeClosure frame (z.1 + 1, z.2 - 1)) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨hs1, hs2⟩ := freeV_odd_s frame hz hodd
  have hy1 := freeV_odd_y_pos frame hz hodd
  have hE := freeV_mem_E frame hz
  have hpar := sGrade_even frame z
  have hnodd := frame.child_odd
  have hid := num_sGrade_eq frame z
  have hev' : ¬ (z.1 + z.2) % 2 = 0 := hodd
  rw [frame.mem_closedPolygon_iff z] at hE
  rcases hE with ⟨he, -⟩ | ⟨-, ht1, ht2, -, -⟩
  · exact absurd he hodd
  by_cases hs3 : frame.child.den - frame.child.num ≤ frame.sGrade z
  · -- the down neighbour (z_1, z_2 - 1) is even and in freeV
    have htw : frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
      unfold ChildFrame.tGrade; ring
    have hsw : frame.sGrade (z.1, z.2 - 1) = frame.sGrade z - (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade; ring
    have hwev : EvenSite (z.1, z.2 - 1) := by
      unfold EvenSite; simp only; omega
    have hlow : frame.tGrade z ≤ frame.child.num - 2 := by
      by_contra hcon
      push Not at hcon
      have hLt : (frame.child.den + frame.child.num) * (frame.child.num - 1) ≤
          (frame.child.den + frame.child.num) * frame.tGrade z :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hA : frame.child.num * frame.sGrade z ≤
          frame.child.num * ((frame.child.den + frame.child.num) - 2) :=
        mul_le_mul_of_nonneg_left (by omega) hn0.le
      have hB : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * z.2 :=
        mul_le_mul_of_nonneg_left hy1 (by omega)
      have key : frame.child.num * ((frame.child.den + frame.child.num) - 2) -
          frame.child.periodDenominator - (frame.child.den + frame.child.num) * (frame.child.num - 1) < 0 := by
        rw [hTd]; nlinarith
      nlinarith
    refine Or.inl ⟨hs3, fc_of_freeV frame (memV_even frame hwev ?_ ?_ ?_ ?_)⟩
    · rw [htw]; omega
    · rw [htw]; omega
    · rw [hsw]; omega
    · rw [hsw]; omega
  · -- the diagonal neighbour (z_1 + 1, z_2 - 1) is odd and in freeV
    have hs4 : frame.sGrade z ≤ frame.child.den - frame.child.num - 2 := by omega
    have hw : ¬ EvenSite (z.1 + 1, z.2 - 1) := by
      unfold EvenSite at hev' ⊢; simp only at hev' ⊢; omega
    have htw : frame.tGrade (z.1 + 1, z.2 - 1) = frame.tGrade z + (frame.child.den + frame.child.num) := by
      unfold ChildFrame.tGrade; ring
    have hsw : frame.sGrade (z.1 + 1, z.2 - 1) = frame.sGrade z + 2 * frame.child.num := by
      unfold ChildFrame.sGrade; ring
    have hlow : frame.tGrade z ≤ -frame.child.num := by
      by_contra hcon
      push Not at hcon
      have hLt : (frame.child.den + frame.child.num) * (1 - frame.child.num) ≤
          (frame.child.den + frame.child.num) * frame.tGrade z :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hA : frame.child.num * frame.sGrade z ≤
          frame.child.num * ((frame.child.den - frame.child.num) - 2) :=
        mul_le_mul_of_nonneg_left (by omega) hn0.le
      have hB : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * z.2 :=
        mul_le_mul_of_nonneg_left hy1 (by omega)
      have key : frame.child.num * ((frame.child.den - frame.child.num) - 2) -
          frame.child.periodDenominator - (frame.child.den + frame.child.num) * (1 - frame.child.num) < 0 := by
        rw [hTd]; nlinarith
      nlinarith
    refine Or.inr ⟨hs4, fc_of_freeV frame (memV_odd frame hw ?_ ?_ ?_ ?_)⟩
    · rw [htw]; omega
    · rw [htw]; omega
    · rw [hsw]; omega
    · rw [hsw]; omega

/-! ### The V1 claims for even free V sites -/

/-- An even free V site with `s ≥ 2` has its down neighbour in freeV. -/
theorem V1D_pos (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z)
    (hs2 : 2 ≤ frame.sGrade z) : (z.1, z.2 - 1) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  obtain ⟨hsa, hsb⟩ := freeV_even_s frame hz hev
  have hy0 := (FLatticePaper.FreeOrbit.freeV_y_range frame hz).1
  have hE := freeV_mem_E frame hz
  rw [frame.mem_closedPolygon_iff z] at hE
  rcases hE with ⟨-, ht1, ht2, -, -⟩ | ⟨ho', -⟩
  swap
  · exact absurd hev ho'
  have hid := num_sGrade_eq frame z
  have hz2p : 1 ≤ z.2 := by
    by_contra hcon
    have hz2e : z.2 = 0 := by omega
    have hs' : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 := by
      unfold ChildFrame.sGrade; rw [hz2e]; ring
    have hz1p : 1 ≤ z.1 := by
      by_contra h2; push Not at h2; nlinarith
    have hLz : (frame.child.den + frame.child.num) * 1 ≤ (frame.child.den + frame.child.num) * z.1 :=
      mul_le_mul_of_nonneg_left hz1p (by omega)
    linarith
  have hneg : frame.tGrade z < 0 := by
    have hA : frame.child.num * frame.sGrade z ≤ frame.child.num * (2 * frame.child.num) :=
      mul_le_mul_of_nonneg_left hsb hn0.le
    have hB : frame.child.periodDenominator * 1 ≤ frame.child.periodDenominator * z.2 :=
      mul_le_mul_of_nonneg_left hz2p (by omega)
    have key : frame.child.num * (2 * frame.child.num) - frame.child.periodDenominator < 0 := by
      rw [hTd]; nlinarith
    by_contra hcon
    push Not at hcon
    have hLt : 0 ≤ (frame.child.den + frame.child.num) * frame.tGrade z :=
      mul_nonneg (by omega) hcon
    nlinarith
  have hwev : ¬ EvenSite (z.1, z.2 - 1) := by
    unfold EvenSite at hev ⊢; simp only at hev ⊢; omega
  have htw : frame.tGrade (z.1, z.2 - 1) = frame.tGrade z + frame.child.den := by
    unfold ChildFrame.tGrade; ring
  have hsw : frame.sGrade (z.1, z.2 - 1) = frame.sGrade z - (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  exact memV_odd frame hwev (by omega) (by omega) (by omega) (by omega)

/-- The lattice step: an even free V site with `s = 0` is a multiple of `V = (n - d, n + d)`. -/
theorem V1D_zero (frame : ChildFrame) {z : Site} (hev : EvenSite z)
    (h0 : frame.sGrade z = 0) :
    ∃ j : ℤ, z.1 = j * (frame.child.num - frame.child.den) ∧ z.2 = j * (frame.child.num + frame.child.den) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hnodd := frame.child_odd
  obtain ⟨a, ha⟩ : ∃ a, frame.child.den + frame.child.num = 2 * a :=
    ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den - frame.child.num = 2 * b :=
    ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  have hna : frame.child.num = a - b := by omega
  have hda : frame.child.den = a + b := by omega
  obtain ⟨u, v, huv⟩ := frame.child_reduced
  have hab : IsCoprime a b := ⟨u + v, v - u, by rw [hna, hda] at huv; linear_combination huv⟩
  have hzeq : a * z.1 + b * z.2 = 0 := by
    unfold ChildFrame.sGrade at h0
    rw [ha, hb] at h0
    linarith
  have hdiv : a ∣ b * z.2 := ⟨-z.1, by linarith⟩
  obtain ⟨k, hk⟩ := hab.dvd_of_dvd_mul_left hdiv
  have ha0 : a ≠ 0 := by omega
  have hz1 : z.1 = -b * k := by
    have h1 : a * (z.1 + b * k) = 0 := by rw [hk] at hzeq; linarith
    have := (mul_eq_zero.mp h1).resolve_left ha0
    linarith
  have hpar : (z.1 + z.2) % 2 = 0 := hev
  have hk2 : k % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      have hsum : z.1 + z.2 = frame.child.num * k := by
        rw [hz1, hk, hna]; ring
      have hsum2 : z.1 + z.2 = 2 * (frame.child.num * m) + frame.child.num := by
        rw [hsum, hm]; ring
      generalize frame.child.num * m = q at hsum2
      omega
  obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  refine ⟨j, ?_, ?_⟩
  · rw [hz1, hj]; linear_combination j * hb
  · rw [hk, hj]; linear_combination (-j) * ha

/-- The down neighbour of an even free V site is free. -/
theorem V1D (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) :
    freeClosure frame (z.1, z.2 - 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  have hsw := freeV_even_s frame hz hev
  have hsev := sGrade_even frame z
  by_cases h0 : frame.sGrade z = 0
  · obtain ⟨j, hj1, hj2⟩ := V1D_zero frame hev h0
    have hs : (frame.child.den - j * (frame.child.num - frame.child.den),
        frame.child.num - j * (frame.child.num + frame.child.den)) ∈ frame.child.modifiedDeck.span := by
      have h := span_comb frame 1 (-j)
      have e : (1 * frame.child.den + (-j) * (frame.child.num - frame.child.den),
          1 * frame.child.num + (-j) * (frame.child.num + frame.child.den)) =
          (frame.child.den - j * (frame.child.num - frame.child.den),
            frame.child.num - j * (frame.child.num + frame.child.den)) := by
        ext <;> dsimp <;> ring
      rw [e] at h
      exact h
    refine ⟨_, hs, Or.inl ?_⟩
    have hpt : (z.1, z.2 - 1) + (frame.child.den - j * (frame.child.num - frame.child.den),
        frame.child.num - j * (frame.child.num + frame.child.den)) = (frame.child.den, frame.child.num - 1) := by
      rw [hj1, hj2]; ext <;> dsimp <;> ring
    rw [hpt]
    have htd : frame.tGrade (frame.child.den, frame.child.num - 1) = frame.child.den := by
      unfold ChildFrame.tGrade; ring
    have hsd : frame.sGrade (frame.child.den, frame.child.num - 1) =
        frame.child.periodDenominator - (frame.child.den - frame.child.num) := by
      unfold ChildFrame.sGrade; rw [hTd]; ring
    have hdodd : ¬ EvenSite (frame.child.den, frame.child.num - 1) := by
      unfold EvenSite; simp only; have := frame.child_odd; omega
    exact memH_odd frame hdodd (by omega) (by omega) (by omega) (by omega)
  · have hs2 : 2 ≤ frame.sGrade z := by omega
    exact fc_of_freeV frame (V1D_pos frame hz hev hs2)

/-! ### The reflection `σ(z) = (V + I) - z` and the up neighbour -/

/-- The reflection `σ(z) = (n - d + 1 - z_1, n + d - 1 - z_2)`, the involution of the free V cut. -/
def sig (frame : ChildFrame) (z : Site) : Site :=
  (frame.child.num - frame.child.den + 1 - z.1, frame.child.num + frame.child.den - 1 - z.2)

theorem sig_sig (frame : ChildFrame) (z : Site) : sig frame (sig frame z) = z := by
  unfold sig; ext <;> dsimp <;> ring

theorem sig_tGrade (frame : ChildFrame) (z : Site) :
    frame.tGrade (sig frame z) = frame.child.num + frame.child.den - frame.child.periodDenominator -
      frame.tGrade z := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  unfold sig ChildFrame.tGrade
  rw [hTd]; ring

theorem sig_sGrade (frame : ChildFrame) (z : Site) :
    frame.sGrade (sig frame z) = 2 * frame.child.num - frame.sGrade z := by
  unfold sig ChildFrame.sGrade; ring

theorem sig_even_iff (frame : ChildFrame) (z : Site) : EvenSite (sig frame z) ↔ EvenSite z := by
  unfold EvenSite sig; simp only; constructor <;> intro h <;> omega

theorem sig_mem_even (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) :
    sig frame z ∈ frame.freeV := by
  have hT := hT_two frame
  have hsw := freeV_even_s frame hz hev
  have hE := freeV_mem_E frame hz
  rw [frame.mem_closedPolygon_iff z] at hE
  rcases hE with ⟨-, ht1, ht2, -, -⟩ | ⟨ho', -⟩
  swap
  · exact absurd hev ho'
  apply memV_even frame ((sig_even_iff frame z).mpr hev)
  · rw [sig_tGrade]; omega
  · rw [sig_tGrade]; omega
  · rw [sig_sGrade]; omega
  · rw [sig_sGrade]; omega

theorem sig_mem_odd (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    sig frame z ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  have hsw := freeV_odd_s frame hz hodd
  have hE := freeV_mem_E frame hz
  rw [frame.mem_closedPolygon_iff z] at hE
  rcases hE with ⟨he, -⟩ | ⟨-, ht1, ht2, -, -⟩
  · exact absurd he hodd
  apply memV_odd frame (fun h => hodd ((sig_even_iff frame z).mp h))
  · rw [sig_tGrade]; omega
  · rw [sig_tGrade]; omega
  · rw [sig_sGrade]; omega
  · rw [sig_sGrade]; omega

/-- The up neighbour of an even free V site is free. -/
theorem V1U (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) :
    freeClosure frame (z.1, z.2 + 1) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := frame.child_facts
  have hT := hT_two frame
  have hsw := freeV_even_s frame hz hev
  have hsev := sGrade_even frame z
  have hnodd := frame.child_odd
  by_cases h2n : frame.sGrade z = 2 * frame.child.num
  · -- the reflected point is a multiple of V, and z + (0,1) = H_0 + (a multiple of V)
    have hu := sig_mem_even frame hz hev
    have hev_u := (sig_even_iff frame z).mpr hev
    have hsu : frame.sGrade (sig frame z) = 0 := by rw [sig_sGrade, h2n]; ring
    obtain ⟨j, hj1, hj2⟩ := V1D_zero frame hev_u hsu
    have hz1 : z.1 = frame.child.num - frame.child.den + 1 - j * (frame.child.num - frame.child.den) := by
      have h1 : frame.child.num - frame.child.den + 1 - z.1 = j * (frame.child.num - frame.child.den) := hj1
      linarith
    have hz2 : z.2 = frame.child.num + frame.child.den - 1 - j * (frame.child.num + frame.child.den) := by
      have h1 : frame.child.num + frame.child.den - 1 - z.2 = j * (frame.child.num + frame.child.den) := hj2
      linarith
    have hs : ((j - 1) * (frame.child.num - frame.child.den), (j - 1) * (frame.child.num + frame.child.den)) ∈
        frame.child.modifiedDeck.span := by
      have h := span_comb frame 0 (j - 1)
      have e : (0 * frame.child.den + (j - 1) * (frame.child.num - frame.child.den),
          0 * frame.child.num + (j - 1) * (frame.child.num + frame.child.den)) =
          ((j - 1) * (frame.child.num - frame.child.den), (j - 1) * (frame.child.num + frame.child.den)) := by
        ext <;> dsimp <;> ring
      rw [e] at h
      exact h
    refine ⟨_, hs, Or.inl ?_⟩
    have hpt : (z.1, z.2 + 1) + ((j - 1) * (frame.child.num - frame.child.den),
        (j - 1) * (frame.child.num + frame.child.den)) = (1, 0) := by
      rw [hz1, hz2]; ext <;> dsimp <;> ring
    rw [hpt]
    have ht1 : frame.tGrade (1, 0) = frame.child.num := by unfold ChildFrame.tGrade; ring
    have hs1 : frame.sGrade (1, 0) = frame.child.den + frame.child.num := by unfold ChildFrame.sGrade; ring
    have hodd10 : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by unfold EvenSite; norm_num
    exact memH_odd frame hodd10 (by omega) (by omega) (by omega) (by omega)
  · have hs2 : 2 ≤ frame.sGrade (sig frame z) := by rw [sig_sGrade]; omega
    have hu := sig_mem_even frame hz hev
    have hev_u := (sig_even_iff frame z).mpr hev
    have hw := V1D_pos frame hu hev_u hs2
    have hodd_w : ¬ EvenSite ((sig frame z).1, (sig frame z).2 - 1) := by
      unfold EvenSite at hev_u ⊢; simp only at hev_u ⊢; omega
    have hw2 := sig_mem_odd frame hw hodd_w
    have hpt : sig frame ((sig frame z).1, (sig frame z).2 - 1) = (z.1, z.2 + 1) := by
      unfold sig; ext <;> dsimp <;> ring
    rw [hpt] at hw2
    exact fc_of_freeV frame hw2

end FLatticePaper.FreeWebClaims
