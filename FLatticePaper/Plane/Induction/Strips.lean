import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Binary

namespace FLatticePaper.Induction
open Farey

/-! The strip inputs of `M` on `E` give both strips of the sewn standard `F`. This first part collects the
arithmetic of the harmonic grid under the transverse vector and under the reflection `R − K`. -/

/-- The harmonic grid under the transverse vector `(n − d, n + d)`: `h0(x + V) = h0(x) + t(x) + c_V`. -/
theorem strip_harmonic_shift (x1 x2 N D P cV : ℤ) (hP : P = D ^ 2 + 2 * D * N - N ^ 2)
    (hcV : 2 * cV = -(D + N + P)) (_hpar : (N + D) % 2 = 0) :
    harmonicGrid (x1 + (N - D), x2 + (N + D)) = harmonicGrid (x1, x2) + (N * x1 - D * x2) + cV := by
  have e1 := harmonicGrid_exact (x1 + (N - D), x2 + (N + D))
  have e2 := harmonicGrid_exact (x1, x2)
  dsimp only at e1 e2
  have hpar' : (x1 + (N - D) + (x2 + (N + D))) % 2 = (x1 + x2) % 2 := by omega
  rw [hpar'] at e1
  have h4 : 4 * harmonicGrid (x1 + (N - D), x2 + (N + D)) =
      4 * (harmonicGrid (x1, x2) + (N * x1 - D * x2) + cV) := by
    linear_combination e1 - e2 + 2 * hP - 2 * hcV
  linarith

/-- The harmonic grid under the reflection `R − K`: `h0(R − K − z) = h0(z) − t(z) + κ`. -/
theorem strip_harmonic_reflect (z1 z2 N D P κ : ℤ) (hP : P = D ^ 2 + 2 * D * N - N ^ 2)
    (hκ : 2 * κ = D + N - P) (_hpar : (N + D) % 2 = 0) :
    harmonicGrid (N - D + 1 - z1, N + D - 1 - z2) = harmonicGrid (z1, z2) - (N * z1 - D * z2) + κ := by
  have e1 := harmonicGrid_exact (N - D + 1 - z1, N + D - 1 - z2)
  have e2 := harmonicGrid_exact (z1, z2)
  dsimp only at e1 e2
  have hpar' : (N - D + 1 - z1 + (N + D - 1 - z2)) % 2 = (z1 + z2) % 2 := by omega
  rw [hpar'] at e1
  have h4 : 4 * harmonicGrid (N - D + 1 - z1, N + D - 1 - z2) =
      4 * (harmonicGrid (z1, z2) - (N * z1 - D * z2) + κ) := by
    linear_combination e1 - e2 - 2 * hκ + 2 * hP
  linarith

theorem ChildFrame.tGrade_pair (frame : ChildFrame) (x1 x2 : ℤ) :
    frame.tGrade (x1, x2) = frame.child.num * x1 - frame.child.den * x2 := by
  unfold ChildFrame.tGrade
  dsimp only

theorem ChildFrame.sGrade_add_pt (frame : ChildFrame) (a b : Site) :
    frame.sGrade (a + b) = frame.sGrade a + frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem ChildFrame.sGrade_kernel_eq (frame : ChildFrame) :
    frame.sGrade frame.child.modifiedDeck.kernel = frame.child.periodDenominator := by
  rw [frame.child_modifiedDeck_kernel]
  unfold ChildFrame.sGrade Fraction.periodDenominator
  dsimp only
  ring

theorem ChildFrame.sGrade_transverse_eq (frame : ChildFrame) :
    frame.sGrade frame.child.modifiedDeck.transverse = 0 := by
  rw [frame.child_modifiedDeck_transverse]
  unfold ChildFrame.sGrade
  dsimp only
  ring

theorem ChildFrame.evenSite_add_kernel (frame : ChildFrame) (z : Site) :
    EvenSite (z + frame.child.modifiedDeck.kernel) ↔ EvenSite z := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  rw [frame.child_modifiedDeck_kernel]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

theorem ChildFrame.evenSite_add_transverse (frame : ChildFrame) (z : Site) :
    EvenSite (z + frame.child.modifiedDeck.transverse) ↔ EvenSite z := by
  rw [frame.child_modifiedDeck_transverse]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

theorem ChildFrame.centre_sub_kernel (frame : ChildFrame) (z : Site) :
    frame.centre - (z + frame.child.modifiedDeck.kernel) =
      (frame.child.num - frame.child.den + 1 - z.1, frame.child.num + frame.child.den - 1 - z.2) := by
  unfold ChildFrame.centre
  rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
  exact Prod.ext (by simp only [Prod.fst_sub, Prod.fst_add]; ring)
    (by simp only [Prod.snd_sub, Prod.snd_add]; ring)

theorem ChildFrame.harmonicGrid_add_transverse (frame : ChildFrame) (x : Site) :
    harmonicGrid (x + frame.child.modifiedDeck.transverse) =
      harmonicGrid x + frame.tGrade x + frame.coherentConstantV := by
  obtain ⟨-, -, -, -, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hcV := frame.coherentConstantV_eq
  obtain ⟨x1, x2⟩ := x
  rw [frame.child_modifiedDeck_transverse, Prod.mk_add_mk, frame.tGrade_pair]
  exact strip_harmonic_shift x1 x2 _ _ _ _ hP hcV hev

theorem ChildFrame.harmonicGrid_reflect (frame : ChildFrame) (z : Site) :
    harmonicGrid (frame.centre - (z + frame.child.modifiedDeck.kernel)) =
      harmonicGrid z - frame.tGrade z + frame.symmetryConstant := by
  obtain ⟨-, -, -, -, hP⟩ := frame.child_facts
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT := frame.T_even
  have hκ : 2 * frame.symmetryConstant =
      frame.child.den + frame.child.num - frame.child.periodDenominator := by
    unfold ChildFrame.symmetryConstant
    omega
  obtain ⟨z1, z2⟩ := z
  rw [frame.centre_sub_kernel, frame.tGrade_pair]
  exact strip_harmonic_reflect z1 z2 _ _ _ _ hP hκ hev

/-! ### Shifts along the kernel and the transverse vector -/

theorem ChildFrame.T_ge (frame : ChildFrame) :
    2 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator := by
  obtain ⟨hN1, hNlt, hND, -, hP⟩ := frame.child_facts
  rw [hP]
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ frame.child.den + frame.child.num)
      (by omega : (0 : ℤ) ≤ frame.child.den - frame.child.num - 2),
    mul_pos hN1 (by omega : (0 : ℤ) < frame.child.den)]

theorem ChildFrame.periodDen_pos (frame : ChildFrame) : 0 < frame.child.periodDenominator := by
  have := frame.T_ge
  obtain ⟨hN1, hNlt, -, -, -⟩ := frame.child_facts
  omega

theorem ChildFrame.sGrade_smul (frame : ChildFrame) (q : ℤ) (x : Site) :
    frame.sGrade (q • x) = q * frame.sGrade x := by
  unfold ChildFrame.sGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem ChildFrame.tGrade_smul (frame : ChildFrame) (q : ℤ) (x : Site) :
    frame.tGrade (q • x) = q * frame.tGrade x := by
  unfold ChildFrame.tGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Every integer `s` has a multiple of `T` moving it into any window `[c, c + T)`. -/
theorem strip_shift_exists (s c T : ℤ) (hT : 0 < T) :
    ∃ q : ℤ, c ≤ s + q * T ∧ s + q * T < c + T := by
  have hk := Int.emod_def (s - c) T
  have hr0 := Int.emod_nonneg (s - c) hT.ne'
  have hr1 := Int.emod_lt_of_pos (s - c) hT
  refine ⟨-((s - c) / T), ?_, ?_⟩
  · linarith
  · linarith

/-- Moving along `q • K` shifts the `s`-grade by `q T` and leaves the `t`-grade unchanged. -/
theorem ChildFrame.exists_shift_K (frame : ChildFrame) (z : Site) (c : ℤ) :
    ∃ q : ℤ, c ≤ frame.sGrade (z + q • frame.child.modifiedDeck.kernel) ∧
      frame.sGrade (z + q • frame.child.modifiedDeck.kernel) < c + frame.child.periodDenominator := by
  obtain ⟨q, h1, h2⟩ := strip_shift_exists (frame.sGrade z) c frame.child.periodDenominator frame.periodDen_pos
  have hs : frame.sGrade (z + q • frame.child.modifiedDeck.kernel) =
      frame.sGrade z + q * frame.child.periodDenominator := by
    rw [frame.sGrade_add_pt, frame.sGrade_smul, frame.sGrade_kernel_eq]
  refine ⟨q, ?_, ?_⟩
  · rw [hs]; exact h1
  · rw [hs]; exact h2

/-- Moving along `p • V` shifts the `t`-grade by `−p T` and leaves the `s`-grade unchanged. -/
theorem ChildFrame.exists_shift_V (frame : ChildFrame) (z : Site) (a : ℤ) :
    ∃ p : ℤ, a ≤ frame.tGrade (z + p • frame.child.modifiedDeck.transverse) ∧
      frame.tGrade (z + p • frame.child.modifiedDeck.transverse) < a + frame.child.periodDenominator := by
  obtain ⟨q, h1, h2⟩ := strip_shift_exists (frame.tGrade z) a frame.child.periodDenominator frame.periodDen_pos
  have hs : frame.tGrade (z + (-q) • frame.child.modifiedDeck.transverse) =
      frame.tGrade z + q * frame.child.periodDenominator := by
    rw [frame.tGrade_add_pt, frame.tGrade_smul, frame.tGrade_transverse_eq]
    ring
  refine ⟨-q, ?_, ?_⟩
  · rw [hs]; exact h1
  · rw [hs]; exact h2

/-- With `c_U = 0` the field is periodic under the kernel. -/
theorem ChildFrame.periodic_kernel (frame : ChildFrame) {F : Field}
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site) (q : ℤ) :
    F (z + q • frame.child.modifiedDeck.kernel) = F z := by
  have hK : Function.Periodic F frame.child.modifiedDeck.kernel := fun x => by
    rw [hper.1 x, add_zero]
  exact (hK.zsmul q) z

/-- One step along the transverse vector: `F (x + V) = F x + t(x) + c_V`. -/
theorem ChildFrame.field_transverse (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (x : Site) :
    F (x + frame.child.modifiedDeck.transverse) = F x + frame.tGrade x + cV := by
  rw [hper.2 x, frame.transverseGrade_eq_neg]
  ring

/-! ### The zero strip -/

/-- The strip inputs: the parts of the zero strip and the harmonic strip inside `E`, and the reflection on `E`. -/
structure ChildFrame.StripInputs (frame : ChildFrame) (M : Site → ℤ) : Prop where
  zero : ∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → M z = 0
  harmonic : ∀ z ∈ frame.closedPolygon,
    frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 → M z = harmonicGrid z
  reflection : ∀ z ∈ frame.closedPolygon,
    M (frame.centre - z) = M z - frame.tGrade z + frame.symmetryConstant

theorem ChildFrame.evenSite_add_smul_kernel (frame : ChildFrame) (z : Site) (q : ℤ) :
    EvenSite (z + q • frame.child.modifiedDeck.kernel) ↔ EvenSite z := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.child.num + frame.child.den = 2 * m :=
    ⟨(frame.child.num + frame.child.den) / 2, by
      have h := frame.child_even
      unfold Fraction.Even at h
      omega⟩
  rw [frame.child_modifiedDeck_kernel]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e : z.1 + q * frame.child.den + (z.2 + q * frame.child.num) = (z.1 + z.2) + 2 * (q * m) := by
    linear_combination q * hm
  rw [e, Int.add_mul_emod_self_left]

theorem ChildFrame.evenSite_add_smul_transverse (frame : ChildFrame) (z : Site) (p : ℤ) :
    EvenSite (z + p • frame.child.modifiedDeck.transverse) ↔ EvenSite z := by
  rw [frame.child_modifiedDeck_transverse]
  unfold EvenSite
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e : z.1 + p * (frame.child.num - frame.child.den) + (z.2 + p * (frame.child.num + frame.child.den)) =
      (z.1 + z.2) + 2 * (p * frame.child.num) := by
    ring
  rw [e, Int.add_mul_emod_self_left]

theorem ChildFrame.tGrade_add_smul_kernel (frame : ChildFrame) (z : Site) (q : ℤ) :
    frame.tGrade (z + q • frame.child.modifiedDeck.kernel) = frame.tGrade z := by
  rw [frame.tGrade_add_pt, frame.tGrade_smul, frame.tGrade_kernel_zero]
  ring

theorem ChildFrame.sGrade_add_smul_transverse (frame : ChildFrame) (z : Site) (p : ℤ) :
    frame.sGrade (z + p • frame.child.modifiedDeck.transverse) = frame.sGrade z := by
  rw [frame.sGrade_add_pt, frame.sGrade_smul, frame.sGrade_transverse_eq]
  ring

theorem ChildFrame.two_symmetry_eq (frame : ChildFrame) :
    2 * frame.symmetryConstant = frame.child.den + frame.child.num - frame.child.periodDenominator := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hT := frame.T_even
  unfold ChildFrame.symmetryConstant
  omega

/-- A site whose transverse neighbour lies in `E` takes the zero value by the reflection through that
neighbour. -/
theorem ChildFrame.zero_of_transverse_mem (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hy : z + frame.child.modifiedDeck.transverse ∈ frame.closedPolygon)
    (_hlo : 1 - frame.child.den ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) : F z = 0 := by
  have hF := frame.field_transverse hper z
  have hw := frame.centre_sub_mem hy
  have hκ := frame.two_symmetry_eq
  have hcV := frame.coherentConstantV_eq
  have hMw : M (frame.centre - (z + frame.child.modifiedDeck.transverse)) = 0 := by
    apply h.zero _ hw
    rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_pt, frame.tGrade_transverse_eq]
    omega
  have htw : frame.tGrade (frame.centre - (z + frame.child.modifiedDeck.transverse)) =
      frame.child.den + frame.child.num - frame.tGrade z := by
    rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_pt, frame.tGrade_transverse_eq]
    ring
  have hR := h.reflection _ hw
  rw [sub_sub_cancel] at hR
  have hFy := hagree _ hy
  linarith

/-- The zero strip, once the `s`-grade of the site lies in the window of its parity. -/
theorem ChildFrame.zero_core (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - frame.child.den ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1)
    (hs : (EvenSite z → 0 ≤ frame.sGrade z ∧ frame.sGrade z < frame.child.periodDenominator) ∧
      (¬ EvenSite z → 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z < 2 - frame.child.den + frame.child.num + frame.child.periodDenominator)) :
    F z = 0 := by
  have hT := frame.T_ge
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  have hsV : frame.sGrade (z + frame.child.modifiedDeck.transverse) = frame.sGrade z := by
    rw [frame.sGrade_add_pt, frame.sGrade_transverse_eq]
    ring
  have htV : frame.tGrade (z + frame.child.modifiedDeck.transverse) =
      frame.tGrade z - frame.child.periodDenominator := by
    rw [frame.tGrade_add_pt, frame.tGrade_transverse_eq]
    ring
  by_cases he : EvenSite z
  · obtain ⟨hs0, hs1⟩ := hs.1 he
    by_cases hb : frame.tGrade z ≤ frame.child.den + frame.child.num - 2
    · have hmem : z ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff z).mpr
        (Or.inl ⟨he, by omega, hb, hs0, by omega⟩)
      rw [hagree z hmem]
      exact h.zero z hmem hlo
    · refine frame.zero_of_transverse_mem h hagree hper z ?_ hlo hhi
      exact (frame.mem_closedPolygon_iff _).mpr (Or.inl ⟨(frame.evenSite_add_transverse z).mpr he,
        by rw [htV]; omega, by rw [htV]; omega, by rw [hsV]; omega, by rw [hsV]; omega⟩)
  · obtain ⟨hs0, hs1⟩ := hs.2 he
    by_cases hb : frame.tGrade z ≤ frame.child.den
    · have hmem : z ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff z).mpr
        (Or.inr ⟨he, by omega, hb, hs0, by omega⟩)
      rw [hagree z hmem]
      exact h.zero z hmem hlo
    · refine frame.zero_of_transverse_mem h hagree hper z ?_ hlo hhi
      exact (frame.mem_closedPolygon_iff _).mpr (Or.inr ⟨fun hh => he ((frame.evenSite_add_transverse z).mp hh),
        by rw [htV]; omega, by rw [htV]; omega, by rw [hsV]; omega, by rw [hsV]; omega⟩)

/-- The zero strip of `F`. -/
theorem ChildFrame.zero_strip (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - frame.child.den ≤ frame.tGrade z)
    (hhi : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) : F z = 0 := by
  by_cases he : EvenSite z
  · obtain ⟨q, hq1, hq2⟩ := frame.exists_shift_K z 0
    have hpar := frame.evenSite_add_smul_kernel z q
    rw [← frame.periodic_kernel hper z q]
    refine frame.zero_core h hagree hper _ (by rw [frame.tGrade_add_smul_kernel]; exact hlo)
      (by rw [frame.tGrade_add_smul_kernel]; exact hhi)
      ⟨fun _ => ⟨hq1, by linarith⟩, fun hn => absurd (hpar.mpr he) hn⟩
  · obtain ⟨q, hq1, hq2⟩ := frame.exists_shift_K z (2 - frame.child.den + frame.child.num)
    have hpar := frame.evenSite_add_smul_kernel z q
    rw [← frame.periodic_kernel hper z q]
    refine frame.zero_core h hagree hper _ (by rw [frame.tGrade_add_smul_kernel]; exact hlo)
      (by rw [frame.tGrade_add_smul_kernel]; exact hhi)
      ⟨fun hE => absurd (hpar.mp hE) he, fun _ => ⟨hq1, hq2⟩⟩

/-! ### The harmonic strip -/

/-- A site whose kernel neighbour lies in `E` takes the harmonic value by the reflection through that neighbour. -/
theorem ChildFrame.harmonic_of_kernel_mem (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - 2 * frame.child.den ≤ frame.sGrade z)
    (hyE : z + frame.child.modifiedDeck.kernel ∈ frame.closedPolygon) : F z = harmonicGrid z := by
  have hT := frame.T_ge
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  have hK : F (z + frame.child.modifiedDeck.kernel) = F z := by
    have := frame.periodic_kernel hper z 1
    rw [one_smul] at this
    exact this
  have hw := frame.centre_sub_mem hyE
  have hMw := h.harmonic _ hw (by
    rw [frame.sGrade_sub, frame.sGrade_centre, frame.sGrade_add_pt, frame.sGrade_kernel_eq]
    omega)
  have hR := h.reflection _ hw
  rw [sub_sub_cancel] at hR
  have hFy := hagree _ hyE
  have htw : frame.tGrade (frame.centre - (z + frame.child.modifiedDeck.kernel)) =
      frame.child.den + frame.child.num - frame.child.periodDenominator - frame.tGrade z := by
    rw [frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_add_pt, frame.tGrade_kernel_zero, add_zero]
  have hh := frame.harmonicGrid_reflect z
  have hκ := frame.two_symmetry_eq
  linarith

/-- The harmonic strip, once the `t`-grade of the site lies in the window of its parity. -/
theorem ChildFrame.harmonic_core (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - 2 * frame.child.den ≤ frame.sGrade z)
    (hhi : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1)
    (ht : (EvenSite z → 2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z < 2) ∧
      (¬ EvenSite z → frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
        frame.tGrade z < frame.child.num)) :
    F z = harmonicGrid z := by
  have hT := frame.T_ge
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  have htK : frame.tGrade (z + frame.child.modifiedDeck.kernel) = frame.tGrade z := by
    rw [frame.tGrade_add_pt, frame.tGrade_kernel_zero, add_zero]
  have hsK : frame.sGrade (z + frame.child.modifiedDeck.kernel) =
      frame.sGrade z + frame.child.periodDenominator := by
    rw [frame.sGrade_add_pt, frame.sGrade_kernel_eq]
  by_cases he : EvenSite z
  · obtain ⟨ht1, ht2⟩ := ht.1 he
    by_cases hs : 0 ≤ frame.sGrade z
    · have hmem : z ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff z).mpr
        (Or.inl ⟨he, ht1, by omega, hs, by omega⟩)
      rw [hagree z hmem]
      exact h.harmonic z hmem hhi
    · have hyE : z + frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff _).mpr
        (Or.inl ⟨(frame.evenSite_add_kernel z).mpr he, by rw [htK]; exact ht1, by rw [htK]; omega,
          by rw [hsK]; omega, by rw [hsK]; omega⟩)
      exact frame.harmonic_of_kernel_mem h hagree hper z hlo hyE
  · obtain ⟨ht1, ht2⟩ := ht.2 he
    by_cases hs : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z
    · have hmem : z ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff z).mpr
        (Or.inr ⟨he, ht1, by omega, hs, by omega⟩)
      rw [hagree z hmem]
      exact h.harmonic z hmem hhi
    · have hyE : z + frame.child.modifiedDeck.kernel ∈ frame.closedPolygon := (frame.mem_closedPolygon_iff _).mpr
        (Or.inr ⟨fun hh => he ((frame.evenSite_add_kernel z).mp hh), by rw [htK]; exact ht1,
          by rw [htK]; omega, by rw [hsK]; omega, by rw [hsK]; omega⟩)
      exact frame.harmonic_of_kernel_mem h hagree hper z hlo hyE

/-- The harmonic strip of `F`: `F − h0` is periodic under the transverse vector. -/
theorem ChildFrame.harmonic_strip (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 1 - 2 * frame.child.den ≤ frame.sGrade z)
    (hhi : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1) : F z = harmonicGrid z := by
  have hG : Function.Periodic (fun x => F x - harmonicGrid x) frame.child.modifiedDeck.transverse := by
    intro x
    show F (x + frame.child.modifiedDeck.transverse) - harmonicGrid (x + frame.child.modifiedDeck.transverse) =
      F x - harmonicGrid x
    rw [frame.field_transverse hper x, frame.harmonicGrid_add_transverse x]
    ring
  by_cases he : EvenSite z
  · obtain ⟨p, hp1, hp2⟩ := frame.exists_shift_V z (2 - frame.child.periodDenominator)
    have hGz : F (z + p • frame.child.modifiedDeck.transverse) -
        harmonicGrid (z + p • frame.child.modifiedDeck.transverse) = F z - harmonicGrid z :=
      hG.zsmul p z
    have hs := frame.sGrade_add_smul_transverse z p
    have hpar := frame.evenSite_add_smul_transverse z p
    have hF1 := frame.harmonic_core h hagree hper (z + p • frame.child.modifiedDeck.transverse)
      (by rw [hs]; exact hlo) (by rw [hs]; exact hhi)
      ⟨fun _ => ⟨hp1, by omega⟩, fun hn => absurd (hpar.mpr he) hn⟩
    linarith
  · obtain ⟨p, hp1, hp2⟩ := frame.exists_shift_V z (frame.child.num - frame.child.periodDenominator)
    have hGz : F (z + p • frame.child.modifiedDeck.transverse) -
        harmonicGrid (z + p • frame.child.modifiedDeck.transverse) = F z - harmonicGrid z :=
      hG.zsmul p z
    have hs := frame.sGrade_add_smul_transverse z p
    have hpar := frame.evenSite_add_smul_transverse z p
    have hF1 := frame.harmonic_core h hagree hper (z + p • frame.child.modifiedDeck.transverse)
      (by rw [hs]; exact hlo) (by rw [hs]; exact hhi)
      ⟨fun hE => absurd (hpar.mp hE) he, fun _ => ⟨hp1, by omega⟩⟩
    linarith

/-! ### The two theorems of the task -/

/-- The strip inputs are the height inputs: the bands lie in the zero strip and the harmonic strip. -/
theorem ChildFrame.StripInputs.heightInputs {frame : ChildFrame} {M : Site → ℤ} (h : frame.StripInputs M) :
    frame.HeightInputs M := by
  obtain ⟨hN1, hNlt, hND, hD3, -⟩ := frame.child_facts
  refine ⟨fun z hz => ?_, fun z hz => ?_, h.reflection⟩
  · obtain ⟨hE, hwin⟩ := (frame.mem_hBand_iff z).mp hz
    apply h.zero z hE
    split_ifs at hwin with he <;> omega
  · obtain ⟨hE, hwin⟩ := (frame.mem_vBand_iff z).mp hz
    apply h.harmonic z hE
    split_ifs at hwin with he <;> omega

/-- The strip inputs of `M` on `E` give both strips of any field `F` that agrees with `M` on `E` and has
the coherent period constants. -/
theorem ChildFrame.hasStrips_of_stripInputs (frame : ChildFrame) {M : Site → ℤ} (h : frame.StripInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV) :
    frame.HasStrips F := by
  rw [frame.coherentConstantU_eq_zero] at hper
  unfold ChildFrame.HasStrips
  exact ⟨fun z hlo hhi => frame.zero_strip h hagree hper z hlo hhi,
    fun z hlo hhi => frame.harmonic_strip h hagree hper z hlo hhi⟩

end FLatticePaper.Induction
