import FLatticePaper.Plane.Induction.BaseReflection

/-! The upper bound `D ≤ 2` on `E` from the recurrent comparison (task 36, item 3).

The comparison is applied to `M` (the sheet minimum, which equals `F` on `E`) against the competitor `F(· + σ) + 2`, on
the finite set `D` of sites of `E` whose four lattice neighbours all lie in `E`. Its incoming boundary lies in `E` and
off `D`, so it consists of boundary sites of `E`, where `D ≤ 2` is assumed. The recurrence of `M` enters only through the
fort form `RecurrentField M`, which is the one hypothesis left in this file. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The four lattice neighbours of `x` all lie in `E`. -/
def FourNbr (E : Set Site) (x : Site) : Prop :=
  x + (1, 0) ∈ E ∧ x + (-1, 0) ∈ E ∧ x + (0, 1) ∈ E ∧ x + (0, -1) ∈ E

theorem edge_mem_of_fourNbr {E : Set Site} {x y : Site} (hx : FourNbr E x) (hE : Edge y x) : y ∈ E := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  unfold Edge incomingNeg incomingPos at hE
  have e1 : (x.1 - 1, x.2) = x + (-1, 0) := Prod.ext (by simp [sub_eq_add_neg]) (by simp)
  have e2 : (x.1 + 1, x.2) = x + (1, 0) := Prod.ext (by simp) (by simp)
  have e3 : (x.1, x.2 - 1) = x + (0, -1) := Prod.ext (by simp) (by simp [sub_eq_add_neg])
  have e4 : (x.1, x.2 + 1) = x + (0, 1) := Prod.ext (by simp) (by simp)
  split_ifs at hE with hpar
  · rcases hE with rfl | rfl
    · rw [e1]; exact h2
    · rw [e2]; exact h1
  · rcases hE with rfl | rfl
    · rw [e3]; exact h4
    · rw [e4]; exact h3

theorem onBoundary_of_not_fourNbr {E : Set Site} {y : Site} (hy : y ∈ E) (h : ¬ FourNbr E y) :
    OnBoundary E y := by
  unfold OnBoundary OutwardDir
  by_contra hc
  apply h
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hn; exact hc (Or.inr (Or.inr (Or.inl ⟨hy, hn⟩)))
  · by_contra hn; exact hc (Or.inr (Or.inr (Or.inr ⟨hy, hn⟩)))
  · by_contra hn; exact hc (Or.inl ⟨hy, hn⟩)
  · by_contra hn; exact hc (Or.inr (Or.inl ⟨hy, hn⟩))

/-- The laplacian of a shifted field is the laplacian of the field at the shifted site (even shift). -/
theorem laplacian_shift_even (F : Field) (σ x : Site) (hσ : EvenSite σ) :
    laplacian (fun z => F (z + σ) + 2) x = laplacian F (x + σ) := by
  unfold laplacian
  simp only
  rw [← incomingNeg_add_of_even x σ hσ, ← incomingPos_add_of_even x σ hσ]
  ring

/-- If `T ≥ 1` and `T x` lies in `[−M, M]`, then so does `x`. -/
theorem abs_bound_of_mul (T x M : ℤ) (hT : 1 ≤ T) (h1 : T * x ≤ M) (h2 : -M ≤ T * x) :
    -M ≤ x ∧ x ≤ M := by
  rcases le_total 0 x with hx | hx
  · have hle : x ≤ T * x := le_mul_of_one_le_left hx hT
    constructor <;> linarith
  · have hle : (T - 1) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hx
    constructor <;> linarith

/-- `E` is bounded: its sites have coordinates bounded by `R = 3 d (T + L)`. -/
theorem closedPolygon_box (frame : ChildFrame) :
    ∃ R : ℤ, ∀ z ∈ frame.closedPolygon, -R ≤ z.1 ∧ z.1 ≤ R ∧ -R ≤ z.2 ∧ z.2 ≤ R := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  refine ⟨3 * frame.child.den * (frame.child.periodDenominator + (frame.child.den + frame.child.num)), ?_⟩
  intro z hz
  have hB : -(frame.child.periodDenominator + (frame.child.den + frame.child.num)) ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.periodDenominator + (frame.child.den + frame.child.num) ∧
      -(frame.child.periodDenominator + (frame.child.den + frame.child.num)) ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + (frame.child.den + frame.child.num) := by
    rw [frame.mem_closedPolygon_iff] at hz
    unfold EvenSite at *
    omega
  have hx : frame.child.periodDenominator * z.1 =
      (frame.child.den - frame.child.num) * frame.tGrade z + frame.child.den * frame.sGrade z := by
    rw [hTform]; unfold ChildFrame.tGrade ChildFrame.sGrade; ring
  have hy : frame.child.periodDenominator * z.2 =
      frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z := by
    rw [hTform]; unfold ChildFrame.tGrade ChildFrame.sGrade; ring
  obtain ⟨h1, h2, h3, h4⟩ := hB
  have hdn' : 0 ≤ frame.child.den - frame.child.num := by omega
  have hd0 : 0 ≤ frame.child.den := by omega
  have hn0' : 0 ≤ frame.child.num := by omega
  have hL0 : 0 ≤ frame.child.den + frame.child.num := by omega
  have hTL : 0 ≤ frame.child.periodDenominator + (frame.child.den + frame.child.num) := by omega
  have hT1 : 1 ≤ frame.child.periodDenominator := by omega
  have ax1 := mul_le_mul_of_nonneg_left h2 hdn'
  have ax2 := mul_le_mul_of_nonneg_left h1 hdn'
  have ay1 := mul_le_mul_of_nonneg_left h4 hd0
  have ay2 := mul_le_mul_of_nonneg_left h3 hd0
  have ay3 := mul_le_mul_of_nonneg_left h4 hn0'
  have ay4 := mul_le_mul_of_nonneg_left h3 hn0'
  have ay5 := mul_le_mul_of_nonneg_left h2 hL0
  have ay6 := mul_le_mul_of_nonneg_left h1 hL0
  have hdB := mul_nonneg hd0 hTL
  have hLB := mul_nonneg hL0 hTL
  have hnB := mul_nonneg hn0' hTL
  have hxu : frame.child.periodDenominator * z.1 ≤
      3 * frame.child.den * (frame.child.periodDenominator + (frame.child.den + frame.child.num)) := by
    linarith
  have hxl : -(3 * frame.child.den * (frame.child.periodDenominator + (frame.child.den + frame.child.num))) ≤
      frame.child.periodDenominator * z.1 := by
    linarith
  have hyu : frame.child.periodDenominator * z.2 ≤
      3 * frame.child.den * (frame.child.periodDenominator + (frame.child.den + frame.child.num)) := by
    linarith
  have hyl : -(3 * frame.child.den * (frame.child.periodDenominator + (frame.child.den + frame.child.num))) ≤
      frame.child.periodDenominator * z.2 := by
    linarith
  have hX := abs_bound_of_mul _ _ _ hT1 hxu hxl
  have hY := abs_bound_of_mul _ _ _ hT1 hyu hyl
  exact ⟨hX.1, hX.2, hY.1, hY.2⟩

/-- The upper bound `D ≤ 2` on `E`: the recurrent comparison of `M` against `F(· + σ) + 2` on the finite set `D` of sites
of `E` whose four neighbours lie in `E`. Its incoming boundary lies in `E` and off `D`, hence on the boundary of `E`, where
`D ≤ 2` is assumed. -/
theorem upper_of_recurrent (frame : ChildFrame) {F M : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hbinF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hbinM : ∀ z, laplacian M z = -1 ∨ laplacian M z = 0) (hrec : RecurrentField M)
    (hbd : ∀ z, OnBoundary frame.closedPolygon z → starDiff F frame.shortShift z ≤ 2) :
    ∀ x ∈ frame.closedPolygon, starDiff F frame.shortShift x ≤ 2 := by
  classical
  obtain ⟨R, hR⟩ := closedPolygon_box frame
  have hσ : EvenSite frame.shortShift := evenSite_shortShift frame
  set D : Finset Site := (Finset.Icc (-R, -R) (R, R)).filter
    (fun z => FourNbr frame.closedPolygon z ∧ z ∈ frame.closedPolygon) with hDdef
  have hmemD : ∀ z, z ∈ D ↔ (FourNbr frame.closedPolygon z ∧ z ∈ frame.closedPolygon) := by
    intro z
    constructor
    · intro hz
      exact (Finset.mem_filter.mp hz).2
    · rintro ⟨h1, h2⟩
      obtain ⟨a, b, c, e⟩ := hR z h2
      rw [hDdef, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Prod.mk_le_mk.mpr ⟨by omega, by omega⟩, Prod.mk_le_mk.mpr ⟨by omega, by omega⟩⟩, h1, h2⟩
  have hA : ∀ x ∈ D, laplacian (fun z => F (z + frame.shortShift) + 2) x = -1 ∨
      laplacian (fun z => F (z + frame.shortShift) + 2) x = 0 := by
    intro x _
    rw [laplacian_shift_even F frame.shortShift x hσ]
    exact hbinF _
  have hbd' : ∀ y x, x ∈ D → Edge y x → y ∉ D → M y ≤ (fun z => F (z + frame.shortShift) + 2) y := by
    intro y x hxD hE hyD
    have hxN := (hmemD x).mp hxD
    have hyE : y ∈ frame.closedPolygon := edge_mem_of_fourNbr hxN.1 hE
    have hnot : ¬ FourNbr frame.closedPolygon y := fun h => hyD ((hmemD y).mpr ⟨h, hyE⟩)
    have hb := hbd y (onBoundary_of_not_fourNbr hyE hnot)
    have hMy := hagree y hyE
    unfold starDiff at hb
    show M y ≤ F (y + frame.shortShift) + 2
    omega
  have key := recurrent_comparison (fun z => F (z + frame.shortShift) + 2) M D hbinM hrec hA hbd'
  intro x hx
  by_cases hN : FourNbr frame.closedPolygon x
  · have hk := key x ((hmemD x).mpr ⟨hN, hx⟩)
    have hMx := hagree x hx
    unfold starDiff
    omega
  · exact hbd x (onBoundary_of_not_fourNbr hx hN)

/-- The base range of `D` on `E`, from the strips, the reflection, the recurrence of `M` (fort form) and the V arcs.
The bottom and top arcs are proved; the V arcs are the input `arcs`. -/
theorem base_range_of_inputs (frame : ChildFrame) {F M : Field} {cU cV : ℤ}
    (hS : frame.StripInputs M) (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper0 : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hrefl : ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant)
    (hbinF : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hbinM : ∀ z, laplacian M z = -1 ∨ laplacian M z = 0) (hrecM : RecurrentField M)
    (arcs : VArcInputs frame F) :
    ∀ x ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift x ∧ starDiff F frame.shortShift x ≤ 2 := by
  have hbot := bottomZero_of_strip frame hS hagree hper0
  have htop := topTwo_of_strip frame hS hagree hper0
  have hbd : ∀ z, OnBoundary frame.closedPolygon z → starDiff F frame.shortShift z ≤ 2 := by
    intro z hz
    rcases onBoundary_cover frame.closedPolygon hz with hb | ht | hv
    · rw [hbot z hb]; norm_num
    · rw [htop z ht]
    · rcases arcs.leftRange z hv with h | h | h <;> rw [h] <;> norm_num
  have hup := upper_of_recurrent frame hagree hbinF hbinM hrecM hbd
  have hlow := lower_of_upper frame hper hrefl hup
  intro x hx
  exact ⟨hlow x hx, hup x hx⟩

end FLatticePaper.Induction
