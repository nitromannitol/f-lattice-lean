import FLatticePaper.Plane.Induction.Coherence
import FLatticePaper.Plane.Induction.Seams

namespace FLatticePaper.Induction
open Farey

/-! The sewn standard has the central reflection on the whole plane, and the period constants it forces. -/

/-- `2κ = L − T`: the reflection constant is an exact half, since `L − T = d + n − d² − 2dn + n²` is even. -/
private theorem two_symmetryConstant (frame : ChildFrame) :
    2 * frame.symmetryConstant = frame.child.den + frame.child.num - frame.child.periodDenominator := by
  obtain ⟨p, hp⟩ := Int.even_mul_succ_self frame.child.num
  obtain ⟨q, hq⟩ := Int.even_mul_succ_self frame.child.den
  have hm : frame.child.den + frame.child.num - frame.child.periodDenominator =
      2 * (p - q + frame.child.den - frame.child.den * frame.child.num) := by
    unfold Fraction.periodDenominator
    linear_combination hp - hq
  have key : ∀ X : ℤ, 2 * (2 * X / 2) = 2 * X := fun X => by omega
  unfold ChildFrame.symmetryConstant
  rw [hm]
  exact key _

theorem ChildFrame.coherentConstantU_eq_zero (frame : ChildFrame) : frame.coherentConstantU = 0 := by
  have hx : frame.child.modifiedDeck.transverse + (1, -1) =
      (frame.child.num - frame.child.den + 1, frame.child.num + frame.child.den - 1) := by
    rw [frame.child_modifiedDeck_transverse]
    ext
    · simp only [Prod.fst_add]
    · simp only [Prod.snd_add]; ring
  have h4 := harmonicGrid_exact (frame.child.modifiedDeck.transverse + (1, -1))
  rw [hx] at h4
  dsimp only at h4
  have hmod : (frame.child.num - frame.child.den + 1 + (frame.child.num + frame.child.den - 1)) % 2 = 0 := by
    omega
  rw [hmod] at h4
  have hk := two_symmetryConstant frame
  have h4' : 4 * frame.coherentConstantU = 0 := by
    unfold ChildFrame.coherentConstantU
    rw [hx]
    unfold ChildFrame.tGrade
    dsimp only
    unfold Fraction.periodDenominator at hk
    linear_combination h4 + 2 * hk
  linarith

theorem ChildFrame.coherentConstantV_eq (frame : ChildFrame) :
    2 * frame.coherentConstantV = -(frame.child.den + frame.child.num + frame.child.periodDenominator) := by
  have hk := two_symmetryConstant frame
  unfold ChildFrame.coherentConstantV
  rw [frame.tGrade_centre, frame.child_modifiedDeck_transverse]
  unfold ChildFrame.tGrade Fraction.periodDenominator at hk ⊢
  dsimp only
  linear_combination hk

/-! ### Grades of the deck vectors and of the reflection -/

theorem ChildFrame.tGrade_add_pt (frame : ChildFrame) (a b : Site) :
    frame.tGrade (a + b) = frame.tGrade a + frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem ChildFrame.tGrade_kernel_zero (frame : ChildFrame) :
    frame.tGrade frame.child.modifiedDeck.kernel = 0 := by
  rw [frame.child_modifiedDeck_kernel]
  unfold ChildFrame.tGrade
  dsimp only
  ring

theorem ChildFrame.tGrade_transverse_eq (frame : ChildFrame) :
    frame.tGrade frame.child.modifiedDeck.transverse = -frame.child.periodDenominator := by
  rw [frame.child_modifiedDeck_transverse]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  dsimp only
  ring

/-- The transverse grade of the child is the negative of the transverse grade of the frame. -/
theorem ChildFrame.transverseGrade_eq_neg (frame : ChildFrame) (x : Site) :
    frame.child.transverseGrade x = -frame.tGrade x := by
  unfold Fraction.transverseGrade ChildFrame.tGrade
  ring

/-- Stepping back along the kernel: `F (w − K) = F w − c_U`. -/
private theorem field_sub_kernel {fraction : Fraction} {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods fraction F cU cV) (w : Site) :
    F (w - fraction.modifiedDeck.kernel) = F w - cU := by
  have h := hper.1 (w - fraction.modifiedDeck.kernel)
  rw [sub_add_cancel] at h
  linarith

/-- Stepping back along the transverse vector: `F (w − V) = F w + g(w − V) − c_V`. -/
private theorem field_sub_transverse {fraction : Fraction} {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods fraction F cU cV) (w : Site) :
    F (w - fraction.modifiedDeck.transverse) =
      F w + fraction.transverseGrade (w - fraction.modifiedDeck.transverse) - cV := by
  have h := hper.2 (w - fraction.modifiedDeck.transverse)
  rw [sub_add_cancel] at h
  linarith

/-- Two fields with the same generator constants that agree on `E` agree everywhere. -/
private theorem eq_of_closedPolygon_periods (frame : ChildFrame) {P Q : Field} {cU cV : ℤ}
    (hP : HasGeneratorPeriods frame.child P cU cV) (hQ : HasGeneratorPeriods frame.child Q cU cV)
    (hagree : ∀ y ∈ frame.closedPolygon, P y = Q y) : P = Q := by
  have hint : frame.child.Interior := frame.valid.current_interior .even
  funext z
  obtain ⟨y, hy, i, j, hz⟩ := frame.closedPolygon_covers z
  have hPl := generator_period_formula hint.inUnitInterval hP y i j
  have hQl := generator_period_formula hint.inUnitInterval hQ y i j
  have hyPQ : (P y : ℝ) = (Q y : ℝ) := by rw [hagree y hy]
  have hreal : (P (y + frame.child.modifiedDeck.combine i j) : ℝ) =
      (Q (y + frame.child.modifiedDeck.combine i j) : ℝ) := by
    linear_combination hPl - hQl + hyPQ
  rw [hz]
  exact_mod_cast hreal

/-- The sewn standard has the central reflection on the whole plane. -/
theorem ChildFrame.reflection_of_heightInputs (frame : ChildFrame) {M : Site → ℤ} (h : frame.HeightInputs M)
    {F : Field} (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F frame.coherentConstantU frame.coherentConstantV) :
    ∀ z, F (frame.centre - z) = F z - frame.tGrade z + frame.symmetryConstant := by
  rw [frame.coherentConstantU_eq_zero] at hper
  obtain ⟨G, hG⟩ : ∃ G : Field, ∀ z, G z =
      F (frame.centre - z) + frame.tGrade z - frame.symmetryConstant := ⟨_, fun z => rfl⟩
  have hGper : HasGeneratorPeriods frame.child G 0 frame.coherentConstantV := by
    refine ⟨fun site => ?_, fun site => ?_⟩
    · rw [hG, hG, show frame.centre - (site + frame.child.modifiedDeck.kernel) =
        (frame.centre - site) - frame.child.modifiedDeck.kernel by abel,
        field_sub_kernel hper, frame.tGrade_add_pt, frame.tGrade_kernel_zero]
      ring
    · rw [hG, hG, show frame.centre - (site + frame.child.modifiedDeck.transverse) =
        (frame.centre - site) - frame.child.modifiedDeck.transverse by abel,
        field_sub_transverse hper, frame.tGrade_add_pt, frame.tGrade_transverse_eq]
      simp only [frame.transverseGrade_eq_neg, frame.tGrade_sub, frame.tGrade_centre, frame.tGrade_transverse_eq]
      have h2 := frame.coherentConstantV_eq
      linear_combination (-1 : ℤ) * h2
  have hGF : ∀ y ∈ frame.closedPolygon, F y = G y := by
    intro y hy
    rw [hG]
    have h1 := hagree (frame.centre - y) (frame.centre_sub_mem hy)
    have h2 := h.reflection y hy
    have h3 := hagree y hy
    linarith
  have hFG : F = G := eq_of_closedPolygon_periods frame hper hGper hGF
  intro z
  have hz := congrFun hFG z
  rw [hG] at hz
  linarith

end FLatticePaper.Induction
