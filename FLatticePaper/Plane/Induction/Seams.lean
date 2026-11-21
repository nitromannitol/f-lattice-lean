import FLatticePaper.Construction.PeriodExtension
import FLatticePaper.Plane.PeriodCocycle
import FLatticePaper.Plane.AlternateSlip
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Sheets

namespace FLatticePaper.Induction
open Farey Construction

private theorem seams_combine_eq_zsmul (deck : PeriodDeck) (i j : ℤ) :
    deck.combine i j = i • deck.kernel + j • deck.transverse := by
  ext <;> simp [PeriodDeck.combine, zsmul_eq_mul]

/-- The Laplacian of a field with generator identities is invariant under the deck. The two generators
are handled by the identities themselves: the kernel leaves the transverse grade of both incoming sites
unchanged, and the transverse vector shifts both by a grade that cancels in the sum. No interval
hypothesis is needed, since every deck vector has even coordinate sum. -/
theorem laplacian_add_combine {fraction : Fraction} {F : Field} {cU cV : ℤ}
    (h : HasGeneratorPeriods fraction F cU cV) (z : Site) (i j : ℤ) :
    laplacian F (z + fraction.modifiedDeck.combine i j) = laplacian F z := by
  have hKspan : fraction.modifiedDeck.kernel ∈ fraction.modifiedDeck.span :=
    ⟨1, 0, by simp [PeriodDeck.combine]⟩
  have hVspan : fraction.modifiedDeck.transverse ∈ fraction.modifiedDeck.span :=
    ⟨0, 1, by simp [PeriodDeck.combine]⟩
  have hKeven : EvenSite fraction.modifiedDeck.kernel :=
    ((fraction.mem_modifiedDeck_iff _).mp hKspan).2
  have hVeven : EvenSite fraction.modifiedDeck.transverse :=
    ((fraction.mem_modifiedDeck_iff _).mp hVspan).2
  have hK : Function.Periodic (laplacian F) fraction.modifiedDeck.kernel := by
    intro x
    unfold laplacian
    rw [incomingNeg_add_of_even x _ hKeven, incomingPos_add_of_even x _ hKeven]
    simp only [h.1]
    ring
  have hgrade : ∀ x : Site, fraction.transverseGrade (incomingNeg x) + fraction.transverseGrade (incomingPos x) =
      2 * fraction.transverseGrade x := by
    intro x
    by_cases he : EvenSite x <;>
      simp only [incomingNeg, incomingPos, he, if_true, if_false, Fraction.transverseGrade] <;> ring
  have hV : Function.Periodic (laplacian F) fraction.modifiedDeck.transverse := by
    intro x
    unfold laplacian
    rw [incomingNeg_add_of_even x _ hVeven, incomingPos_add_of_even x _ hVeven]
    simp only [h.2]
    linarith [hgrade x]
  have hcomb : Function.Periodic (laplacian F) (fraction.modifiedDeck.combine i j) := by
    rw [seams_combine_eq_zsmul]
    exact (hK.zsmul i).add_period (hV.zsmul j)
  exact hcomb z

/-- A property of the Laplacian values that holds on `E` holds everywhere. -/
theorem ChildFrame.laplacian_forall_of_closedPolygon (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (P : ℤ → Prop)
    (hE : ∀ z ∈ frame.closedPolygon, P (laplacian F z)) : ∀ z, P (laplacian F z) := by
  intro z
  obtain ⟨y, hy, i, j, hz⟩ := frame.closedPolygon_covers z
  rw [hz, laplacian_add_combine h y i j]
  exact hE y hy

/-- The value of a periodized field at an input outside `E`, through its translate in `E`. -/
theorem ChildFrame.input_value (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) {z u : Site} (hz : z ∈ frame.closedPolygon)
    (hu : Edge u z) :
    ∃ i j : ℤ, (i = -1 ∨ i = 0 ∨ i = 1) ∧ (j = -1 ∨ j = 0 ∨ j = 1) ∧
      u + frame.child.modifiedDeck.combine i j ∈ frame.closedPolygon ∧
      F u = F (u + frame.child.modifiedDeck.combine i j) - periodIncrement frame.child cU cV u i j := by
  obtain ⟨i, j, hi, hj, hmem⟩ := frame.input_mem_translate hz hu
  refine ⟨i, j, hi, hj, hmem, ?_⟩
  have hint : frame.child.Interior := frame.valid.current_interior .even
  have hlaw := generator_period_formula hint.inUnitInterval h u i j
  have hctR : (2 : ℝ) * (chooseTwo j : ℝ) = (j : ℝ) * ((j : ℝ) - 1) := by
    exact_mod_cast two_mul_chooseTwo j
  have hT : (frame.child.periodDenominator : ℝ) * (2 * (chooseTwo j : ℝ)) =
      (frame.child.periodDenominator : ℝ) * ((j : ℝ) * ((j : ℝ) - 1)) := by
    rw [hctR]
  have hreal : (F (u + frame.child.modifiedDeck.combine i j) : ℝ) =
      (F u : ℝ) + (periodIncrement frame.child cU cV u i j : ℝ) := by
    unfold periodIncrement
    push_cast
    linear_combination hlaw + (1 / 2 : ℝ) * hT
  have hint' : F (u + frame.child.modifiedDeck.combine i j) =
      F u + periodIncrement frame.child cU cV u i j := by
    exact_mod_cast hreal
  linarith

end FLatticePaper.Induction
