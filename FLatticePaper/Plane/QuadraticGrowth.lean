import FLatticePaper.Plane.PeriodCocycle

namespace FLatticePaper

open Farey

noncomputable def squaredSize (site : Site) : ℝ := (site.1 : ℝ) ^ 2 + (site.2 : ℝ) ^ 2

/-- Literal uniform form of the little-oh quadratic error at spatial infinity. -/
def HasQuadraticGrowth (field : Field) (matrix : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ radius : ℝ, 0 < radius ∧
    ∀ site : Site, radius ^ 2 ≤ squaredSize site →
      |(field site : ℝ) - matrixQuadratic matrix site| ≤ ε * squaredSize site

private theorem abs_le_size_div (coord other radius : ℝ) (hpos : 0 < radius)
    (hlarge : radius ^ 2 ≤ coord ^ 2 + other ^ 2) :
    |coord| ≤ (coord ^ 2 + other ^ 2) / radius := by
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hlarge, sq_nonneg (|coord| - radius), sq_abs coord, sq_nonneg other]

theorem quadraticGrowth_of_bounded_linear_error {field : Field}
    {matrix : Matrix (Fin 2) (Fin 2) ℝ} (linearX linearY bound : ℝ) (hbound : 0 ≤ bound)
    (herror : ∀ site : Site,
      |(field site : ℝ) - matrixQuadratic matrix site -
        (linearX * (site.1 : ℝ) + linearY * (site.2 : ℝ))| ≤ bound) :
    HasQuadraticGrowth field matrix := by
  intro ε hε
  let mass := bound + |linearX| + |linearY|
  have hmass : 0 ≤ mass := by dsimp [mass]; positivity
  let radius := 1 + mass / ε
  have hradOne : 1 ≤ radius := by dsimp [radius]; linarith [div_nonneg hmass hε.le]
  have hrad : 0 < radius := by linarith
  refine ⟨radius, hrad, fun site hsize => ?_⟩
  have hradSq : radius ≤ radius ^ 2 := by
    nlinarith only [mul_nonneg hrad.le (sub_nonneg.mpr hradOne)]
  have hscale : 1 ≤ squaredSize site / radius := by
    apply (le_div_iff₀ hrad).mpr
    rw [one_mul]
    exact hradSq.trans hsize
  have hcoeff : mass / radius ≤ ε := by
    apply (div_le_iff₀ hrad).mpr
    have hmul : ε * radius = ε + mass := by
      dsimp [radius]
      field_simp
    linarith
  have hx : |(site.1 : ℝ)| ≤ squaredSize site / radius :=
    abs_le_size_div _ _ _ hrad hsize
  have hy : |(site.2 : ℝ)| ≤ squaredSize site / radius := by
    simpa only [squaredSize, add_comm] using
      abs_le_size_div (site.2 : ℝ) (site.1 : ℝ) radius hrad (by simpa only [squaredSize, add_comm] using hsize)
  let tilt := linearX * (site.1 : ℝ) + linearY * (site.2 : ℝ)
  let value := (field site : ℝ) - matrixQuadratic matrix site
  calc
    |value| = |value - tilt + tilt| := congrArg abs (sub_add_cancel value tilt).symm
    _ ≤ |value - tilt| + |tilt| := abs_add_le ..
    _ ≤ bound + (|linearX| * |(site.1 : ℝ)| + |linearY| * |(site.2 : ℝ)|) := by
      apply add_le_add (herror site)
      simpa only [tilt, abs_mul] using abs_add_le (linearX * (site.1 : ℝ)) (linearY * (site.2 : ℝ))
    _ ≤ bound * (squaredSize site / radius) +
        (|linearX| * (squaredSize site / radius) + |linearY| * (squaredSize site / radius)) := by
      exact add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hbound)
        (add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) (mul_le_mul_of_nonneg_left hy (abs_nonneg _)))
    _ = (mass / radius) * squaredSize site := by dsimp [mass]; ring
    _ ≤ ε * squaredSize site := mul_le_mul_of_nonneg_right hcoeff (by unfold squaredSize; positivity)

theorem bounded_periodRemainder {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ site : Site, |periodRemainder fraction field constantU constantV site| ≤ bound := by
  let remainder := periodRemainder fraction field constantU constantV
  let deck := fraction.modifiedDeck
  have hpos : 0 < deck.det := Fraction.det_modifiedDeck_pos hinterval
  obtain ⟨origin, horigin, _⟩ := deck.exists_square_representative hpos 0
  obtain ⟨maxSite, _, hmax⟩ :=
    deck.residueSquare.exists_max_image (fun site => |remainder site|) ⟨origin, horigin⟩
  refine ⟨|remainder maxSite|, abs_nonneg _, fun site => ?_⟩
  obtain ⟨point, hpoint, hclass⟩ := deck.exists_square_representative hpos site
  have hspan := (deck.classCode_eq_iff (ne_of_gt hpos) site point).mp hclass
  have hper : remainder (point + (site - point)) = remainder point :=
    periodRemainder_periodic hinterval hperiod hspan point
  rw [add_comm point (site - point), sub_add_cancel] at hper
  change |remainder site| ≤ |remainder maxSite|
  rw [hper]
  exact hmax point hpoint

private theorem periodicTilt_linear (fraction : Fraction) (constantU constantV : ℤ) (site : Site) :
    periodicTilt fraction constantU constantV site =
      periodicTilt fraction constantU constantV (1, 0) * (site.1 : ℝ) +
      periodicTilt fraction constantU constantV (0, 1) * (site.2 : ℝ) := by
  simp [periodicTilt, PeriodDeck.kernelNumerator, PeriodDeck.transverseNumerator]
  ring

theorem generator_periods_growth {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods fraction field constantU constantV) :
    HasQuadraticGrowth field fraction.matrix := by
  obtain ⟨bound, hbound, hrem⟩ := bounded_periodRemainder hinterval hperiod
  apply quadraticGrowth_of_bounded_linear_error
    (periodicTilt fraction constantU constantV (1, 0))
    (periodicTilt fraction constantU constantV (0, 1)) bound hbound
  intro site
  rw [← periodicTilt_linear]
  exact hrem site

end FLatticePaper
