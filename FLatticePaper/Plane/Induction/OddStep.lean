import FLatticePaper.Plane.Induction.ChildFrame
import FLatticePaper.Plane.RecurrenceRotation
import FLatticePaper.Plane.QuadraticGrowth
import FLatticePaper.Farey.RotationLattice
import FLatticePaper.MainTheorems
import FLatticePaper.Plane.OdometerTheorem

namespace FLatticePaper.Induction
open Farey

/-- The harmonic quarter-turn `x ↦ F(Zx) + h0(x)`. -/
def quarterTurnField (F : Field) : Field :=
  fun x => F (QuarterTurn.counterclockwise.mapSite (0, -1) x) + harmonicGrid x

/-- The quarter-turn offset map `Z(x, y) = (−y, x − 1)`. -/
theorem quarterTurn_site (x : Site) :
    QuarterTurn.counterclockwise.mapSite (0, -1) x = (-x.2, x.1 - 1) := by
  simp [QuarterTurn.mapSite, QuarterTurn.turn, sub_eq_add_neg]

/-- The parity of `x + y` as a real number in `{0, 1}`. -/
def parityReal (x : Site) : ℝ := (((x.1 + x.2) % 2 : ℤ) : ℝ)

theorem parityReal_bounds (x : Site) : 0 ≤ parityReal x ∧ parityReal x ≤ 1 := by
  unfold parityReal
  have h0 : 0 ≤ (x.1 + x.2) % 2 := Int.emod_nonneg _ (by norm_num)
  have h1 : (x.1 + x.2) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  constructor
  · exact_mod_cast h0
  · have : (x.1 + x.2) % 2 ≤ 1 := by omega
    exact_mod_cast this

/-- The real form of `h0`: `4 h0(x) = x₁² + 2x₁x₂ − x₂² − 2x₂ − par(x₁+x₂)`. -/
theorem harmonicGrid_real (x : Site) :
    (harmonicGrid x : ℝ) =
      ((x.1 : ℝ) ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - parityReal x) / 4 := by
  have h := harmonicGrid_exact x
  have h' : (4 : ℝ) * (harmonicGrid x : ℝ) =
      (x.1 : ℝ) ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - parityReal x := by
    unfold parityReal
    exact_mod_cast h
  linarith

/-- The denominator of the period matrix as a real number. -/
theorem periodDenominator_real (f : Fraction) :
    (f.periodDenominator : ℝ) = (f.den : ℝ) ^ 2 + 2 * f.den * f.num - (f.num : ℝ) ^ 2 := by
  unfold Fraction.periodDenominator
  push_cast
  ring

/-- The rotated fraction of an odd fraction has numerator `d − n` and denominator `d + n`. -/
theorem rotate_num_den_of_odd {f : Fraction} (hodd : f.Odd) :
    f.rotate.num = f.den - f.num ∧ f.rotate.den = f.den + f.num := by
  rw [Fraction.rotate_of_odd hodd]
  exact ⟨rfl, rfl⟩

/-- The period denominator of the rotated odd fraction is twice that of the fraction. -/
theorem rotate_periodDenominator_real {f : Fraction} (hodd : f.Odd) :
    (f.rotate.periodDenominator : ℝ) = 2 * (f.periodDenominator : ℝ) := by
  obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
  rw [periodDenominator_real, periodDenominator_real, h1, h2]
  push_cast
  ring

/-- The matrix identity `M(f) = Rᵀ M(Rf) R + H`, written as a dot-product identity. -/
theorem dot_rotate_identity {f : Fraction} (hodd : f.Odd) (hT : (f.periodDenominator : ℝ) ≠ 0)
    (x v : Site) :
    dotProduct (siteVector x) (f.matrix.mulVec (siteVector v)) =
      dotProduct (siteVector (mulI x)) (f.rotate.matrix.mulVec (siteVector (mulI v))) +
        dotProduct (siteVector x)
          ((!![1 / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec (siteVector v)) := by
  obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
  simp only [Fraction.matrix]
  rw [h1, h2]
  have hT2 : ((f.rotate.periodDenominator : ℤ) : ℝ) = 2 * ((f.periodDenominator : ℤ) : ℝ) :=
    rotate_periodDenominator_real hodd
  rw [hT2]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, siteVector, mulI]
  field_simp
  rw [periodDenominator_real f]
  ring

/-- The quadratic part of the quarter-turned growth: `Q_{Rf}(Zx) + h0(x) − Q_f(x)` is affine in `x`
up to the parity term of `h0`. -/
theorem growth_identity {f : Fraction} (hodd : f.Odd) (hT : (f.periodDenominator : ℝ) ≠ 0) (x : Site) :
    matrixQuadratic f.rotate.matrix (-x.2, x.1 - 1) + (harmonicGrid x : ℝ) -
        matrixQuadratic f.matrix x =
      ((f.den : ℝ) + f.num) ^ 2 / (2 * (f.periodDenominator : ℝ)) * x.1 -
        ((f.den : ℝ) * f.num) / (f.periodDenominator : ℝ) * x.2 -
        ((f.den : ℝ) + f.num) ^ 2 / (4 * (f.periodDenominator : ℝ)) - parityReal x / 4 := by
  obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
  rw [harmonicGrid_real]
  unfold matrixQuadratic
  simp only [Fraction.matrix]
  rw [h1, h2, rotate_periodDenominator_real hodd]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, siteVector]
  field_simp
  rw [periodDenominator_real f]
  ring

/-- A coordinate of a site is bounded by `s / R` once `s` is at least `R²`. -/
theorem coord_le_size_div (y s R : ℝ) (hR : 0 < R) (hs : R ^ 2 ≤ s) (hy : y ^ 2 ≤ s) :
    |y| ≤ s / R := by
  rw [le_div_iff₀ hR]
  nlinarith [sq_abs y, sq_nonneg (|y| - R)]

theorem squaredSize_quarterTurn (x : Site) :
    squaredSize (-x.2, x.1 - 1) = squaredSize x - 2 * (x.1 : ℝ) + 1 := by
  unfold squaredSize
  push_cast
  ring

/-- Little-oh growth transfers along the quarter-turn when the remainder is affine in the coordinates:
the error of the rotated field at `Zx` is controlled by its size at `Zx`, which is comparable to `|x|²`. -/
theorem growth_of_affine_remainder {G : Field} {Mrf Mf : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : HasQuadraticGrowth G Mrf) (h : Site → ℤ) (A1 A2 A0 : ℝ)
    (hid : ∀ x : Site, matrixQuadratic Mrf (-x.2, x.1 - 1) + (h x : ℝ) - matrixQuadratic Mf x =
      A1 * x.1 - A2 * x.2 - A0 - parityReal x / 4) :
    HasQuadraticGrowth (fun x => G (-x.2, x.1 - 1) + h x) Mf := by
  intro ε hε
  obtain ⟨R1, hR1, hG1⟩ := hG (ε / 4) (by positivity)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |A1| + |A2| + |A0| + 1 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  obtain ⟨R0, hR0def⟩ : ∃ R0 : ℝ, R0 = 4 + 2 * R1 + 8 * K / ε := ⟨_, rfl⟩
  have hR0 : 4 ≤ R0 := by
    have : 0 ≤ 8 * K / ε := by positivity
    rw [hR0def]; linarith
  have hR0K : 8 * K ≤ ε * R0 := by
    have h1 : ε * R0 = ε * (4 + 2 * R1) + 8 * K := by
      rw [hR0def]; field_simp
    have h2 : 0 ≤ ε * (4 + 2 * R1) := by positivity
    linarith
  have hR0R1 : 2 * R1 ≤ R0 := by
    have : 0 ≤ 8 * K / ε := by positivity
    rw [hR0def]; linarith
  refine ⟨R0, by linarith, fun x hx => ?_⟩
  -- the size of the point x and of its image `Zx`
  have hs1 : 1 ≤ squaredSize x := by
    unfold squaredSize at hx ⊢
    nlinarith [sq_nonneg (x.1 : ℝ), sq_nonneg (x.2 : ℝ)]
  have hxsq1 : (x.1 : ℝ) ^ 2 ≤ squaredSize x := by unfold squaredSize; nlinarith [sq_nonneg (x.2 : ℝ)]
  have hxsq2 : (x.2 : ℝ) ^ 2 ≤ squaredSize x := by unfold squaredSize; nlinarith [sq_nonneg (x.1 : ℝ)]
  have hx1 : |(x.1 : ℝ)| ≤ squaredSize x / R0 := coord_le_size_div _ _ _ (by linarith) hx hxsq1
  have hx2 : |(x.2 : ℝ)| ≤ squaredSize x / R0 := coord_le_size_div _ _ _ (by linarith) hx hxsq2
  have hs4 : squaredSize x / R0 ≤ squaredSize x / 4 := div_le_div_of_nonneg_left
    (by unfold squaredSize; positivity) (by norm_num) hR0
  have hx1' : |(x.1 : ℝ)| ≤ squaredSize x / 4 := hx1.trans hs4
  have hZlow : R1 ^ 2 ≤ squaredSize (-x.2, x.1 - 1) := by
    rw [squaredSize_quarterTurn]
    have hl : (2 : ℝ) * x.1 ≤ squaredSize x / 2 := by
      have := le_abs_self (x.1 : ℝ)
      linarith
    have hR1sq : R1 ^ 2 ≤ squaredSize x / 4 := by
      have : (2 * R1) ^ 2 ≤ R0 ^ 2 := by nlinarith [hR0R1, hR1]
      have hRx : R0 ^ 2 ≤ squaredSize x := hx
      nlinarith
    nlinarith
  have hZup : squaredSize (-x.2, x.1 - 1) ≤ 3 * squaredSize x := by
    rw [squaredSize_quarterTurn]
    have := le_abs_self (x.1 : ℝ)
    have := neg_abs_le (x.1 : ℝ)
    nlinarith [hx1']
  have herr := hG1 (-x.2, x.1 - 1) hZlow
  -- the affine remainder is bounded by `K s / R0`
  have hBound : |A1 * x.1 - A2 * x.2 - A0 - parityReal x / 4| ≤ K * (squaredSize x / R0) := by
    obtain ⟨hp0, hp1⟩ := parityReal_bounds x
    have hsR : 1 ≤ squaredSize x / R0 := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have e1 : |A1 * (x.1 : ℝ)| ≤ |A1| * (squaredSize x / R0) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
    have e2 : |A2 * (x.2 : ℝ)| ≤ |A2| * (squaredSize x / R0) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
    have e3 : |A0 + parityReal x / 4| ≤ (|A0| + 1) * (squaredSize x / R0) := by
      have h0 : |A0 + parityReal x / 4| ≤ |A0| + 1 := by
        have : |parityReal x / 4| ≤ 1 := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have := abs_add_le A0 (parityReal x / 4)
        linarith
      nlinarith [abs_nonneg A0]
    have hsplit : A1 * (x.1 : ℝ) - A2 * (x.2 : ℝ) - A0 - parityReal x / 4 =
        A1 * (x.1 : ℝ) + (-(A2 * (x.2 : ℝ))) + (-(A0 + parityReal x / 4)) := by ring
    rw [hsplit]
    have f1 := abs_add_le (A1 * (x.1 : ℝ) + (-(A2 * (x.2 : ℝ)))) (-(A0 + parityReal x / 4))
    have f2 := abs_add_le (A1 * (x.1 : ℝ)) (-(A2 * (x.2 : ℝ)))
    rw [abs_neg] at f1
    rw [abs_neg] at f2
    have hK : |A1| + |A2| + |A0| + 1 = K := hKdef.symm
    nlinarith [abs_nonneg A1, abs_nonneg A2, abs_nonneg A0, hsR, e1, e2, e3, f1, f2]
  -- the bound on the rotated error
  have hKs : K * (squaredSize x / R0) ≤ ε / 8 * squaredSize x := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [hR0K, hs1]
  -- assemble
  have hsplit : ((fun x => G (-x.2, x.1 - 1) + h x) x : ℝ) - matrixQuadratic Mf x =
      ((G (-x.2, x.1 - 1) : ℝ) - matrixQuadratic Mrf (-x.2, x.1 - 1)) +
        (matrixQuadratic Mrf (-x.2, x.1 - 1) + (h x : ℝ) - matrixQuadratic Mf x) := by
    simp only
    push_cast
    ring
  rw [hsplit, hid x]
  have hfin := abs_add_le ((G (-x.2, x.1 - 1) : ℝ) - matrixQuadratic Mrf (-x.2, x.1 - 1))
    (A1 * x.1 - A2 * x.2 - A0 - parityReal x / 4)
  nlinarith [hfin, herr, hBound, hKs, hs1]

theorem modifiedDeck_odd {f : Fraction} (hodd : f.Odd) :
    f.modifiedDeck.kernel = (2 * f.den, 2 * f.num) ∧ f.modifiedDeck.transverse = (f.num - f.den, f.num + f.den) := by
  have hmu : f.periodMultiplicity = 2 := by
    unfold Fraction.periodMultiplicity
    have hne : ¬ ((f.num + f.den) % 2 = 0) := by
      unfold Fraction.Odd at hodd
      omega
    rw [if_neg hne]
  simp [Fraction.modifiedDeck, hmu, Fraction.unmodifiedDeck]

theorem modifiedDeck_even {f : Fraction} (heven : f.Even) :
    f.modifiedDeck.kernel = (f.den, f.num) ∧ f.modifiedDeck.transverse = (f.num - f.den, f.num + f.den) := by
  have hmu : f.periodMultiplicity = 1 := by
    unfold Fraction.periodMultiplicity
    have h : (f.num + f.den) % 2 = 0 := heven
    rw [if_pos h]
  simp [Fraction.modifiedDeck, hmu, Fraction.unmodifiedDeck]

/-- The period lattice of an odd fraction consists of sites of even coordinate sum. -/
theorem evenSite_of_mem_span_odd {f : Fraction} (hodd : f.Odd) {v : Site}
    (hv : v ∈ f.modifiedDeck.span) : EvenSite v := by
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hk, ht⟩ := modifiedDeck_odd hodd
  unfold EvenSite
  simp only [PeriodDeck.combine, hk, ht]
  have h : i * (2 * f.den) + j * (f.num - f.den) + (i * (2 * f.num) + j * (f.num + f.den)) =
      2 * (i * (f.den + f.num) + j * f.num) := by ring
  rw [h]
  simp

/-- Multiplication by `I` carries the period lattice of an odd fraction into that of its rotation. -/
theorem mulI_mem_span_rotate {f : Fraction} (hodd : f.Odd) {v : Site}
    (hv : v ∈ f.modifiedDeck.span) : mulI v ∈ f.rotate.modifiedDeck.span := by
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hk, ht⟩ := modifiedDeck_odd hodd
  obtain ⟨hk', ht'⟩ := modifiedDeck_even (Fraction.rotate_even_of_odd hodd)
  obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
  refine ⟨-j, i, ?_⟩
  simp only [PeriodDeck.combine, hk, ht, hk', ht', h1, h2, mulI]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- The harmonic grid translates by an even-sum site up to the bilinear form of `(1/2, 1/2; 1/2, −1/2)`. -/
theorem harmonicGrid_translate (x v : Site) (hv : EvenSite v) :
    (harmonicGrid (x + v) : ℝ) = harmonicGrid x + harmonicGrid v +
      dotProduct (siteVector x)
        ((!![1 / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec (siteVector v)) := by
  have hv' : (v.1 + v.2) % 2 = 0 := hv
  have hpar : parityReal (x + v) = parityReal x := by
    unfold parityReal
    simp only [Prod.fst_add, Prod.snd_add]
    have h : (x.1 + v.1 + (x.2 + v.2)) % 2 = (x.1 + x.2) % 2 := by omega
    rw [h]
  have hpv : parityReal v = 0 := by
    unfold parityReal
    rw [hv']
    simp
  rw [harmonicGrid_real, harmonicGrid_real, harmonicGrid_real, hpar, hpv]
  simp [dotProduct, Fin.sum_univ_two, siteVector, Matrix.mulVec]
  ring

/-- The odd fraction's quarter-turned periods: the quarter-turn of an odd fraction's standard field
is periodic on the odd lattice with the matrix of the fraction. -/
theorem satisfiesPeriodicity_quarterTurn {f : Fraction} (hodd : f.Odd)
    (hT : (f.periodDenominator : ℝ) ≠ 0) {G : Field} (hps : SatisfiesPeriodicity f.rotate G) :
    SatisfiesPeriodicity f (quarterTurnField G) := by
  intro v hv
  obtain ⟨cu, hcu⟩ := hps (mulI v) (mulI_mem_span_rotate hodd hv)
  refine ⟨2 * cu - G ((0, 1) + mulI v) + G (0, 1) + harmonicGrid v, fun x => ?_⟩
  have hG1 := hcu (0, 1)
  have hGZ := hcu (-x.2, x.1 - 1)
  have hZ : (-(x + v).2, (x + v).1 - 1) = (-x.2, x.1 - 1) + mulI v := by
    refine Prod.ext ?_ ?_ <;> simp [mulI] <;> ring
  have hdot := dot_rotate_identity hodd hT x v
  have hh := harmonicGrid_translate x v (evenSite_of_mem_span_odd hodd hv)
  have h01 : dotProduct (siteVector (0, 1)) (f.rotate.matrix.mulVec (siteVector (mulI v))) =
      (f.rotate.matrix.mulVec (siteVector (mulI v))) 1 := by
    simp [dotProduct, Fin.sum_univ_two, siteVector]
  have hZdot : dotProduct (siteVector (-x.2, x.1 - 1)) (f.rotate.matrix.mulVec (siteVector (mulI v))) =
      dotProduct (siteVector (mulI x)) (f.rotate.matrix.mulVec (siteVector (mulI v))) -
        (f.rotate.matrix.mulVec (siteVector (mulI v))) 1 := by
    simp [dotProduct, Fin.sum_univ_two, siteVector, mulI]
    ring
  rw [h01] at hG1
  unfold quarterTurnField
  rw [quarterTurn_site (x + v), quarterTurn_site x, hZ]
  push_cast
  rw [hGZ, hh]
  linarith [hdot, hZdot, hG1]

/-- The inverse of `Z` is an integer-affine bijection, so a non-affine difference stays non-affine after `Z`. -/
theorem not_integerAffine_comp_quarterTurn {D : Field} (h : ¬ IntegerAffine D) :
    ¬ IntegerAffine (fun x => D (-x.2, x.1 - 1)) := by
  rintro ⟨g, c, hg⟩
  apply h
  refine ⟨(-g.2, g.1), g.1 + c, fun w => ?_⟩
  have hw := hg (w.2 + 1, -w.1)
  have e : (-(-w.1), (w.2 + 1) - 1) = w := Prod.ext (by simp) (by simp)
  simp only [e] at hw
  simp only
  linear_combination hw

theorem quarterTurnField_eq (G : Field) :
    quarterTurnField G = fun x => G (-x.2, x.1 - 1) + harmonicGrid x := by
  funext x
  unfold quarterTurnField
  rw [quarterTurn_site]

/-- `theorem:odometers` at an odd fraction from the theorem at its rotation. -/
theorem odometersTheoremAt_of_rotate {fraction : Fraction} (hodd : fraction.Odd)
    (hinterval : fraction.InUnitInterval) (hreduced : fraction.Reduced)
    (h : OdometersTheoremAt fraction.rotate) : OdometersTheoremAt fraction := by
  have _hreduced : fraction.Reduced := hreduced
  obtain ⟨std, alt, hs, ha, hps, hpa, -, hna⟩ := h
  have hT : (fraction.periodDenominator : ℝ) ≠ 0 := by
    have hpos := Fraction.periodDenominator_pos hinterval
    exact_mod_cast hpos.ne'
  obtain ⟨hsup, hrec, hgr⟩ := hs
  obtain ⟨hsup', hrec', hgr'⟩ := ha
  have hoff : ¬ EvenSite (0, -1) := by decide
  have hqS : Superharmonic (quarterTurnField std) ∧ Recurrent (quarterTurnField std) :=
    Recurrent.quarterTurn (correction := harmonicGrid) hrec hsup QuarterTurn.counterclockwise
      (0, -1) hoff (fun x => harmonicGrid_harmonic x)
  have hqA : Superharmonic (quarterTurnField alt) ∧ Recurrent (quarterTurnField alt) :=
    Recurrent.quarterTurn (correction := harmonicGrid) hrec' hsup' QuarterTurn.counterclockwise
      (0, -1) hoff (fun x => harmonicGrid_harmonic x)
  have hgS : HasQuadraticGrowth (quarterTurnField std) fraction.matrix := by
    rw [quarterTurnField_eq]
    exact growth_of_affine_remainder hgr harmonicGrid _ _ _ (growth_identity hodd hT)
  have hgA : HasQuadraticGrowth (quarterTurnField alt) fraction.matrix := by
    rw [quarterTurnField_eq]
    exact growth_of_affine_remainder hgr' harmonicGrid _ _ _ (growth_identity hodd hT)
  have hna' : ¬ IntegerAffine (fun x => quarterTurnField alt x - quarterTurnField std x) := by
    have e : (fun x => quarterTurnField alt x - quarterTurnField std x) =
        fun x => (fun y => alt y - std y) (-x.2, x.1 - 1) := by
      funext x
      simp only [quarterTurnField, quarterTurn_site]
      ring
    rw [e]
    exact not_integerAffine_comp_quarterTurn hna
  refine ⟨quarterTurnField std, quarterTurnField alt, ⟨hqS.1, hqS.2, hgS⟩, ⟨hqA.1, hqA.2, hgA⟩,
    satisfiesPeriodicity_quarterTurn hodd hT hps, satisfiesPeriodicity_quarterTurn hodd hT hpa,
    ?_, hna'⟩
  intro heq
  apply hna'
  refine ⟨(0, 0), 0, fun x => ?_⟩
  rw [← heq]
  simp

/-- The odometer theorem reduces to even fractions. -/
theorem odometersTheorem_of_even
    (h : ∀ fraction : Fraction, fraction.Interior → fraction.Reduced → fraction.Even →
      OdometersTheoremAt fraction) : OdometersTheorem := by
  intro fraction hint hred
  by_cases hodd : fraction.Odd
  · have hinterval : fraction.InUnitInterval := hint.inUnitInterval
    obtain ⟨hn, hnd⟩ := hint
    obtain ⟨h1, h2⟩ := rotate_num_den_of_odd hodd
    have hrot : fraction.rotate.Interior := by
      unfold Fraction.Interior
      rw [h1, h2]
      constructor <;> omega
    exact odometersTheoremAt_of_rotate hodd hinterval hred
      (h fraction.rotate hrot (Fraction.rotate_reduced hinterval hred)
        (Fraction.rotate_even_of_odd hodd))
  · have heven : fraction.Even := by
      unfold Fraction.Odd at hodd
      unfold Fraction.Even
      omega
    exact h fraction hint hred heven

end FLatticePaper.Induction
