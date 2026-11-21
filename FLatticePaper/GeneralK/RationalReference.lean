import FLatticePaper.GeneralK.PeriodicEnvelope
import FLatticePaper.Construction.PeriodExtension
import Mathlib.Data.Rat.Floor

namespace FLatticePaper.GeneralK

open Farey Construction

/-- The physical rational quadratic before the floor is taken. -/
def ratQuadratic (a b c : ℚ) (site : Site) : ℚ :=
  (a * (site.1 : ℚ) ^ 2 + 2 * b * (site.1 : ℚ) * (site.2 : ℚ) + c * (site.2 : ℚ) ^ 2) / 2

def rationalFloorReference (a b c tiltX tiltY : ℚ) : Field := fun site =>
  ⌊ratQuadratic a b c site + (tiltX * (site.1 : ℚ) + tiltY * (site.2 : ℚ))⌋

/-- The integer action of a rational physical Hessian on a displacement. -/
def HasIntegerAction (a b c : ℚ) (step : Site) : Prop :=
  ∃ slopeX slopeY : ℤ, a * (step.1 : ℚ) + b * (step.2 : ℚ) = slopeX ∧
    b * (step.1 : ℚ) + c * (step.2 : ℚ) = slopeY

/-- The floor reference has genuine integer affine increments on every
element of the prescribed deck. Full rank is used to choose the rational
tilt which cancels the quadratic increment on each basis vector. -/
theorem exists_rationalFloorReference {a b c : ℚ} (deck : PeriodDeck) (hdet : deck.det ≠ 0)
    (hkernel : HasIntegerAction a b c deck.kernel) (htransverse : HasIntegerAction a b c deck.transverse) :
    ∃ tiltX tiltY : ℚ, ∀ step ∈ deck.span, ∃ slopeX slopeY constant : ℤ, ∀ site,
      rationalFloorReference a b c tiltX tiltY (site + step) =
        rationalFloorReference a b c tiltX tiltY site + slopeX * site.1 + slopeY * site.2 + constant := by
  let u := deck.kernel
  let v := deck.transverse
  let q := ratQuadratic a b c
  obtain ⟨ax, ay, hax, hay⟩ := hkernel
  obtain ⟨bx, by', hbx, hby⟩ := htransverse
  have hdet' : (deck.det : ℚ) ≠ 0 := by exact_mod_cast hdet
  let tiltX := (-(q u) * (v.2 : ℚ) + q v * (u.2 : ℚ)) / (deck.det : ℚ)
  let tiltY := (-(q v) * (u.1 : ℚ) + q u * (v.1 : ℚ)) / (deck.det : ℚ)
  have hu : tiltX * (u.1 : ℚ) + tiltY * (u.2 : ℚ) = -q u := by
    dsimp only [tiltX, tiltY]
    field_simp
    simp only [PeriodDeck.det, Int.cast_sub, Int.cast_mul, u, v]
    ring
  have hv : tiltX * (v.1 : ℚ) + tiltY * (v.2 : ℚ) = -q v := by
    dsimp only [tiltX, tiltY]
    field_simp
    simp only [PeriodDeck.det, Int.cast_sub, Int.cast_mul, u, v]
    ring
  let selfU := ax * u.1 + ay * u.2
  let selfV := bx * v.1 + by' * v.2
  let cross := ax * v.1 + ay * v.2
  have huu : (selfU : ℚ) = 2 * q u := by
    simp only [selfU, q, ratQuadratic, Int.cast_add, Int.cast_mul, u]
    linear_combination -(u.1 : ℚ) * hax - (u.2 : ℚ) * hay
  have hvv : (selfV : ℚ) = 2 * q v := by
    simp only [selfV, q, ratQuadratic, Int.cast_add, Int.cast_mul, v]
    linear_combination -(v.1 : ℚ) * hbx - (v.2 : ℚ) * hby
  have huv : (cross : ℚ) = a * (u.1 : ℚ) * (v.1 : ℚ) +
      b * ((u.1 : ℚ) * (v.2 : ℚ) + (u.2 : ℚ) * (v.1 : ℚ)) + c * (u.2 : ℚ) * (v.2 : ℚ) := by
    simp only [cross, Int.cast_add, Int.cast_mul]
    linear_combination -(v.1 : ℚ) * hax - (v.2 : ℚ) * hay
  refine ⟨tiltX, tiltY, ?_⟩
  rintro step ⟨i, j, rfl⟩
  let step := deck.combine i j
  let slopeX := i * ax + j * bx
  let slopeY := i * ay + j * by'
  let constant := chooseTwo i * selfU + i * j * cross + chooseTwo j * selfV
  have hstepX : a * (step.1 : ℚ) + b * (step.2 : ℚ) = (slopeX : ℚ) := by
    simp only [step, PeriodDeck.combine, slopeX, Int.cast_add, Int.cast_mul]
    linear_combination (i : ℚ) * hax + (j : ℚ) * hbx
  have hstepY : b * (step.1 : ℚ) + c * (step.2 : ℚ) = (slopeY : ℚ) := by
    simp only [step, PeriodDeck.combine, slopeY, Int.cast_add, Int.cast_mul]
    linear_combination (i : ℚ) * hay + (j : ℚ) * hby
  have hconstant : q step + (tiltX * (step.1 : ℚ) + tiltY * (step.2 : ℚ)) = (constant : ℚ) := by
    have hi : 2 * (chooseTwo i : ℚ) = (i : ℚ) * ((i : ℚ) - 1) := by exact_mod_cast two_mul_chooseTwo i
    have hj : 2 * (chooseTwo j : ℚ) = (j : ℚ) * ((j : ℚ) - 1) := by exact_mod_cast two_mul_chooseTwo j
    have htilt : tiltX * (step.1 : ℚ) + tiltY * (step.2 : ℚ) = -(i : ℚ) * q u - (j : ℚ) * q v := by
      simp only [step, PeriodDeck.combine, Int.cast_add, Int.cast_mul, u, v] at hu hv ⊢
      linear_combination (i : ℚ) * hu + (j : ℚ) * hv
    have hquad : q step = (i : ℚ) ^ 2 * q u + (i : ℚ) * (j : ℚ) * (cross : ℚ) + (j : ℚ) ^ 2 * q v := by
      rw [huv]
      simp only [q, ratQuadratic, step, PeriodDeck.combine, Int.cast_add, Int.cast_mul, u, v]
      ring
    rw [hquad, htilt]
    simp only [constant, Int.cast_add, Int.cast_mul, huu, hvv]
    linear_combination -(q u) * hi - (q v) * hj
  refine ⟨slopeX, slopeY, constant, fun site => ?_⟩
  have hpoly : q (site + step) + (tiltX * ((site + step).1 : ℚ) + tiltY * ((site + step).2 : ℚ)) =
      (q site + (tiltX * (site.1 : ℚ) + tiltY * (site.2 : ℚ))) +
        ((slopeX * site.1 + slopeY * site.2 + constant : ℤ) : ℚ) := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_mul, q, ratQuadratic] at hconstant ⊢
    linear_combination hconstant + (site.1 : ℚ) * hstepX + (site.2 : ℚ) * hstepY
  change ⌊q (site + step) + (tiltX * ((site + step).1 : ℚ) + tiltY * ((site + step).2 : ℚ))⌋ = _
  rw [hpoly, Int.floor_add_intCast]
  simp only [rationalFloorReference, q, ← add_assoc]

/-- The two physical labels for every admitted rational matrix and every
specified deck of phase-preserving integer-action shifts. At this stage the
envelope has a real deck slope. -/
theorem exists_periodicEnvelope_of_mem_growthSet {k : ℤ} (hk : 2 ≤ k) {a b c : ℚ}
    (hm : symmetricMatrix (a : ℝ) (b : ℝ) (c : ℝ) ∈ growthSet k)
    (deck : PeriodDeck) (hdet : deck.det ≠ 0) (hphase : ∀ step ∈ deck.span, Retained k step)
    (hkernel : HasIntegerAction a b c deck.kernel) (htransverse : HasIntegerAction a b c deck.transverse) :
    ∃ (baseX baseY : ℚ) (tiltX tiltY : ℝ) (envelope : Site → ℝ),
      (∀ step ∈ deck.span, ∀ site,
        envelope (site + step) = envelope site + (tiltX * (step.1 : ℝ) + tiltY * (step.2 : ℝ))) ∧
      (∀ offset : ℝ, Superharmonic k (fun site => rationalFloorReference a b c baseX baseY site + ⌊envelope site + offset⌋)) ∧
      ∀ site, ⌈envelope (incomingNeg k site) - envelope site⌉ + ⌈envelope (incomingPos k site) - envelope site⌉ ≤
        -laplacian k (rationalFloorReference a b c baseX baseY) site := by
  obtain ⟨height, slopeX, slopeY, lower, hsuper, hlo⟩ := exists_affine_lower_bound_of_mem_growthSet hk hm
  obtain ⟨baseX, baseY, hperiod⟩ := exists_rationalFloorReference deck hdet hkernel htransverse
  let reference := rationalFloorReference a b c baseX baseY
  have hlow (site : Site) : (reference site : ℝ) +
      ((slopeX - (baseX : ℝ)) * (site.1 : ℝ) + (slopeY - (baseY : ℝ)) * (site.2 : ℝ)) + lower ≤ height site := by
    have hf : (reference site : ℝ) ≤ ((ratQuadratic a b c site + (baseX * (site.1 : ℚ) + baseY * (site.2 : ℚ)) : ℚ) : ℝ) := by
      exact_mod_cast (Int.floor_le (ratQuadratic a b c site + (baseX * (site.1 : ℚ) + baseY * (site.2 : ℚ))))
    obtain ⟨x, y⟩ := site
    have hh := hlo (x, y)
    simp only [matrixQuadratic_symmetricMatrix] at hh
    simp only [ratQuadratic, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] at hf
    linarith only [hf, hh]
  obtain ⟨envelope, hdrift, hrounded⟩ := exists_roundedEnvelope hphase hperiod hsuper
    (slopeX - (baseX : ℝ)) (slopeY - (baseY : ℝ)) lower hlow
  exact ⟨baseX, baseY, _, _, envelope, hdrift, hrounded, ceilEnvelope_input_sum_le hrounded⟩

/-- Each integer ceiling label descends to the physical period quotient. -/
theorem ceilEnvelope_input_periodic {k : ℤ} {step : Site} (hstep : Retained k step)
    {envelope : Site → ℝ} {drift : ℝ} (hperiod : ∀ site, envelope (site + step) = envelope site + drift)
    (site : Site) :
    ⌈envelope (incomingNeg k (site + step)) - envelope (site + step)⌉ =
      ⌈envelope (incomingNeg k site) - envelope site⌉ ∧
    ⌈envelope (incomingPos k (site + step)) - envelope (site + step)⌉ =
      ⌈envelope (incomingPos k site) - envelope site⌉ := by
  have hneg : incomingNeg k (site + step) = incomingNeg k site + step := by
    simp only [incomingNeg, retained_add_iff hstep]
    split <;> (apply Prod.ext <;> (simp; all_goals omega))
  have hpos : incomingPos k (site + step) = incomingPos k site + step := by
    simp only [incomingPos, retained_add_iff hstep]
    split <;> (apply Prod.ext <;> (simp; all_goals omega))
  rw [hneg, hpos, hperiod, hperiod, hperiod]
  simp

end FLatticePaper.GeneralK
