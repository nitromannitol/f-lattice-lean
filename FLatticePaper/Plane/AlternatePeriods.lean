import FLatticePaper.Plane.AlternateSlip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FLatticePaper

theorem alternateSlip_transverse (num den parentNum parentDen : ℤ) :
    num * (alternateSlip num den parentNum parentDen).1 -
      den * (alternateSlip num den parentNum parentDen).2 =
      -2 * (parentNum * den - parentDen * num) ^ 2 := by
  dsimp only [alternateSlip]
  ring

/-- The even midpoint minus the standard has transverse-period increment
`-1`, from the standard's prescribed period jet and the unit Farey determinant. -/
theorem roundedMidpoint_sub_standard_add_transverse
    (standard : Field) (num den parentNum parentDen constant : ℤ)
    (hdet : parentNum * den - parentDen * num = -1 ∨
      parentNum * den - parentDen * num = 1)
    (hperiod : ∀ site,
      standard (site + (num - den, num + den)) =
        standard site + num * site.1 - den * site.2 + constant)
    (site : Site) :
    let alt := roundedMidpoint standard (alternateCompanion standard num den parentNum parentDen)
    let period : Site := (num - den, num + den)
    alt (site + period) - standard (site + period) = alt site - standard site - 1 := by
  dsimp only [roundedMidpoint, alternateCompanion]
  let offset := alternateSlip num den parentNum parentDen
  let period : Site := (num - den, num + den)
  have htransverse : num * offset.1 - den * offset.2 = -2 := by
    dsimp only [offset]
    rw [alternateSlip_transverse]
    rcases hdet with hdet | hdet <;> rw [hdet] <;> decide
  have hsum : standard (site + period) - standard (site + period + offset) =
      standard site - standard (site + offset) + 2 := by
    rw [add_right_comm site period offset]
    have hbase := hperiod site
    have hcopy := hperiod (site + offset)
    change standard (site + period) = standard site + num * site.1 - den * site.2 + constant at hbase
    change standard (site + offset + period) =
      standard (site + offset) + num * (site.1 + offset.1) - den * (site.2 + offset.2) + constant at hcopy
    simp only [mul_add] at hcopy
    omega
  change standard (site + period) - (standard (site + period) -
    standard (site + period + offset)) / 2 - standard (site + period) =
    standard site - (standard site - standard (site + offset)) / 2 - standard site - 1
  rw [hsum]
  omega

/-- Along the undoubled kernel period of the even child, the midpoint minus
the standard is unchanged. This only uses the constant standard increment. -/
theorem roundedMidpoint_sub_standard_add_kernel (standard : Field)
    (num den parentNum parentDen constant : ℤ)
    (hperiod : ∀ site, standard (site + (den, num)) = standard site + constant)
    (site : Site) :
    let alt := roundedMidpoint standard (alternateCompanion standard num den parentNum parentDen)
    alt (site + (den, num)) - standard (site + (den, num)) = alt site - standard site := by
  dsimp only [roundedMidpoint, alternateCompanion]
  rw [add_right_comm site (den, num), hperiod, hperiod]
  have hgap : standard site + constant -
      (standard (site + alternateSlip num den parentNum parentDen) + constant) =
      standard site - standard (site + alternateSlip num den parentNum parentDen) := by omega
  rw [hgap]
  omega

/-- An affine height with integer coefficients in the physical coordinates. -/
def IntegerAffine (field : Field) : Prop :=
  ∃ gradient : Site, ∃ constant : ℤ,
    ∀ site, field site = gradient.1 * site.1 + gradient.2 * site.2 + constant

private theorem noGradientWithIncrements (num den : ℤ) (hnum : 0 < num) (hden : num < den)
    (gradient : Site) (hkernel : den * gradient.1 + num * gradient.2 = 0)
    (htransverse : (num - den) * gradient.1 + (num + den) * gradient.2 = -1) : False := by
  let det := den ^ 2 + 2 * den * num - num ^ 2
  have hlarge : num < det := by
    dsimp only [det]
    have hpos := mul_pos (show 0 < den - num by omega) (show 0 < den + num by omega)
    have hprod := mul_pos (show 0 < den by omega) hnum
    have hle : num ≤ den * num := by
      simpa using (mul_le_mul_of_nonneg_right (show 1 ≤ den by omega) hnum.le)
    nlinarith only [hpos, hprod, hle]
  have heq : det * gradient.1 = num := by
    calc
      det * gradient.1 =
          (num + den) * (den * gradient.1 + num * gradient.2) -
            num * ((num - den) * gradient.1 + (num + den) * gradient.2) := by
        dsimp only [det]
        ring
      _ = num := by rw [hkernel, htransverse]; ring
  by_cases hgrad : gradient.1 ≤ 0
  · have hle := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ det by omega) hgrad
    omega
  · have hle := mul_le_mul_of_nonneg_left (show 1 ≤ gradient.1 by omega) (show 0 ≤ det by omega)
    rw [mul_one] at hle
    omega

/-- The even midpoint and the standard cannot differ by an integer affine
function when the standard has the manuscript's two generator increments. -/
theorem not_integerAffine_roundedMidpoint_sub_standard
    (standard : Field) (num den parentNum parentDen kernelConstant transverseConstant : ℤ)
    (hnum : 0 < num) (hden : num < den)
    (hdet : parentNum * den - parentDen * num = -1 ∨
      parentNum * den - parentDen * num = 1)
    (hkernel : ∀ site, standard (site + (den, num)) = standard site + kernelConstant)
    (hperiod : ∀ site, standard (site + (num - den, num + den)) =
      standard site + num * site.1 - den * site.2 + transverseConstant) :
    ¬ IntegerAffine (fun site =>
      roundedMidpoint standard (alternateCompanion standard num den parentNum parentDen) site -
        standard site) := by
  let difference : Field := fun site =>
    roundedMidpoint standard (alternateCompanion standard num den parentNum parentDen) site -
      standard site
  change ¬ IntegerAffine difference
  rintro ⟨gradient, constant, hAffine⟩
  have hu := roundedMidpoint_sub_standard_add_kernel standard num den parentNum parentDen
    kernelConstant hkernel 0
  have hv := roundedMidpoint_sub_standard_add_transverse standard num den parentNum parentDen
    transverseConstant hdet hperiod 0
  change difference (0 + (den, num)) = difference 0 at hu
  change difference (0 + (num - den, num + den)) = difference 0 - 1 at hv
  simp only [zero_add, hAffine] at hu hv
  apply noGradientWithIncrements num den hnum hden gradient
  · change gradient.1 * den + gradient.2 * num + constant =
      gradient.1 * 0 + gradient.2 * 0 + constant at hu
    rw [mul_comm den gradient.1, mul_comm num gradient.2]
    omega
  · change gradient.1 * (num - den) + gradient.2 * (num + den) + constant =
      gradient.1 * 0 + gradient.2 * 0 + constant - 1 at hv
    rw [mul_comm (num - den) gradient.1, mul_comm (num + den) gradient.2]
    omega

end FLatticePaper
