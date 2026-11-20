import FLattice.Auxiliary.QuadraticGap
import FLattice.Auxiliary.RankedProperGap
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The two endpoint profiles and the elementary harmonic correction

The second profile is written as a product of integer quotients. This
equals the floor-of-square formula in the manuscript and makes signed
integer arithmetic explicit. Every identity holds on the whole plane.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.ElementaryProfiles

/-- Coordinate-sum parity, with values zero and one. -/
def parity (x y : ℤ) : ℤ := (x + y) % 2

/-- The endpoint with matrix diag(0,-1). -/
def zeroProfile (z : ℤ × ℤ) : ℤ := -(z.2 * (z.2 + 1) / 2)

/-- The endpoint at the other end of the rational parameter interval. -/
def oneProfile (z : ℤ × ℤ) : ℤ :=
  -((z.1 - z.2) / 2) * ((z.1 - z.2 - 1) / 2)

/-- The integer harmonic correction used by the affine quarter turn. -/
def harmonic (z : ℤ × ℤ) : ℤ := oneProfile z - zeroProfile (0, z.1 - 1)

/-- The native parity is always zero or one, also at negative coordinates. -/
theorem parity_cases (x y : ℤ) : parity x y = 0 ∨ parity x y = 1 := by
  unfold parity
  omega

/-- Exact doubled endpoint identity, with no truncation remainder. -/
theorem zeroProfile_twice (x y : ℤ) :
    2 * zeroProfile (x, y) = -y * (y + 1) := by
  have h := Int.mul_ediv_cancel' (Int.two_dvd_mul_add_one y)
  dsimp [zeroProfile]
  nlinarith only [h]

private theorem quotient_product_four (s : ℤ) :
    4 * (-(s / 2) * ((s - 1) / 2)) = -s ^ 2 + 2 * s - s % 2 := by
  have hq : 2 * (s / 2) + s % 2 = s := by omega
  have he : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases he with he | he
  · have hp : (s - 1) / 2 = s / 2 - 1 := by omega
    have hs : s = 2 * (s / 2) := by omega
    rw [hp, he]
    conv_rhs => rw [hs]
    ring
  · have hp : (s - 1) / 2 = s / 2 := by omega
    have hs : s = 2 * (s / 2) + 1 := by omega
    rw [hp, he]
    conv_rhs => rw [hs]
    ring

/-- Exact fourfold endpoint identity, including the parity correction. -/
theorem oneProfile_four (x y : ℤ) :
    4 * oneProfile (x, y) = -(x - y) ^ 2 + 2 * (x - y) - parity x y := by
  have h := quotient_product_four (x - y)
  have hParity : (x - y) % 2 = parity x y := by unfold parity; omega
  simpa only [oneProfile, hParity] using h

/-- The quotient-product profile is exactly the manuscript's integer
floor of the squared difference, including negative arguments. -/
theorem oneProfile_eq_square_quotient (x y : ℤ) :
    oneProfile (x, y) = -((x - y - 1) ^ 2 / 4) := by
  have h := oneProfile_four x y
  have he := parity_cases x y
  have hLo : 4 * (-oneProfile (x, y)) ≤ (x - y - 1) ^ 2 := by
    rcases he with he | he <;> nlinarith only [h, he]
  have hHi : (x - y - 1) ^ 2 < 4 * (-oneProfile (x, y) + 1) := by
    rcases he with he | he <;> nlinarith only [h, he]
  omega

/-- The harmonic correction has an exact quadratic-affine-parity formula. -/
theorem harmonic_four (x y : ℤ) :
    4 * harmonic (x, y) = x ^ 2 + 2 * x * y - y ^ 2 - 2 * y - parity x y := by
  have hOne := oneProfile_four x y
  have hZero := zeroProfile_twice 0 (x - 1)
  dsimp [harmonic]
  nlinarith only [hOne, hZero]

/-- All four neighbors have the opposite coordinate-sum parity. -/
theorem neighbor_parities (x y : ℤ) :
    parity (x - 1) y = 1 - parity x y ∧
    parity (x + 1) y = 1 - parity x y ∧
    parity x (y - 1) = 1 - parity x y ∧
    parity x (y + 1) = 1 - parity x y := by
  unfold parity
  omega

/-- The zero endpoint's horizontal second difference is zero. -/
theorem zeroProfile_horizontal (x y : ℤ) :
    zeroProfile (x - 1, y) + zeroProfile (x + 1, y) - 2 * zeroProfile (x, y) = 0 := by
  dsimp [zeroProfile]
  omega

/-- The zero endpoint's vertical second difference is minus one. -/
theorem zeroProfile_vertical (x y : ℤ) :
    zeroProfile (x, y - 1) + zeroProfile (x, y + 1) - 2 * zeroProfile (x, y) = -1 := by
  have h₀ := zeroProfile_twice x y
  have hMinus := zeroProfile_twice x (y - 1)
  have hPlus := zeroProfile_twice x (y + 1)
  nlinarith only [h₀, hMinus, hPlus]

/-- The other endpoint has second difference parity minus one horizontally. -/
theorem oneProfile_horizontal (x y : ℤ) :
    oneProfile (x - 1, y) + oneProfile (x + 1, y) - 2 * oneProfile (x, y) =
      parity x y - 1 := by
  have h₀ := oneProfile_four x y
  have hMinus := oneProfile_four (x - 1) y
  have hPlus := oneProfile_four (x + 1) y
  obtain ⟨hm, hp, _⟩ := neighbor_parities x y
  rw [hm] at hMinus
  rw [hp] at hPlus
  nlinarith only [h₀, hMinus, hPlus]

/-- The same parity formula holds for the vertical second difference. -/
theorem oneProfile_vertical (x y : ℤ) :
    oneProfile (x, y - 1) + oneProfile (x, y + 1) - 2 * oneProfile (x, y) =
      parity x y - 1 := by
  have h₀ := oneProfile_four x y
  have hMinus := oneProfile_four x (y - 1)
  have hPlus := oneProfile_four x (y + 1)
  obtain ⟨_, _, hm, hp⟩ := neighbor_parities x y
  rw [hm] at hMinus
  rw [hp] at hPlus
  nlinarith only [h₀, hMinus, hPlus]

/-- The elementary correction is harmonic for the actual incoming pair. -/
theorem harmonic_native (x y : ℤ) :
    (if (x + y) % 2 = 0 then harmonic (x - 1, y) + harmonic (x + 1, y)
      else harmonic (x, y - 1) + harmonic (x, y + 1)) = 2 * harmonic (x, y) := by
  have h₀ := harmonic_four x y
  obtain ⟨hxm, hxp, hym, hyp⟩ := neighbor_parities x y
  by_cases he : (x + y) % 2 = 0
  · rw [if_pos he]
    have hMinus := harmonic_four (x - 1) y
    have hPlus := harmonic_four (x + 1) y
    rw [hxm] at hMinus
    rw [hxp] at hPlus
    have he' : parity x y = 0 := he
    nlinarith only [h₀, hMinus, hPlus, he']
  · rw [if_neg he]
    have hMinus := harmonic_four x (y - 1)
    have hPlus := harmonic_four x (y + 1)
    rw [hym] at hMinus
    rw [hyp] at hPlus
    have he' : parity x y = 1 := by unfold parity; omega
    nlinarith only [h₀, hMinus, hPlus, he']

/-- Exact real polynomial expression for the first endpoint. -/
theorem zeroProfile_real (x y : ℤ) :
    (zeroProfile (x, y) : ℝ) = -(1 / 2 : ℝ) * (y : ℝ) ^ 2 - (y : ℝ) / 2 := by
  have h : (2 : ℝ) * (zeroProfile (x, y) : ℝ) = -(y : ℝ) * ((y : ℝ) + 1) := by
    exact_mod_cast zeroProfile_twice x y
  nlinarith only [h]

/-- Exact quadratic, linear and parity terms for the second endpoint. -/
theorem oneProfile_real (x y : ℤ) :
    (oneProfile (x, y) : ℝ) = -(1 / 4 : ℝ) * ((x : ℝ) - (y : ℝ)) ^ 2 +
      ((x : ℝ) - (y : ℝ)) / 2 - (parity x y : ℝ) / 4 := by
  have h : (4 : ℝ) * (oneProfile (x, y) : ℝ) =
      -((x : ℝ) - (y : ℝ)) ^ 2 + 2 * ((x : ℝ) - (y : ℝ)) - (parity x y : ℝ) := by
    exact_mod_cast oneProfile_four x y
  linarith only [h]

/-- The source harmonic matrix and its exact affine/parity remainder. -/
theorem harmonic_real (x y : ℤ) :
    (harmonic (x, y) : ℝ) = (1 / 4 : ℝ) *
      ((x : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) - (y : ℝ) ^ 2) -
        (y : ℝ) / 2 - (parity x y : ℝ) / 4 := by
  have h : (4 : ℝ) * (harmonic (x, y) : ℝ) =
      (x : ℝ) ^ 2 + 2 * (x : ℝ) * (y : ℝ) - (y : ℝ) ^ 2 -
        2 * (y : ℝ) - (parity x y : ℝ) := by
    exact_mod_cast harmonic_four x y
  linarith only [h]

end FLattice.Auxiliary.ElementaryProfiles
