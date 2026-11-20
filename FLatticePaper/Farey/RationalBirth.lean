import FLatticePaper.Farey.Birth
import Mathlib.Data.Rat.Defs

namespace FLatticePaper.Farey

def Fraction.ofRat (value : ℚ) : Fraction := ⟨value.num, value.den⟩

def Fraction.toRat (fraction : Fraction) : ℚ := Rat.divInt fraction.num fraction.den

@[simp]
theorem Fraction.toRat_ofRat (value : ℚ) : (ofRat value).toRat = value :=
  Rat.num_divInt_den value

theorem Fraction.ofRat_reduced (value : ℚ) : (ofRat value).Reduced := by
  rw [Reduced, Int.isCoprime_iff_gcd_eq_one]
  change value.num.natAbs.gcd value.den = 1
  exact value.reduced

theorem Fraction.ofRat_toRat {fraction : Fraction} (hden : 0 < fraction.den)
    (hreduced : fraction.Reduced) : ofRat fraction.toRat = fraction := by
  have hgcd := Int.isCoprime_iff_gcd_eq_one.mp hreduced.symm
  apply Fraction.ext
  · change (Rat.divInt fraction.num fraction.den).num = fraction.num
    rw [Rat.num_divInt, hgcd, Int.sign_eq_one_of_pos hden]
    simp
  · change ((Rat.divInt fraction.num fraction.den).den : ℤ) = fraction.den
    rw [Rat.den_divInt, if_neg (ne_of_gt hden), hgcd, Nat.div_one]
    exact Int.ofNat_natAbs_of_nonneg hden.le

theorem Fraction.ofRat_interior {value : ℚ} (hlo : 0 < value) (hhi : value < 1) :
    (ofRat value).Interior := by
  have hlo' := (Rat.lt_iff 0 value).mp hlo
  have hhi' := (Rat.lt_iff value 1).mp hhi
  simp only [Rat.num_zero, Rat.den_zero, Rat.num_one, Rat.den_one, Nat.cast_one,
    zero_mul, one_mul, mul_one] at hlo' hhi'
  exact ⟨hlo', hhi'⟩

/-- The generated odd and even birth registers enumerate every reduced
interior rational exactly once. -/
theorem existsUnique_rational_birth (value : ℚ) (hlo : 0 < value) (hhi : value < 1) :
    ∃! birth : Birth, birth.fraction.toRat = value := by
  obtain ⟨birth, hbirth, hunique⟩ :=
    existsUnique_birth (Fraction.ofRat value) (Fraction.ofRat_interior hlo hhi)
      (Fraction.ofRat_reduced value)
  refine ⟨birth, ?_, ?_⟩
  · change birth.fraction.toRat = value
    rw [hbirth, Fraction.toRat_ofRat]
  · intro other hOther
    apply hunique other
    have hinterior := other.interior
    have hden : 0 < other.fraction.den := hinterior.inUnitInterval.1
    rw [← Fraction.ofRat_toRat hden other.reduced, hOther]

end FLatticePaper.Farey
