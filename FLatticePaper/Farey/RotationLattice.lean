import FLatticePaper.Farey.Rotation
import FLatticePaper.Farey.PeriodDeck
import Mathlib.Tactic.LinearCombination

namespace FLatticePaper.Farey

/-- Multiplication by `I` on `ℤ[I] = ℤ²`. -/
def mulI (site : Site) : Site := (-site.2, site.1)

/-- `lemma:rot_parity-laplace` (line 539): the rotation `(n,d) ↦ (d-n, n+d)`, halved for even fractions, is reduced
and flips parity. -/
theorem rot_parity_laplace {fraction : Fraction} (hinterval : fraction.InUnitInterval)
    (hreduced : fraction.Reduced) :
    (fraction.Even →
      Int.gcd ((fraction.den - fraction.num) / 2) ((fraction.num + fraction.den) / 2) = 1 ∧
        fraction.rotate.Reduced ∧ fraction.rotate.Odd) ∧
    (fraction.Odd →
      Int.gcd (fraction.den - fraction.num) (fraction.num + fraction.den) = 1 ∧
        fraction.rotate.Reduced ∧ fraction.rotate.Even) := by
  refine ⟨fun heven => ⟨?_, fraction.rotate_reduced hinterval hreduced,
      fraction.rotate_odd_of_even heven hreduced⟩,
    fun hodd => ⟨?_, fraction.rotate_reduced hinterval hreduced, fraction.rotate_even_of_odd hodd⟩⟩
  · have hpar : (fraction.num + fraction.den) % 2 = 0 := heven
    obtain ⟨x, y, h⟩ := hreduced
    obtain ⟨a, ha⟩ : ∃ a, a = (fraction.den - fraction.num) / 2 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = (fraction.num + fraction.den) / 2 := ⟨_, rfl⟩
    rw [← ha, ← hb]
    have hd : fraction.den = a + b := by omega
    have hn : fraction.num = b - a := by omega
    refine Int.isCoprime_iff_gcd_eq_one.mp ⟨y - x, x + y, ?_⟩
    linear_combination h - x * hn - y * hd
  · have hpar : (fraction.num + fraction.den) % 2 = 1 := hodd
    obtain ⟨x, y, h⟩ := hreduced
    obtain ⟨k, hk⟩ : ∃ k, fraction.num + fraction.den = 2 * k + 1 := ⟨(fraction.num + fraction.den) / 2, by omega⟩
    refine Int.isCoprime_iff_gcd_eq_one.mp ⟨-k * (y - x), 1 - k * (x + y), ?_⟩
    linear_combination (-2 * k) * h + hk

/-- `lemma:lattice_rotation` (line 683), odd case. -/
theorem lattice_rotation_odd {fraction : Fraction} (hodd : fraction.Odd) :
    fraction.rotate.unmodifiedDeck.kernel = -mulI fraction.unmodifiedDeck.transverse ∧
      fraction.rotate.unmodifiedDeck.transverse = mulI ((2 : ℤ) • fraction.unmodifiedDeck.kernel) := by
  rw [Fraction.rotate_of_odd hodd]
  constructor
  · refine Prod.ext ?_ ?_ <;> simp [mulI, Fraction.unmodifiedDeck]
    omega
  · refine Prod.ext ?_ ?_ <;> simp [mulI, Fraction.unmodifiedDeck] <;> omega

/-- `lemma:lattice_rotation` (line 683), even case. -/
theorem lattice_rotation_even {fraction : Fraction} (heven : fraction.Even) :
    (2 : ℤ) • fraction.rotate.unmodifiedDeck.kernel = -mulI fraction.unmodifiedDeck.transverse ∧
      fraction.rotate.unmodifiedDeck.transverse = mulI fraction.unmodifiedDeck.kernel := by
  have hpar : (fraction.num + fraction.den) % 2 = 0 := heven
  rw [Fraction.rotate_of_even heven]
  constructor
  · refine Prod.ext ?_ ?_ <;> simp [mulI, Fraction.unmodifiedDeck] <;> omega
  · refine Prod.ext ?_ ?_ <;> simp [mulI, Fraction.unmodifiedDeck] <;> omega

end FLatticePaper.Farey
