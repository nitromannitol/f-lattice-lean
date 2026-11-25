import FLatticePaper.Plane.Induction.TwosEPolicy
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Basic

/-! Same class key means the same coset of the period lattice `⟨U, V⟩`, with `U = (a+1, a−1)` and `V = (−2, 2a)`.
Here `a` is even (so `a+1` is odd and prime to `2`); the coefficients are integers. -/

namespace FLatticePaper.TwosEPolicy

theorem class_lattice {a x y x' y' : ℤ} (ha : 4 ≤ a) (he : a % 2 = 0)
    (hk : classKey a (x, y) = classKey a (x', y')) :
    ∃ i l : ℤ, x = x' + i * (a + 1) + l * (-2) ∧ y = y' + i * (a - 1) + l * (2 * a) := by
  have hk' : ((a - 1) * x - (a + 1) * y) % (2 * a * a + 4 * a - 2) =
      ((a - 1) * x' - (a + 1) * y') % (2 * a * a + 4 * a - 2) := hk
  have hd : (2 * a * a + 4 * a - 2) ∣ ((a - 1) * x - (a + 1) * y) - ((a - 1) * x' - (a + 1) * y') := by
    apply Int.dvd_of_emod_eq_zero
    rw [Int.sub_emod, hk', sub_self, Int.zero_emod]
  obtain ⟨m, hm⟩ := hd
  have hdiv2 : (a + 1) ∣ 2 * ((x - x') - 2 * m) :=
    ⟨(x - x') - (y - y') - 2 * (a + 1) * m, by linear_combination (-1 : ℤ) * hm⟩
  have hcop : IsCoprime (a + 1) 2 := ⟨1, -(a / 2), by omega⟩
  obtain ⟨i, hi⟩ := hcop.dvd_of_dvd_mul_left hdiv2
  refine ⟨i, -m, ?_, ?_⟩
  · linear_combination hi
  · have hprod : (a + 1) * (y - (y' + i * (a - 1) + (-m) * (2 * a))) = 0 := by
      linear_combination (-1 : ℤ) * hm + (a - 1) * hi
    rcases mul_eq_zero.mp hprod with h | h
    · omega
    · linarith

end FLatticePaper.TwosEPolicy
