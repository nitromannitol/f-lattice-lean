import FLatticePaper.Tiles.CellFourTests
import FLatticePaper.Tiles.SubCriteria

/-! Task Q25 (sub), the four-corner cell test for an even fraction.

For an even fraction `f = (N, D)` (`N + D` even, so `μ = 1`) and the unit cell with lower-left corner `z`, the four corners of the
cell lie in `H_f` exactly when `2D − T − k ≤ t(z) ≤ k` and `λ ≤ s(z) ≤ T − 2(D − N) − λ`, with `T = tOf f`, `k = cellK f ev` and
`λ = lOf f ev` at the parity `ev` of `z`. This is `cell_four_tests_iff` with `μ = 1` in place of `μ = 2`. -/

namespace FLatticePaper.Tiles.CellFourEven

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.CellFourTests

/-- **The four-corner cell test for an even fraction.** -/
theorem cell_four_tests_even (f : Fraction) (hev : (f.num + f.den) % 2 = 0) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (z : ℤ × ℤ) :
    (InH f z ∧ InH f (z.1 + 1, z.2) ∧ InH f (z.1, z.2 + 1) ∧ InH f (z.1 + 1, z.2 + 1)) ↔
      ((2 * f.den - tOf f - cellK f (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo f z ∧
          tCo f z ≤ cellK f (decide ((z.1 + z.2) % 2 = 0))) ∧
        (lOf f (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo f z ∧
          sCo f z ≤ tOf f - 2 * (f.den - f.num) - lOf f (decide ((z.1 + z.2) % 2 = 0)))) := by
  have hmu : muOf f = 1 := by
    unfold muOf
    rw [if_neg (by omega)]
  have e1 : tCo f (z.1 + 1, z.2) = tCo f z + f.num := by unfold tCo; ring
  have e2 : tCo f (z.1, z.2 + 1) = tCo f z - f.den := by unfold tCo; ring
  have e3 : tCo f (z.1 + 1, z.2 + 1) = tCo f z + f.num - f.den := by unfold tCo; ring
  have s1 : sCo f (z.1 + 1, z.2) = sCo f z + (f.den + f.num) := by unfold sCo; ring
  have s2 : sCo f (z.1, z.2 + 1) = sCo f z + (f.den - f.num) := by unfold sCo; ring
  have s3 : sCo f (z.1 + 1, z.2 + 1) = sCo f z + 2 * f.den := by unfold sCo; ring
  rcases (show (z.1 + z.2) % 2 = 0 ∨ (z.1 + z.2) % 2 = 1 by omega) with h0 | h1
  · have hd : decide ((z.1 + z.2) % 2 = 0) = true := decide_eq_true h0
    rw [hd]
    rw [inH_even_iff f z h0,
      inH_odd_iff f (z.1 + 1, z.2) (show (z.1 + 1 + z.2) % 2 = 1 by omega),
      inH_odd_iff f (z.1, z.2 + 1) (show (z.1 + (z.2 + 1)) % 2 = 1 by omega),
      inH_even_iff f (z.1 + 1, z.2 + 1) (show (z.1 + 1 + (z.2 + 1)) % 2 = 0 by omega),
      e1, e2, e3, s1, s2, s3, hmu]
    simp only [aOf, lOf, cellK, if_true, if_false, Bool.false_eq_true]
    simp only [min_def]
    split_ifs <;> omega
  · have hd : decide ((z.1 + z.2) % 2 = 0) = false := by
      simp [h1]
    rw [hd]
    rw [inH_odd_iff f z h1,
      inH_even_iff f (z.1 + 1, z.2) (show (z.1 + 1 + z.2) % 2 = 0 by omega),
      inH_even_iff f (z.1, z.2 + 1) (show (z.1 + (z.2 + 1)) % 2 = 0 by omega),
      inH_odd_iff f (z.1 + 1, z.2 + 1) (show (z.1 + 1 + (z.2 + 1)) % 2 = 1 by omega),
      e1, e2, e3, s1, s2, s3, hmu]
    simp only [aOf, lOf, cellK, if_true, if_false, Bool.false_eq_true]
    simp only [min_def, max_def]
    split_ifs <;> omega

end FLatticePaper.Tiles.CellFourEven
