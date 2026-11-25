import FLatticePaper.Tiles.SiteInduction

/-! Task Q25 (b): the four-corner cell test.

For an odd fraction `f = (N, D)` (`N + D` odd) and the unit cell with lower-left corner `z`, the four corners of the cell lie
in `H_f` (`SiteInduction.InH`) exactly when the reduced bounds of Q25 (1) hold at `z`:
`2D − T − k ≤ t(z) ≤ k` and `λ ≤ s(z) ≤ 2T − 2(D − N) − λ`, where `T = tOf f`, `t = tCo f`, `s = sCo f`, the cell offset
`k = D − N` on even cells and `k = max (D − 2N) N` on odd cells, and `λ = lOf f` (`0` on even cells, `min (D − N) (3N − D)`
on odd cells). The parity is that of `z`. -/

namespace FLatticePaper.Tiles.CellFourTests

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction

/-- The cell offset `k_i` of Q25 (1): `D − N` on even cells, `max (D − 2N) N` on odd cells. -/
def cellK (f : Fraction) (ev : Bool) : ℤ :=
  if ev then f.den - f.num else max (f.den - 2 * f.num) f.num

/-- The membership of an even site in `H_f`, with the bounds at the even parity. -/
theorem inH_even_iff (f : Fraction) (z : ℤ × ℤ) (h : (z.1 + z.2) % 2 = 0) :
    InH f z ↔ (aOf f true - tOf f ≤ tCo f z ∧ tCo f z ≤ f.den + f.num - aOf f true) ∧
      (lOf f true ≤ sCo f z ∧ sCo f z ≤ muOf f * tOf f + 2 * f.num - lOf f true) := by
  simp [InH, h, and_assoc]

/-- The membership of an odd site in `H_f`, with the bounds at the odd parity. -/
theorem inH_odd_iff (f : Fraction) (z : ℤ × ℤ) (h : (z.1 + z.2) % 2 = 1) :
    InH f z ↔ (aOf f false - tOf f ≤ tCo f z ∧ tCo f z ≤ f.den + f.num - aOf f false) ∧
      (lOf f false ≤ sCo f z ∧ sCo f z ≤ muOf f * tOf f + 2 * f.num - lOf f false) := by
  have h' : ¬ ((z.1 + z.2) % 2 = 0) := by omega
  simp [InH, h', and_assoc]

/-- **The four-corner cell test (Q25 (1)).** For an odd fraction and a cell with lower-left corner `z`, the four corners are
in `H_f` exactly when the reduced bounds hold, with the parity of `z`. -/
theorem cell_four_tests_iff (f : Fraction) (hodd : (f.num + f.den) % 2 = 1) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (z : ℤ × ℤ) :
    (InH f z ∧ InH f (z.1 + 1, z.2) ∧ InH f (z.1, z.2 + 1) ∧ InH f (z.1 + 1, z.2 + 1)) ↔
      ((2 * f.den - tOf f - cellK f (decide ((z.1 + z.2) % 2 = 0)) ≤ tCo f z ∧
          tCo f z ≤ cellK f (decide ((z.1 + z.2) % 2 = 0))) ∧
        (lOf f (decide ((z.1 + z.2) % 2 = 0)) ≤ sCo f z ∧
          sCo f z ≤ 2 * tOf f - 2 * (f.den - f.num) - lOf f (decide ((z.1 + z.2) % 2 = 0)))) := by
  have hmu : muOf f = 2 := by
    unfold muOf
    rw [if_pos hodd]
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

end FLatticePaper.Tiles.CellFourTests
