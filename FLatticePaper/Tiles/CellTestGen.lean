import FLatticePaper.Tiles.SubCriteria
import FLatticePaper.Tiles.SubBlockEven

/-! Task Q25 (completeness of the seam), the four-test bound (1) of `fixes/Q25.md` for every fraction.

For a fraction `f = (N, D)` with `0 < N < D`, the lower-left corner `(x, y)` of a cell lies in the cell tile of `H_f` (all four corners in
`H_f`) exactly when `2D − T − k ≤ t ≤ k` and `λ ≤ s ≤ μT − 2(D − N) − λ`, with `t = N x − D y`, `s = (D + N) x + (D − N) y`, `μ = muOf f`,
and `k`, `λ` at the parity of `x + y`. This unifies the odd (`μ = 2`) and even (`μ = 1`) forms. -/

namespace FLatticePaper.Tiles.CellTestGen

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.CellFourTests
  FLatticePaper.Tiles.StandardClause

theorem cell_test_gen (f : Fraction) (hpos : 0 < f.num) (hlt : f.num < f.den) (P : Finset GInt)
    (hP : ∀ z : GInt, z ∈ P ↔ InH f z) (x y : ℤ) :
    cellCorners (x, y) ⊆ P ↔
      ((2 * f.den - tOf f - cellK f (decide ((x + y) % 2 = 0)) ≤ f.num * x - f.den * y ∧
          f.num * x - f.den * y ≤ cellK f (decide ((x + y) % 2 = 0))) ∧
        (lOf f (decide ((x + y) % 2 = 0)) ≤ (f.den + f.num) * x + (f.den - f.num) * y ∧
          (f.den + f.num) * x + (f.den - f.num) * y ≤
            muOf f * tOf f - 2 * (f.den - f.num) - lOf f (decide ((x + y) % 2 = 0)))) := by
  by_cases hodd : (f.num + f.den) % 2 = 1
  · have hmu : muOf f = 2 := by
      unfold muOf
      rw [if_pos hodd]
    rw [hmu]
    exact SubCriteria.cellCorners_subset_iff_bounds f hodd hpos hlt P hP (x, y)
  · have hev : (f.num + f.den) % 2 = 0 := by omega
    have hmu : muOf f = 1 := by
      unfold muOf
      rw [if_neg hodd]
    rw [hmu, one_mul]
    exact SubBlockEven.cellCorners_subset_iff_bounds_even f hev hpos hlt P hP (x, y)

end FLatticePaper.Tiles.CellTestGen
