import FLatticePaper.Plane.Induction.OddStep

/-! # The harmonic shifts of the zone argument of I1 (task 49, steps (a) and (b) of the fix)

Notation as in fixes/Q4-strips.md: `Z(x) = (−x₂, x₁ − 1)`, `f = quarterTurnField F = F ∘ Z + h₀`, so `f − h₀ = F ∘ Z`.
The kernel of the earlier conjugate is `κ = (D + N, D − N)`, its transverse vector is `τ = (−2N, 2D)`, and `V_p = (−(D − N), D + N)`.
Step (a): `f − h₀` is invariant under `V_p`, because `Z(x + V_p) = Z x − κ` and `F` has zero kernel constant.
-/

namespace FLatticePaper.Induction
open FLatticePaper

namespace ZoneHarmonic

/-- The harmonic grid along the shift `V = (α + β, α − β)`: `h₀(x) − h₀(x − V) = α x₁ + β x₂ + c` where `2c` is the
explicit constant `−2αβ − α² + β² − α + β`. -/
theorem harmonicGrid_sub_shift (x : Site) (α β c : ℤ)
    (hc : 2 * c = -2 * α * β - α ^ 2 + β ^ 2 - α + β) :
    harmonicGrid x - harmonicGrid (x - (α + β, α - β)) = α * x.1 + β * x.2 + c := by
  have hpar : (x.1 + x.2) % 2 = (x.1 - (α + β) + (x.2 - (α - β))) % 2 := by omega
  unfold harmonicGrid
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [hpar]
  have key : x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - (x.1 - (α + β) + (x.2 - (α - β))) % 2
      = ((x.1 - (α + β)) ^ 2 + 2 * (x.1 - (α + β)) * (x.2 - (α - β)) - (x.2 - (α - β)) ^ 2
          - 2 * (x.2 - (α - β)) - (x.1 - (α + β) + (x.2 - (α - β))) % 2) + 4 * (α * x.1 + β * x.2 + c) := by
    linear_combination (-2 : ℤ) * hc
  rw [key, Int.add_mul_ediv_left _ _ (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-- Step (a): `F ∘ Z` is invariant under the shift `V_p = (−(D − N), D + N)`, given the kernel constant zero:
`F(y + κ) = F y` for `κ = (D + N, D − N)`. Hence `f − h₀` is `V_p`-invariant. -/
theorem fZ_add_Vp (F : Site → ℤ) (N D : ℤ) (hK : ∀ y : Site, F (y + (D + N, D - N)) = F y) (x : Site) :
    F (-(x.2 + (D + N)), x.1 - (D - N) - 1) = F (-x.2, x.1 - 1) := by
  have hZ : (-(x.2 + (D + N)), x.1 - (D - N) - 1) = (-x.2, x.1 - 1) - (D + N, D - N) := by
    ext <;> simp <;> ring
  rw [hZ, ← hK ((-x.2, x.1 - 1) - (D + N, D - N))]
  congr 1
  ext <;> simp

/-- Step (b): `U_p = (2D, 2N)` is a zero period of the quarter-turn field `f = F ∘ Z + h₀`. The transverse period of `F`
(`F(y + τ) = F y + t(y) − (B + D)` for `τ = (−2N, 2D)`, `t(y) = (D − N) y₁ − (D + N) y₂`, `B = D² + 2DN − N²`) and the harmonic
shift along `(D + N, D − N)` (constant `−B − N`) cancel exactly. -/
theorem quarterTurnField_add_Up (F : Field) (N D : ℤ)
    (hT : ∀ y : Site, F (y + (-2 * N, 2 * D)) =
      F y + ((D - N) * y.1 - (D + N) * y.2) - (D ^ 2 + 2 * D * N - N ^ 2 + D))
    (x : Site) :
    quarterTurnField F (x + (2 * D, 2 * N)) = quarterTurnField F x := by
  unfold quarterTurnField
  rw [quarterTurn_site, quarterTurn_site]
  have hZ : (-(x + (2 * D, 2 * N)).2, (x + (2 * D, 2 * N)).1 - 1) = (-x.2, x.1 - 1) + (-2 * N, 2 * D) := by
    ext <;> simp <;> ring
  have hc : 2 * (-(D ^ 2 + 2 * D * N - N ^ 2) - N) =
      -2 * (D + N) * (D - N) - (D + N) ^ 2 + (D - N) ^ 2 - (D + N) + (D - N) := by ring
  have hh := harmonicGrid_sub_shift (x + (2 * D, 2 * N)) (D + N) (D - N)
    (-(D ^ 2 + 2 * D * N - N ^ 2) - N) hc
  have e : x + (2 * D, 2 * N) - ((D + N) + (D - N), (D + N) - (D - N)) = x := by
    ext <;> simp <;> ring
  rw [e] at hh
  simp only [Prod.fst_add, Prod.snd_add] at hh
  rw [hZ, hT]
  dsimp only
  linear_combination hh

end ZoneHarmonic

end FLatticePaper.Induction
