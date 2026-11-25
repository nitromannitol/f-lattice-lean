import FLatticePaper.Plane.Induction.PsiCalibration

/-! Task 116 / the boundary bound `hbd` (Q22, `H_SOURCE_ANCESTRAL_CLOSURE.md` §§2–3): the H-source arc.

Block (2) of the Q22 argument: the harmonic strip `h₀(x,y) = ⌊(x+y)²/4⌋ − y(y+1)/2` is the Lean `harmonicGrid`, and the two pairs of
reduction points give the values `0, 1` (phase zero: `h₀(1,0)`, `h₀(2,0)`; phase one: `h₀(0,−1)`, `h₀(−1,−1)`).

Block (1), the zero at the specified endpoint, is already in `PsiCalibration`: `sheetPsi_hLast_W1` (`Ψ(H_last) = 0`, phase one) and the
phase-zero value `sheetPsi_H0_W0`. Blocks (3) and (4) (the arc monotonicity of `Ψ` along the retained H-arc edges, and the assembly of
`P ≤ c₀` on the boundary) are not proved here: the arc edges are the hypothesis `hret` of `ArcPsi.psi_arc_W0` / `psi_arc_W1`. -/

namespace FLatticePaper.HSourceBound

open FLatticePaper FLatticePaper.Induction

/-- **The harmonic strip is the Lean harmonic grid.** `harmonicGrid (x,y) = ⌊(x+y)²/4⌋ − y(y+1)/2` (Q22's `h₀`). -/
theorem harmonicGrid_eq_strip (x : Site) :
    harmonicGrid x = (x.1 + x.2) ^ 2 / 4 - x.2 * (x.2 + 1) / 2 := by
  have hP : x.2 * (x.2 + 1) % 2 = 0 := Int.even_iff.mp (Int.even_mul_succ_self x.2)
  have hS : (x.1 + x.2) ^ 2 % 4 = (x.1 + x.2) % 2 := by
    rcases Int.even_or_odd (x.1 + x.2) with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> ring_nf <;> omega
  have hN : x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 = (x.1 + x.2) ^ 2 - 2 * (x.2 * (x.2 + 1)) := by
    ring
  unfold harmonicGrid
  rw [hN]
  omega

/-- The phase-zero reduction pair: `h₀(1,0) = 0` and `h₀(2,0) = 1` (Q22, block (2)). -/
theorem harmonic_pair_zero : harmonicGrid (1, 0) = 0 ∧ harmonicGrid (2, 0) = 1 := by
  constructor <;> norm_num [harmonicGrid]

/-- The phase-one reduction pair: `h₀(0,−1) = 0` and `h₀(−1,−1) = 1` (Q22, block (2)). -/
theorem harmonic_pair_one : harmonicGrid (0, -1) = 0 ∧ harmonicGrid (-1, -1) = 1 := by
  constructor <;> norm_num [harmonicGrid]

/-- Both reduction pairs equal `0, 1` (Q22, block (2)): the other offer's harmonic part is `0` at the first point and `1` at the second. -/
theorem harmonic_pairs : (harmonicGrid (1, 0) = 0 ∧ harmonicGrid (2, 0) = 1) ∧
    (harmonicGrid (0, -1) = 0 ∧ harmonicGrid (-1, -1) = 1) :=
  ⟨harmonic_pair_zero, harmonic_pair_one⟩

end FLatticePaper.HSourceBound
