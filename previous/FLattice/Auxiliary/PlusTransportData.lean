import FLattice.Auxiliary.TransportStarNormalization
import FLattice.Auxiliary.PeriodCostAttainment
import FLattice.Auxiliary.MiddleCostAttainment

/-!
# Literal data of the plus infimum transport

All coefficients, sample points and target displacements are defined for
integer `m`; the preservation theorem will impose `1 ≤ m`. The two
already proved attainment families are connected to these same formulas.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusTransport

/-- The coefficient of the first square in the integer transport cost. -/
def squareCoefficient (m : ℤ) : ℤ := 2 * m ^ 2 + 2 * m - 1

/-- The literal real period matrix, for every integer coefficient. -/
noncomputable def periodMatrix (m : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4 * (m : ℝ) ^ 2 + 4 * (m : ℝ) - 2, 2 * (m : ℝ); 2 * (m : ℝ), 2]

/-- The cost `J*a²+(m*a+b)²+m*a`, written through its Hessian coefficients. -/
def cost (m : ℤ) (p : ℤ × ℤ) : ℤ :=
  TransportStarNormalization.cost (squareCoefficient m) (2 * m) 1 m 0 p

/-- The source coordinate `Bw`, where `B=[[-2m,-1],[-1,0]]`. -/
def backwardPoint (m : ℤ) (w : ℤ × ℤ) : ℤ × ℤ := (-2 * m * w.1 - w.2, -w.1)

/-- The literal argument `Bw-Cp` of the unknown integer function. -/
def samplePoint (m : ℤ) (w p : ℤ × ℤ) : ℤ × ℤ :=
  TransportStarNormalization.samplePoint (squareCoefficient m) (2 * m) 1
    (backwardPoint m w).1 (backwardPoint m w).2 p

/-- Image under `B` of the positive incoming target direction. -/
def direction (m : ℤ) (ε : Fin 2) : ℤ × ℤ :=
  if ε = 0 then (-2 * m, -1) else (-1, 0)

/-- The target center (`c=0`) or either of its native incoming neighbors. -/
def targetPoint (w : ℤ × ℤ) (ε : Fin 2) (c : ℤ) : ℤ × ℤ :=
  if ε = 0 then (w.1 + c, w.2) else (w.1, w.2 + c)

/-- This is exactly the cost written in the mathematical source. -/
theorem cost_eq (m : ℤ) (p : ℤ × ℤ) :
    cost m p = (m ^ 2 + 2 * m - 1) * p.1 ^ 2 + (m * p.1 + p.2) ^ 2 + m * p.1 := by
  simp only [cost, squareCoefficient, TransportStarNormalization.cost]
  ring

/-- The source point has the parity of the target point, for every signed index. -/
theorem samplePoint_parity (m : ℤ) (w p : ℤ × ℤ) :
    ((samplePoint m w p).1 + (samplePoint m w p).2) % 2 = (w.1 + w.2) % 2 := by
  have hIdentity : (samplePoint m w p).1 + (samplePoint m w p).2 =
      -(w.1 + w.2) + 2 * (-m * w.1 - squareCoefficient m * p.1 - m * p.2 - m * p.1 - p.2) := by
    simp only [samplePoint, backwardPoint, TransportStarNormalization.samplePoint]
    ring
  rw [hIdentity]
  omega

/-- Moving by a native target step gives exactly the signed source displacement. -/
theorem samplePoint_at_target (m : ℤ) (w p : ℤ × ℤ) (ε : Fin 2) (c : ℤ) :
    samplePoint m (targetPoint w ε c) p =
      TransportStarNormalization.samplePoint (squareCoefficient m) (2 * m) 1
        ((backwardPoint m w).1 + c * (direction m ε).1)
        ((backwardPoint m w).2 + c * (direction m ε).2) p := by
  fin_cases ε <;> apply Prod.ext <;>
    norm_num [samplePoint, targetPoint, backwardPoint, direction,
      TransportStarNormalization.samplePoint] <;> ring

/-- The target displacement zero is the original target vertex. -/
theorem targetPoint_zero (w : ℤ × ℤ) (ε : Fin 2) : targetPoint w ε 0 = w := by
  fin_cases ε <;> simp [targetPoint]

/-- The infimum at every target point is attained, including `m=1`. -/
theorem exists_minimizer
    (m : ℤ) (hm : 1 ≤ m) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef) (w : ℤ × ℤ) :
    ∃ p : ℤ × ℤ, ∀ q : ℤ × ℤ,
      g (samplePoint m w p) + cost m p ≤ g (samplePoint m w q) + cost m q := by
  by_cases hOne : m = 1
  · subst m
    have hPositiveOne : (M + MiddleProfile.periodMatrix⁻¹).PosDef := by
      simpa only [periodMatrix, MiddleProfile.periodMatrix, Int.cast_one,
        one_pow, mul_one, show (4 : ℝ) + 4 - 2 = 6 by norm_num] using hPositive
    obtain ⟨p, hp⟩ := MiddleCostAttainment.exists_minimizer g M
      (backwardPoint 1 w).1 (backwardPoint 1 w).2 1 0 hGrowth hPositiveOne
    refine ⟨p, ?_⟩
    intro q
    simpa [samplePoint, cost, squareCoefficient, TransportStarNormalization.samplePoint,
      TransportStarNormalization.cost, MiddleCostAttainment.samplePoint,
      MiddleCostAttainment.cost, mul_assoc] using hp q
  · let μ : PlusEvenProfile.Parameter := ⟨m, by omega⟩
    have hPositiveGeneral : (M + (PlusEvenProfile.periodMatrix μ)⁻¹).PosDef := hPositive
    obtain ⟨p, hp⟩ := PeriodCostAttainment.exists_minimizer μ g M
      (backwardPoint m w).1 (backwardPoint m w).2 m 0 hGrowth hPositiveGeneral
    have hSample : ∀ q : ℤ × ℤ, samplePoint m w q =
        PeriodCostAttainment.samplePoint μ (backwardPoint m w).1 (backwardPoint m w).2 q := by
      intro q
      apply Prod.ext <;>
        simp only [samplePoint, squareCoefficient, TransportStarNormalization.samplePoint,
          PeriodCostAttainment.samplePoint, μ] <;> ring
    have hCost : ∀ q : ℤ × ℤ, cost m q = PeriodCostAttainment.cost μ m 0 q := by
      intro q
      rw [cost_eq]
      simp only [PeriodCostAttainment.cost, PlusEvenProfile.halfPeriod, μ, zero_mul, add_zero]
    refine ⟨p, ?_⟩
    intro q
    simpa only [hSample, hCost] using hp q

end FLattice.Auxiliary.PlusTransport
