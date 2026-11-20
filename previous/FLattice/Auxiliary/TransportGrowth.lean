import FLattice.Auxiliary.TransportGrowthData
import FLattice.Auxiliary.QuadraticTransportGrowth
import FLattice.Auxiliary.PlusTransport
import FLattice.Auxiliary.MinusTransport

/-!
# Concrete transport minima have the computed quadratic growth

The real sampling and cost identities are supplied internally for both
literal integer operators. The existence conclusions combine the proved
integer F-superharmonic transport with its exact computed growth matrix;
there is no assumed output growth or extra sampling/attainment premise.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusTransport

/-- The literal attained plus minimum has the original uniform quadratic
asymptotic with its computed actual-inverse matrix. -/
theorem quadratic_growth_of_minimum
    (m : ℤ) (hm : 1 ≤ m) (g T : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (PlusTransport.periodMatrix m)⁻¹).PosDef)
    (hMinimum : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
      T w = g (samplePoint m w p) + cost m p ∧
      ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(T (x, y) : ℝ) - LatticeQuadraticRounding.quadratic
          (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
            (TransportGrowthData.plusMatrix m) M) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  apply QuadraticTransportGrowth.quadratic_growth_of_minimum
    (PlusTransport.periodMatrix m) M (TransportGrowthData.plusMatrix m)
    (TransportGrowthData.periodMatrix_isSymm m) (TransportGrowthData.periodMatrix_isUnit m hm)
    hPositive (TransportGrowthData.plusLinear m)
    (fun z => (g z : ℝ)) (fun z => (T z : ℝ)) (samplePoint m) (fun p => (cost m p : ℝ))
    (TransportGrowthData.plus_samplePoint_real m) (TransportGrowthData.plus_cost_real m)
  · intro w
    obtain ⟨p, hp, hAll⟩ := hMinimum w
    refine ⟨p, ?_, ?_⟩
    · exact_mod_cast hp
    · intro q
      exact_mod_cast hAll q
  · exact hGrowth

/-- An attained integer plus minimum, native F-superharmonicity and the
computed output growth all follow from the original input hypotheses. -/
theorem exists_superharmonic_minimum_with_growth
    (m : ℤ) (hm : 1 ≤ m) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (PlusTransport.periodMatrix m)⁻¹).PosDef) :
    ∃ T : ℤ × ℤ → ℤ,
      (∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
        T w = g (samplePoint m w p) + cost m p ∧
        ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) ∧
      (∀ x y : ℤ,
        (if (x + y) % 2 = 0 then T (x - 1, y) + T (x + 1, y)
          else T (x, y - 1) + T (x, y + 1)) ≤ 2 * T (x, y)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(T (x, y) : ℝ) - LatticeQuadraticRounding.quadratic
          (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
            (TransportGrowthData.plusMatrix m) M) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) := by
  obtain ⟨T, hMin, hSH⟩ := exists_superharmonic_minimum m hm g M hSuperharmonic hGrowth hPositive
  exact ⟨T, hMin, hSH, quadratic_growth_of_minimum m hm g T M hGrowth hPositive hMin⟩

end FLattice.Auxiliary.PlusTransport

namespace FLattice.Auxiliary.MinusTransport

/-- The literal attained minus minimum has the original uniform quadratic
asymptotic with its computed actual-inverse matrix. -/
theorem quadratic_growth_of_minimum
    (m : ℤ) (hm : 1 ≤ m) (g T : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (PlusTransport.periodMatrix m)⁻¹).PosDef)
    (hMinimum : ∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
      T w = g (samplePoint m w p) + cost m p ∧
      ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(T (x, y) : ℝ) - LatticeQuadraticRounding.quadratic
          (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
            (TransportGrowthData.minusMatrix m) M) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
  apply QuadraticTransportGrowth.quadratic_growth_of_minimum
    (PlusTransport.periodMatrix m) M (TransportGrowthData.minusMatrix m)
    (TransportGrowthData.periodMatrix_isSymm m) (TransportGrowthData.periodMatrix_isUnit m hm)
    hPositive (TransportGrowthData.minusLinear m)
    (fun z => (g z : ℝ)) (fun z => (T z : ℝ)) (samplePoint m) (fun p => (cost m p : ℝ))
    (TransportGrowthData.minus_samplePoint_real m) (TransportGrowthData.minus_cost_real m)
  · intro w
    obtain ⟨p, hp, hAll⟩ := hMinimum w
    refine ⟨p, ?_, ?_⟩
    · exact_mod_cast hp
    · intro q
      exact_mod_cast hAll q
  · exact hGrowth

/-- An attained integer minus minimum, native F-superharmonicity and the
computed output growth all follow from the original input hypotheses. -/
theorem exists_superharmonic_minimum_with_growth
    (m : ℤ) (hm : 1 ≤ m) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (PlusTransport.periodMatrix m)⁻¹).PosDef) :
    ∃ T : ℤ × ℤ → ℤ,
      (∀ w : ℤ × ℤ, ∃ p : ℤ × ℤ,
        T w = g (samplePoint m w p) + cost m p ∧
        ∀ q : ℤ × ℤ, T w ≤ g (samplePoint m w q) + cost m q) ∧
      (∀ x y : ℤ,
        (if (x + y) % 2 = 0 then T (x - 1, y) + T (x + 1, y)
          else T (x, y - 1) + T (x, y + 1)) ≤ 2 * T (x, y)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(T (x, y) : ℝ) - LatticeQuadraticRounding.quadratic
          (MatrixInverseOrder.transportMatrix (PlusTransport.periodMatrix m)⁻¹
            (TransportGrowthData.minusMatrix m) M) (x : ℝ) (y : ℝ)| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) := by
  obtain ⟨T, hMin, hSH⟩ := exists_superharmonic_minimum m hm g M hSuperharmonic hGrowth hPositive
  exact ⟨T, hMin, hSH, quadratic_growth_of_minimum m hm g T M hGrowth hPositive hMin⟩

end FLattice.Auxiliary.MinusTransport

