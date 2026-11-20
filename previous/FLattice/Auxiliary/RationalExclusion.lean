import FLattice.Auxiliary.RationalDescentInduction
import FLattice.Auxiliary.BranchTransportData
import FLattice.Auxiliary.TransportGrowth
import FLattice.Auxiliary.EndpointExclusion
import FLattice.Auxiliary.ElementaryDuality

/-!
# Exclusion above every primitive rational reference matrix

This combines the actual integer transports, their computed uniform growth,
exact branch algebra, literal harmonic duality and endpoint comparisons.
The final theorem has only the original function/growth/strict-domination
hypotheses. No admissibility placeholder or descent-closure premise remains.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalExclusion

open BranchMatrix RationalDescent

private theorem normalized_dual_reference (p : Pair) :
    ElementaryDuality.rotationMatrix.transpose * rankOneMatrix (p.n : ℝ) (p.d : ℝ) *
        ElementaryDuality.rotationMatrix + ElementaryDuality.harmonicMatrix =
      rankOneMatrix ((dual p).n : ℝ) ((dual p).d : ℝ) := by
  have hd : (0 : ℝ) < (p.d : ℝ) := by exact_mod_cast p.d_pos
  have hn : (0 : ℝ) ≤ (p.n : ℝ) := Nat.cast_nonneg _
  have hnd : (p.n : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.n_le_d
  have hb : (dualDivisor p : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (dualDivisor_pos p)
  have hN : (dualDivisor p : ℝ) * ((dual p).n : ℝ) = (p.d : ℝ) - (p.n : ℝ) := by
    rw [← Nat.cast_mul, dual_scale_n, Nat.cast_sub p.n_le_d]
  have hD : (dualDivisor p : ℝ) * ((dual p).d : ℝ) = (p.d : ℝ) + (p.n : ℝ) := by
    rw [← Nat.cast_mul, dual_scale_d, Nat.cast_add]
  have hScale := ElementaryDuality.rankOneMatrix_scale
    ((dual p).n : ℝ) ((dual p).d : ℝ) (dualDivisor p : ℝ) hb
  rw [hN, hD] at hScale
  exact (ElementaryDuality.dual_matrix_reference (p.n : ℝ) (p.d : ℝ) hd hn hnd).trans hScale

/-- No integer F-superharmonic function with the original uniform quadratic
growth can strictly dominate a primitive rational reference matrix. -/
theorem not_strict_dominator
    (p : Pair) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hAbove : (M - rankOneMatrix (p.n : ℝ) (p.d : ℝ)).PosDef) : False := by
  induction p using RationalDescent.induction generalizing g M with
  | hZero p hp =>
    have hd := zero_endpoint p hp
    apply EndpointExclusion.not_strict_dominator 0 g M hSuperharmonic hGrowth
    simpa [hp, hd, rankOneMatrix_zero_one, EndpointExclusion.endpointMatrix] using hAbove
  | hOne p hp =>
    obtain ⟨hn, hd⟩ := one_endpoint p hp
    apply EndpointExclusion.not_strict_dominator 1 g M hSuperharmonic hGrowth
    simpa only [hn, hd, Nat.cast_one, rankOneMatrix_one_one,
      EndpointExclusion.endpointMatrix, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hAbove
  | hDual p _ ih =>
    let N := ElementaryDuality.rotationMatrix.transpose * M * ElementaryDuality.rotationMatrix +
      ElementaryDuality.harmonicMatrix
    have hNewAbove : (N - rankOneMatrix ((dual p).n : ℝ) ((dual p).d : ℝ)).PosDef := by
      have h := ElementaryDuality.rotated_difference_posDef M
        (rankOneMatrix (p.n : ℝ) (p.d : ℝ)) ElementaryDuality.harmonicMatrix hAbove
      rw [normalized_dual_reference] at h
      exact h
    exact ih (ElementaryDuality.dual g) N
      (ElementaryDuality.dual_superharmonic g hSuperharmonic)
      (ElementaryDuality.dual_quadratic_growth g M hGrowth) hNewAbove
  | hPlus child parent k hk hEven hn hd ih =>
    let m : ℤ := (k/2 : ℕ)
    have hkNat : 2*(k/2)=k := by omega
    have hm : 1≤m := by dsimp [m]; omega
    have hkReal : (k : ℝ)=2*(m : ℝ) := by
      have hInt : (k : ℤ)=2*m := by
        dsimp [m]
        exact_mod_cast hkNat.symm
      exact_mod_cast hInt
    have hN : (child.n : ℝ)=(parent.d : ℝ) := by exact_mod_cast hn
    have hD : (child.d : ℝ)=2*(m : ℝ)*(parent.d : ℝ)+(parent.n : ℝ) := by
      rw [hd, Nat.cast_add, Nat.cast_mul, hkReal]
    have hParentD : (0 : ℝ)<(parent.d : ℝ) := by exact_mod_cast parent.d_pos
    have hParentN : (0 : ℝ)≤(parent.n : ℝ) := Nat.cast_nonneg _
    have hParentND : (parent.n : ℝ)≤(parent.d : ℝ) := by exact_mod_cast parent.n_le_d
    rw [hN, hD] at hAbove
    obtain ⟨hDomain, hNewAbove⟩ := plus_integer_coefficient_strict_dominator m hm
      (parent.n : ℝ) (parent.d : ℝ) hParentD hParentN hParentND M hAbove
    obtain ⟨T, _, hTSH, hTGrowth⟩ := PlusTransport.exists_superharmonic_minimum_with_growth
      m hm g M hSuperharmonic hGrowth hDomain
    exact ih T _ hTSH hTGrowth hNewAbove
  | hMinus child parent k hk hEven hp0 hpLt hn hd ih =>
    let m : ℤ := (k/2 : ℕ)-1
    have hkNat : 2*(k/2)=k := by omega
    have hm : 1≤m := by dsimp [m]; omega
    have hkReal : (k : ℝ)=2*(m : ℝ)+2 := by
      have hInt : (k : ℤ)=2*m+2 := by
        have h := congrArg (fun z : ℕ => (z : ℤ)) hkNat
        push_cast at h
        dsimp [m]
        omega
      exact_mod_cast hInt
    have hN : (child.n : ℝ)=(parent.d : ℝ) := by exact_mod_cast hn
    have hSub : parent.n ≤ k*parent.d := by nlinarith only [parent.n_le_d, hk]
    have hD : (child.d : ℝ)=(2*(m : ℝ)+2)*(parent.d : ℝ)-(parent.n : ℝ) := by
      rw [hd, Nat.cast_sub hSub, Nat.cast_mul, hkReal]
    have hParentD : (0 : ℝ)<(parent.d : ℝ) := by exact_mod_cast parent.d_pos
    have hParentN : (0 : ℝ)<(parent.n : ℝ) := by exact_mod_cast hp0
    have hParentND : (parent.n : ℝ)<(parent.d : ℝ) := by exact_mod_cast hpLt
    rw [hN, hD] at hAbove
    obtain ⟨hDomain, hNewAbove⟩ := minus_integer_coefficient_strict_dominator m hm
      (parent.n : ℝ) (parent.d : ℝ) hParentD hParentN hParentND M hAbove
    obtain ⟨T, _, hTSH, hTGrowth⟩ := MinusTransport.exists_superharmonic_minimum_with_growth
      m hm g M hSuperharmonic hGrowth hDomain
    exact ih T _ hTSH hTGrowth hNewAbove

end FLattice.Auxiliary.RationalExclusion
