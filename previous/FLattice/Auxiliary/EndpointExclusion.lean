import FLattice.Auxiliary.EndpointRanks

/-!
# No integer superharmonic matrix strictly dominates either endpoint

The reference formulas and directed ranks are proved on the whole plane.
Original quadratic growth and actual positive matrix difference give proper
gap sublevels. The graph-independent rank principle supplies the contradiction.
No recurrence or boundary comparison is assumed.
-/

set_option autoImplicit false
open scoped BigOperators

namespace FLattice.Auxiliary.EndpointExclusion

open ElementaryProfiles

/-- The two literal quadratic endpoint matrices from the manuscript. -/
noncomputable def endpointMatrix (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if i = 0 then !![0, 0; 0, -1] else !![-(1/2:ℝ), 1/2; 1/2, -(1/2)]

/-- Both integer references are bounded perturbations of their exact
quadratic and linear parts. -/
theorem profile_reference (i : Fin 2) (x y : ℤ) :
    |(EndpointRanks.profile i (x, y) : ℝ) - (-(1 / 2 : ℝ) *
      ((x : ℝ) * (-endpointMatrix i) 0 0 * (x : ℝ) +
        (x : ℝ) * (-endpointMatrix i) 0 1 * (y : ℝ) +
        (y : ℝ) * (-endpointMatrix i) 1 0 * (x : ℝ) +
        (y : ℝ) * (-endpointMatrix i) 1 1 * (y : ℝ)) +
      (if i = 0 then (0 : ℝ) else 1/2) * (x : ℝ) +
        (-(1/2:ℝ)) * (y : ℝ) + 0)| ≤ 1 := by
  fin_cases i
  · norm_num [EndpointRanks.profile, endpointMatrix, zeroProfile_real, Matrix.neg_apply]
    ring_nf
    norm_num
  · norm_num [EndpointRanks.profile, endpointMatrix, oneProfile_real, Matrix.neg_apply]
    have he := parity_cases x y
    rcases he with he | he <;> rw [he] <;> norm_num <;> ring_nf <;> norm_num

/-- Strict endpoint domination yields finite integer gap sublevels from
the original uniform quadratic growth assumption. -/
theorem finite_gap_sublevels
    (i : Fin 2) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M - endpointMatrix i).PosDef) :
    ∀ t : ℤ, {z : ℤ × ℤ | g z - EndpointRanks.profile i z ≤ t}.Finite := by
  intro t
  have hFinite := QuadraticGap.finite_sublevels
    (fun z : ℤ × ℤ => (g z : ℝ))
    (fun z : ℤ × ℤ => (EndpointRanks.profile i z : ℝ))
    M (-endpointMatrix i) (if i = 0 then 0 else 1/2) (-(1/2)) 0 1
    hGrowth (profile_reference i) (by simpa only [sub_eq_add_neg] using hPositive) (t : ℝ)
  apply hFinite.subset
  intro z hz
  change (g z : ℝ) - (EndpointRanks.profile i z : ℝ) ≤ (t : ℝ)
  exact_mod_cast hz

/-- Original integer F-superharmonicity and quadratic growth exclude
a strictly positive matrix difference from either literal endpoint. -/
theorem not_strict_dominator
    (i : Fin 2) (g : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then g (x - 1, y) + g (x + 1, y)
        else g (x, y - 1) + g (x, y + 1)) ≤ 2 * g (x, y))
    (hGrowth : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(g (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          δ * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M - endpointMatrix i).PosDef) : False := by
  apply not_proper_gap_of_ranked_incoming (fun _ : ℤ × ℤ => 2) EndpointRanks.incoming
    (fun z => g z - EndpointRanks.profile i z) (EndpointRanks.deficit i)
    (EndpointRanks.rank i) (0, 0)
  · rintro ⟨x, y⟩
    rw [Finset.sum_sub_distrib, EndpointRanks.profile_incoming_sum,
      EndpointRanks.incoming_sum]
    have h := hSuperharmonic x y
    norm_num only [Nat.cast_ofNat]
    omega
  · exact EndpointRanks.selected_incoming i
  · exact finite_gap_sublevels i g M hGrowth hPositive

end FLattice.Auxiliary.EndpointExclusion
