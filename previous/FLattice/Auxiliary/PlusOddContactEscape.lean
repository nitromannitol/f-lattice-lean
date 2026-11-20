import FLattice.Auxiliary.PlusOddActiveEdges
import FLattice.Auxiliary.PlusOddComparison
import FLattice.Auxiliary.PlusOddNegativeShift
import FLattice.Auxiliary.PlusOddAddedContact
import FLattice.Auxiliary.FiniteComparison

/-!
# Strict odd comparison on the physical contact region and both root bounds

The global lower comparison controls every incoming value. At a contact,
integer counting forces a selected predecessor to remain a contact. All
selected edges stay in the actual one-period region and lower the physical
rank, so a finite contact set there is empty. The negative root bound then
uses two ordinary integer averages, without an augmented region or rank.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary.PlusOddProfile

open PlusEvenProfile DirectionalRank

/-- Actual incoming selections exclude all finite contacts in the original
physical active region. Only the reference geometry is periodic. -/
theorem profile_strict_on_active_of_finite_sublevel
    (m : Parameter) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z : ℤ × ℤ, profile m z.1 z.2 ≤ h z)
    (hFinite : {z : ℤ × ℤ | h z - profile m z.1 z.2 ≤ 0}.Finite) :
    ∀ x y : ℤ, activePoint m x y → profile m x y + 1 ≤ h (x, y) := by
  let u : ℤ × ℤ → ℤ := fun z => profile m z.1 z.2
  let contacts : Set (ℤ × ℤ) := {z | activePoint m z.1 z.2 ∧ h z - u z = 0}
  have hContactFinite : contacts.Finite := hFinite.subset (fun z hz => by
    change activePoint m z.1 z.2 ∧ h z - u z = 0 at hz
    change h z - u z ≤ 0
    omega)
  have hNoContacts : ¬contacts.Nonempty := by
    apply not_nonempty_of_finite_rank_descent contacts
      (fun z => leftRank z.1 (z.2 + 1)) hContactFinite
    intro z hz
    obtain ⟨hActive, hContact⟩ := hz
    obtain ⟨S, hCount, hSelected⟩ := activePoint_selected m z.1 z.2 hActive
    rw [← incomingDeficit_eq_table] at hCount
    have hStar : (∑ i : Fin 2, h (incomingPoint z.1 z.2 i)) - 2 * h z ≤ 0 := by
      rw [incomingPoint_sum]
      have hSH := hSuperharmonic z.1 z.2
      simpa only [Prod.mk.eta, sub_nonpos] using hSH
    have hSumUpper := sum_incoming_gap_le (incomingPoint z.1 z.2) h u z 2 0
      (incomingDeficit m z.1 z.2) hStar (incomingDeficit_eq_residual m z.1 z.2)
    rw [hContact, mul_zero, zero_add] at hSumUpper
    have hInputLower : ∀ i : Fin 2, 0 ≤ h (incomingPoint z.1 z.2 i) -
        u (incomingPoint z.1 z.2 i) := by
      intro i
      have hBound := hLower (incomingPoint z.1 z.2 i)
      dsimp [u]
      omega
    have hInputContact : ∃ i ∈ S,
        h (incomingPoint z.1 z.2 i) - u (incomingPoint z.1 z.2 i) = 0 := by
      by_contra hNoInput
      have hStrict : ∀ i ∈ S, 0 + 1 ≤ h (incomingPoint z.1 z.2 i) -
          u (incomingPoint z.1 z.2 i) := by
        intro i hi
        have hNonnegative := hInputLower i
        have hNe : h (incomingPoint z.1 z.2 i) - u (incomingPoint z.1 z.2 i) ≠ 0 :=
          fun hEq => hNoInput ⟨i, hi, hEq⟩
        omega
      have hSumLower := card_mul_add_card_le_sum
        (fun i : Fin 2 => h (incomingPoint z.1 z.2 i) - u (incomingPoint z.1 z.2 i))
        0 S hInputLower hStrict
      omega
    obtain ⟨i, hi, hEq⟩ := hInputContact
    obtain ⟨hMember, hRank⟩ := hSelected i hi
    exact ⟨incomingPoint z.1 z.2 i, ⟨hMember, hEq⟩, hRank⟩
  intro x y hActive
  have hBound := hLower (x, y)
  have hNe : h (x, y) - profile m x y ≠ 0 :=
    fun hEq => hNoContacts ⟨(x, y), ⟨hActive, hEq⟩⟩
  dsimp at hBound
  omega

/-- Positive signed pin data, original quadratic growth and strict matrix
domination force the strict odd root bound. -/
theorem one_le_origin_of_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (-1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    1 ≤ h (0, 0) := by
  have hLower := profile_le_of_quadratic_growth m h M hSuperharmonic hGrowth hPositive hPrescribed
  have hFinite := finite_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive 0
  have hStrict := profile_strict_on_active_of_finite_sublevel m h hSuperharmonic hLower hFinite
    0 0 (activePoint_origin m)
  simpa only [profile_origin, zero_add] using hStrict

/-- Negative signed pin data give the same root bound. The two extra
integer averages replace the source's enlarged contact region. -/
theorem one_le_origin_of_negative_quadratic_growth
    (m : Parameter) (h : ℤ × ℤ → ℤ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hGrowth : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x y : ℤ,
      R ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 →
        |(h (x, y) : ℝ) - (1 / 2 : ℝ) *
          ((x : ℝ) * M 0 0 * (x : ℝ) + (x : ℝ) * M 0 1 * (y : ℝ) +
            (y : ℝ) * M 1 0 * (x : ℝ) + (y : ℝ) * M 1 1 * (y : ℝ))| ≤
          ε * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))
    (hPositive : (M + (periodMatrix m)⁻¹).PosDef)
    (hPrescribed : ∀ a b : ℤ,
      1 - (halfPeriod m * a ^ 2 + (m.val * a + b) ^ 2 + m.val * a) ≤
        h (1 - (4 * m.val ^ 2 + 4 * m.val - 2) * a - 2 * m.val * b,
          -2 * m.val * a - 2 * b)) :
    1 ≤ h (0, 0) := by
  let f : ℤ × ℤ → ℤ := fun z => h (z.1 + 2, z.2)
  have hfSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then f (x - 1, y) + f (x + 1, y)
        else f (x, y - 1) + f (x, y + 1)) ≤ 2 * f (x, y) := by
    intro x y
    have hSH := hSuperharmonic (x + 2) y
    have hParity : (x + 2 + y + 1) % 2 = (x + y + 1) % 2 := by omega
    rw [hParity] at hSH
    dsimp [f]
    simpa only [show x - 1 + 2 = x + 2 - 1 by omega,
      show x + 1 + 2 = x + 2 + 1 by omega] using hSH
  have hfLower : ∀ z : ℤ × ℤ, profile m z.1 z.2 ≤ f z := by
    rintro ⟨x, y⟩
    have hBound := negative_shift_comparison_of_quadratic_growth m h M hSuperharmonic
      hGrowth hPositive hPrescribed (x + 2) y
    simpa only [f, Prod.fst, Prod.snd, add_sub_cancel_right] using hBound
  have hOriginalFinite := finite_negative_gap_sublevels_of_quadratic_growth m h M hGrowth hPositive 0
  have hfFinite : {z : ℤ × ℤ | f z - profile m z.1 z.2 ≤ 0}.Finite := by
    apply (hOriginalFinite.image (fun w : ℤ × ℤ => (w.1 - 2, w.2))).subset
    intro z hz
    refine ⟨(z.1 + 2, z.2), ?_, ?_⟩
    · simpa only [Set.mem_setOf_eq, add_sub_cancel_right] using hz
    · apply Prod.ext
      · dsimp
        omega
      · rfl
  have hfActive := profile_strict_on_active_of_finite_sublevel m f hfSuperharmonic hfLower hfFinite
  have hBound := one_le_added_point_of_active_strict_comparison m f hfSuperharmonic hfLower hfActive
  simpa only [f, Prod.fst, Prod.snd, neg_add_cancel] using hBound

end FLattice.Auxiliary.PlusOddProfile
