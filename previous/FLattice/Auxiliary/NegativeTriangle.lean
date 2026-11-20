import FLattice.Auxiliary.FiniteComparison
import FLattice.Auxiliary.DirectionalRank
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A finite negative-branch triangle with a global parabola

This conditional lattice comparison uses only literal superharmonicity and
explicit values on the triangle and its incoming collar. The baseline is
global: horizontal deficit zero and vertical deficit one. Boundary inputs
already at gap two replace the adjusted finite-patch baseline.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.NegativeTriangle

open DirectionalRank

/-- The global integer parabola used throughout the triangle and collar. -/
def baseline (y : ℤ) : ℤ := -(y * (y - 1) / 2) - 1

/-- The finite triangular region, with its literal physical coordinates. -/
def region (m : ℤ) : Set (ℤ × ℤ) :=
  {z | 1 ≤ z.1 ∧ z.1 ≤ 2 * m - 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 + z.2 ≤ 2 * m + 1}

private theorem twice_baseline (y : ℤ) :
    2 * baseline y = -y * (y - 1) - 2 := by
  have hEven : (y * (y - 1)) % 2 = 0 := by
    rcases (show y % 2 = 0 ∨ y % 2 = 1 by omega) with h | h
    · rw [Int.mul_emod, h]
      norm_num
    · have hPrevious : (y - 1) % 2 = 0 := by omega
      rw [Int.mul_emod, hPrevious]
      norm_num
  have hDiv := Int.emod_add_mul_ediv (y * (y - 1)) 2
  rw [hEven] at hDiv
  unfold baseline
  nlinarith

/-- The global parabola has vertical deficit exactly one at every signed height. -/
theorem baseline_vertical_sum (y : ℤ) :
    baseline (y - 1) + baseline (y + 1) = 2 * baseline y - 1 := by
  have hPrevious := twice_baseline (y - 1)
  have hCenter := twice_baseline y
  have hNext := twice_baseline (y + 1)
  nlinarith

private theorem region_finite (m : ℤ) : (region m).Finite := by
  let rectangle : Finset (ℤ × ℤ) :=
    (Finset.Icc 1 (2 * m - 1)).product (Finset.Icc 0 (2 * m - 1))
  apply rectangle.finite_toSet.subset
  intro z hz
  obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hz
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hx0, hxm⟩, Finset.mem_Icc.mpr ⟨hy0, by omega⟩⟩

private theorem horizontal_left (m x y : ℤ) (hz : (x, y) ∈ region m)
    (hEven : (x + y) % 2 = 0) :
    (x - 1, y) ∈ region m ∨ (y = x ∧ 0 ≤ x - 1 ∧ x - 1 ≤ m - 1) := by
  obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hz
  by_cases hmem : (x - 1, y) ∈ region m
  · exact Or.inl hmem
  · right
    change ¬(1 ≤ x - 1 ∧ x - 1 ≤ 2 * m - 1 ∧ 0 ≤ y ∧
      y ≤ x - 1 ∧ x - 1 + y ≤ 2 * m + 1) at hmem
    exact ⟨by omega, by omega, by omega⟩

private theorem horizontal_right (m x y : ℤ) (hz : (x, y) ∈ region m)
    (hEven : (x + y) % 2 = 0) :
    (x + 1, y) ∈ region m ∨ (x = 2 * m - 1 ∧ y = 1) := by
  obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hz
  by_cases hmem : (x + 1, y) ∈ region m
  · exact Or.inl hmem
  · right
    change ¬(1 ≤ x + 1 ∧ x + 1 ≤ 2 * m - 1 ∧ 0 ≤ y ∧
      y ≤ x + 1 ∧ x + 1 + y ≤ 2 * m + 1) at hmem
    exact ⟨by omega, by omega⟩

private theorem vertical_down (m x y : ℤ) (hz : (x, y) ∈ region m) :
    (x, y - 1) ∈ region m ∨ y = 0 := by
  obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hz
  by_cases hmem : (x, y - 1) ∈ region m
  · exact Or.inl hmem
  · right
    change ¬(1 ≤ x ∧ x ≤ 2 * m - 1 ∧ 0 ≤ y - 1 ∧
      y - 1 ≤ x ∧ x + (y - 1) ≤ 2 * m + 1) at hmem
    omega

private theorem vertical_up (m x y : ℤ) (hz : (x, y) ∈ region m)
    (hOdd : (x + y) % 2 = 1) :
    (x, y + 1) ∈ region m ∨ (m + 1 ≤ x ∧ y + 1 = 2 * m + 2 - x) := by
  obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hz
  by_cases hmem : (x, y + 1) ∈ region m
  · exact Or.inl hmem
  · right
    change ¬(1 ≤ x ∧ x ≤ 2 * m - 1 ∧ 0 ≤ y + 1 ∧
      y + 1 ≤ x ∧ x + (y + 1) ≤ 2 * m + 1) at hmem
    exact ⟨by omega, by omega⟩

/-- The explicit collar bounds raise the entire triangle to gap two and force
value at least one at the origin. No growth or periodicity of h is assumed. -/
theorem triangle_and_origin_lower_bound (m : ℤ) (hm : 2 ≤ m)
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hTriangle : ∀ x y : ℤ, (x, y) ∈ region m → baseline y + 1 ≤ h (x, y))
    (hLeft : ∀ i : ℤ, 0 ≤ i → i ≤ m - 1 → baseline (i + 1) + 1 ≤ h (i, i + 1))
    (hRight : ∀ i : ℤ, m + 1 ≤ i → i ≤ 2 * m - 1 →
      baseline (2 * m + 2 - i) + 2 ≤ h (i, 2 * m + 2 - i))
    (hBottom : ∀ i : ℤ, 1 ≤ i → i ≤ 2 * m - 1 → i % 2 = 1 → 0 ≤ h (i, -1))
    (hSource : 1 ≤ h (2 * m, 1)) (hOriginLeft : 0 ≤ h (-1, 0)) :
    (∀ z ∈ region m, baseline z.2 + 2 ≤ h z) ∧ 1 ≤ h (0, 0) := by
  let bad : Set (ℤ × ℤ) := {z | z ∈ region m ∧ h z - baseline z.2 = 1}
  have hFinite : bad.Finite := (region_finite m).subset (fun _ hz => hz.1)
  have hNoBad : ¬bad.Nonempty := by
    apply not_nonempty_of_finite_rank_descent bad (fun z => rightRank z.1 z.2) hFinite
    rintro ⟨x, y⟩ ⟨hz, hgap⟩
    dsimp only at hgap
    have hb : 1 ≤ x ∧ x ≤ 2 * m - 1 ∧ 0 ≤ y ∧ y ≤ x ∧ x + y ≤ 2 * m + 1 := hz
    obtain ⟨hx0, hxm, hy0, hyx, hsum⟩ := hb
    have hStar := hSuperharmonic x y
    by_cases hEven : (x + y) % 2 = 0
    · rw [if_pos hEven] at hStar
      have hLeftLower : baseline y + 1 ≤ h (x - 1, y) := by
        rcases horizontal_left m x y hz hEven with hmem | ⟨hy, hi0, him⟩
        · exact hTriangle (x - 1) y hmem
        · have hb := hLeft (x - 1) hi0 him
          simpa only [show x - 1 + 1 = y by omega] using hb
      rcases horizontal_right m x y hz hEven with hmem | ⟨hx, hy⟩
      · have hRightLower := hTriangle (x + 1) y hmem
        refine ⟨(x + 1, y), ⟨hmem, by dsimp only; omega⟩, ?_⟩
        dsimp only
        have hRank := rightRank_right_of_even x y hEven
        omega
      · have hRightLower : baseline y + 2 ≤ h (x + 1, y) := by
          simpa [hx, hy, baseline] using hSource
        omega
    · rw [if_neg hEven] at hStar
      have hOdd : (x + y) % 2 = 1 := by omega
      have hDown : (x, y - 1) ∈ region m ∨ baseline (y - 1) + 2 ≤ h (x, y - 1) := by
        rcases vertical_down m x y hz with hmem | hy
        · exact Or.inl hmem
        · right
          have hb := hBottom x hx0 hxm (by omega)
          simpa [hy, baseline] using hb
      have hUp : (x, y + 1) ∈ region m ∨ baseline (y + 1) + 2 ≤ h (x, y + 1) := by
        rcases vertical_up m x y hz hOdd with hmem | ⟨hxm', hy⟩
        · exact Or.inl hmem
        · right
          simpa only [hy] using hRight x hxm' hxm
      have hDownLower : baseline (y - 1) + 1 ≤ h (x, y - 1) := by
        rcases hDown with hmem | hb
        · exact hTriangle x (y - 1) hmem
        · omega
      have hUpLower : baseline (y + 1) + 1 ≤ h (x, y + 1) := by
        rcases hUp with hmem | hb
        · exact hTriangle x (y + 1) hmem
        · omega
      have hBase := baseline_vertical_sum y
      have hContact : h (x, y - 1) - baseline (y - 1) = 1 ∨
          h (x, y + 1) - baseline (y + 1) = 1 := by omega
      have hRanks := rightRank_vertical_of_odd x y hOdd
      rcases hContact with hd | hu
      · have hmem : (x, y - 1) ∈ region m := by
          rcases hDown with hmem | hb
          · exact hmem
          · omega
        exact ⟨(x, y - 1), ⟨hmem, hd⟩, by dsimp only; omega⟩
      · have hmem : (x, y + 1) ∈ region m := by
          rcases hUp with hmem | hb
          · exact hmem
          · omega
        exact ⟨(x, y + 1), ⟨hmem, hu⟩, by dsimp only; omega⟩
  have hTwo : ∀ z ∈ region m, baseline z.2 + 2 ≤ h z := by
    rintro ⟨x, y⟩ hz
    dsimp only
    have hOne := hTriangle x y hz
    by_contra hFailure
    exact hNoBad ⟨(x, y), hz, by dsimp only; omega⟩
  refine ⟨hTwo, ?_⟩
  have hAtOne := hTwo (1, 0) (by change 1 ≤ 1 ∧ 1 ≤ 2 * m - 1 ∧ 0 ≤ 0 ∧ 0 ≤ 1 ∧ 1 + 0 ≤ 2 * m + 1; omega)
  have hOrigin := hSuperharmonic 0 0
  norm_num [baseline] at hAtOne hOrigin
  omega

end FLattice.Auxiliary.NegativeTriangle
