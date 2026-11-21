import FLatticePaper.Graph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Int

namespace FLatticePaper.GeneralK

private def integerPrimitive (f : ℤ → ℤ) : ℤ → ℤ
  | .ofNat n => ∑ i ∈ Finset.range n, f (i : ℤ)
  | .negSucc n => -(∑ i ∈ Finset.range (n + 1), f (-((i : ℤ) + 1)))

@[simp] private theorem integerPrimitive_zero (f : ℤ → ℤ) : integerPrimitive f 0 = 0 := by
  simp [integerPrimitive]

private theorem integerPrimitive_succ (f : ℤ → ℤ) (index : ℤ) :
    integerPrimitive f (index + 1) - integerPrimitive f index = f index := by
  cases index with
  | ofNat n =>
    change integerPrimitive f (Int.ofNat (n + 1)) - integerPrimitive f (Int.ofNat n) = f (n : ℤ)
    simp [integerPrimitive, Finset.sum_range_succ]
  | negSucc n =>
    cases n with
    | zero =>
      change integerPrimitive f (Int.ofNat 0) - integerPrimitive f (Int.negSucc 0) = f (Int.negSucc 0)
      simp [integerPrimitive]
    | succ n =>
      rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega]
      simp only [integerPrimitive, Finset.sum_range_succ (n := n + 1), sub_neg_eq_add]
      rw [show -(((n + 1 : ℕ) : ℤ) + 1) = Int.negSucc (n + 1) by omega]
      omega

private theorem eq_of_eq_next {α : Type*} (f : ℤ → α) (h : ∀ i, f (i + 1) = f i) (i j : ℤ) : f i = f j := by
  refine Int.inductionOn' i j rfl ?_ ?_
  · intro n _ ih
    exact (h n).trans ih
  · intro n _ ih
    have hh := h (n - 1)
    rw [sub_add_cancel] at hh
    exact hh.symm.trans ih

private theorem integerPrimitive_sub {f g target : ℤ → ℤ} (h : ∀ n, f n - g n = target (n + 1) - target n)
    (n : ℤ) : integerPrimitive f n - integerPrimitive g n = target n - target 0 := by
  let ref (i : ℤ) := integerPrimitive f i - integerPrimitive g i - target i
  have hper (i : ℤ) : ref (i + 1) = ref i := by
    dsimp only [ref]
    have hf := integerPrimitive_succ f i
    have hg := integerPrimitive_succ g i
    have ht := h i
    omega
  have hh := eq_of_eq_next ref hper n 0
  simp only [ref, integerPrimitive_zero] at hh
  omega

/-- The integer potential of a curl-free field on lattice edges, with its
origin fixed at zero. -/
def axisPotential (horizontal vertical : ℤ → ℤ → ℤ) (site : Site) : ℤ :=
  integerPrimitive (fun x => horizontal x 0) site.1 + integerPrimitive (vertical site.1) site.2

theorem axisPotential_add_vertical (horizontal vertical : ℤ → ℤ → ℤ) (x y : ℤ) :
    axisPotential horizontal vertical (x, y + 1) - axisPotential horizontal vertical (x, y) = vertical x y := by
  simp only [axisPotential]
  have h := integerPrimitive_succ (vertical x) y
  omega

theorem axisPotential_add_horizontal {horizontal vertical : ℤ → ℤ → ℤ}
    (hcurl : ∀ x y, vertical (x + 1) y - vertical x y = horizontal x (y + 1) - horizontal x y) (x y : ℤ) :
    axisPotential horizontal vertical (x + 1, y) - axisPotential horizontal vertical (x, y) = horizontal x y := by
  have h := integerPrimitive_sub (hcurl x) y
  have h' := integerPrimitive_succ (fun i => horizontal i 0) x
  simp only [axisPotential]
  omega

/-- A translation preserving both edge arrays changes their potential by
one constant. -/
theorem axisPotential_shift {horizontal vertical : ℤ → ℤ → ℤ}
    (hcurl : ∀ x y, vertical (x + 1) y - vertical x y = horizontal x (y + 1) - horizontal x y)
    (step : Site) (hh : ∀ x y, horizontal (x + step.1) (y + step.2) = horizontal x y)
    (hv : ∀ x y, vertical (x + step.1) (y + step.2) = vertical x y) (site : Site) :
    axisPotential horizontal vertical (site + step) - axisPotential horizontal vertical site =
      axisPotential horizontal vertical step := by
  let difference (x y : ℤ) := axisPotential horizontal vertical ((x, y) + step) - axisPotential horizontal vertical (x, y)
  have hhorizontal (x y : ℤ) : difference (x + 1) y = difference x y := by
    have h₁ := axisPotential_add_horizontal hcurl x y
    have h₂ := axisPotential_add_horizontal hcurl (x + step.1) (y + step.2)
    rw [hh] at h₂
    change axisPotential horizontal vertical (x + 1 + step.1, y + step.2) - axisPotential horizontal vertical (x + 1, y) =
      axisPotential horizontal vertical (x + step.1, y + step.2) - axisPotential horizontal vertical (x, y)
    rw [add_right_comm x 1 step.1]
    omega
  have hvertical (x y : ℤ) : difference x (y + 1) = difference x y := by
    have h₁ := axisPotential_add_vertical horizontal vertical x y
    have h₂ := axisPotential_add_vertical horizontal vertical (x + step.1) (y + step.2)
    rw [hv] at h₂
    change axisPotential horizontal vertical (x + step.1, y + 1 + step.2) - axisPotential horizontal vertical (x, y + 1) =
      axisPotential horizontal vertical (x + step.1, y + step.2) - axisPotential horizontal vertical (x, y)
    rw [add_right_comm y 1 step.2]
    omega
  obtain ⟨x, y⟩ := site
  change difference x y = _
  rw [eq_of_eq_next (fun i => difference i y) (fun i => hhorizontal i y) x 0,
    eq_of_eq_next (difference 0) (hvertical 0) y 0]
  simp [difference, axisPotential]

theorem axisPotential_nat_horizontal (horizontal vertical : ℤ → ℤ → ℤ) (n : ℕ) :
    axisPotential horizontal vertical (n, 0) = ∑ i ∈ Finset.range n, horizontal (i : ℤ) 0 := by
  simp [axisPotential, integerPrimitive]

theorem axisPotential_nat_vertical (horizontal vertical : ℤ → ℤ → ℤ) (n : ℕ) :
    axisPotential horizontal vertical (0, n) = ∑ i ∈ Finset.range n, vertical 0 (i : ℤ) := by
  simp [axisPotential, integerPrimitive]

end FLatticePaper.GeneralK
