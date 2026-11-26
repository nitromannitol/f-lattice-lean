import FLatticePaper.Plane.Induction.WeightChange

/-! # The rank is bounded above on the zero set of a sheet difference

Let `F` have increments `p` along the deck vector `U` and `q` along `V`, and let `R` have increments `p'`, `q'` along the same
two vectors, with the two linear forms proportional (`p' q = q' p`) and `(p, q) ≠ 0`. Then `R` is bounded above on the zero set
of `F`.

Proof. The sites are covered by a finite box `S` of representatives (`exists_deck_box`), so a zero `z = r + i U + j V` has
`i p + j q = −F r`, which is bounded by `max_S |F|`. Proportionality gives `p · (i p' + j q') = p' · (i p + j q)` (and the same with `q`),
so the linear part of `R` is bounded by `(|p'| + |q'|)` times that bound. -/

namespace FLatticePaper.TieRankBound

open FLatticePaper FLatticePaper.WeightChange

/-- The two linear forms are proportional: `p` and `q` times the form of `R` are the multiples of the form of `F`. -/
theorem linear_proportional (p q p' q' i j : ℤ) (hc : p' * q = q' * p) :
    p * (i * p' + j * q') = p' * (i * p + j * q) ∧ q * (i * p' + j * q') = q' * (i * p + j * q) := by
  constructor
  · linear_combination (-j) * hc
  · linear_combination i * hc

/-- **The linear part is bounded.** If the forms are proportional, `(p, q) ≠ 0`, and the `F`-form is bounded by `M`, then the
`R`-form is bounded by `(|p'| + |q'|) M`. -/
theorem linear_bound (p q p' q' i j M : ℤ) (hc : p' * q = q' * p) (hpq : p ≠ 0 ∨ q ≠ 0)
    (hM : |i * p + j * q| ≤ M) : i * p' + j * q' ≤ (|p'| + |q'|) * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hM
  have hp' : 0 ≤ |p'| := abs_nonneg _
  have hq' : 0 ≤ |q'| := abs_nonneg _
  obtain ⟨e1, e2⟩ := linear_proportional p q p' q' i j hc
  have hR : |i * p' + j * q'| ≤ (|p'| + |q'|) * M := by
    rcases hpq with hp | hq
    · have h1 := congrArg abs e1
      rw [abs_mul, abs_mul] at h1
      have hpabs : 1 ≤ |p| := Int.one_le_abs hp
      have hR0 : 0 ≤ |i * p' + j * q'| := abs_nonneg _
      have h2 : |p'| * |i * p + j * q| ≤ |p'| * M := mul_le_mul_of_nonneg_left hM hp'
      have h3 : |i * p' + j * q'| ≤ |p| * |i * p' + j * q'| := by nlinarith
      have h4 : |p| * |i * p' + j * q'| ≤ |p'| * M := by rw [h1]; exact h2
      nlinarith [mul_nonneg hq' hM0]
    · have h1 := congrArg abs e2
      rw [abs_mul, abs_mul] at h1
      have hqabs : 1 ≤ |q| := Int.one_le_abs hq
      have hR0 : 0 ≤ |i * p' + j * q'| := abs_nonneg _
      have h2 : |q'| * |i * p + j * q| ≤ |q'| * M := mul_le_mul_of_nonneg_left hM hq'
      have h3 : |i * p' + j * q'| ≤ |q| * |i * p' + j * q'| := by nlinarith
      have h4 : |q| * |i * p' + j * q'| ≤ |q'| * M := by rw [h1]; exact h2
      nlinarith [mul_nonneg hp' hM0]
  exact le_trans (le_abs_self _) hR

/-- **The rank is bounded above on the zero set.** If `F` and `R` have increments `(p, q)` and `(p', q')` along the deck basis
`U, V` (with `det ≠ 0`), the forms are proportional and `(p, q) ≠ 0`, then `R` is bounded above on `{z | F z = 0}`. -/
theorem rank_bounded_on_zero {U V : Site} (hD : U.1 * V.2 - U.2 * V.1 ≠ 0) {F R : Site → ℤ} {p q p' q' : ℤ}
    (hFU : ∀ z, F (z + U) = F z + p) (hFV : ∀ z, F (z + V) = F z + q)
    (hRU : ∀ z, R (z + U) = R z + p') (hRV : ∀ z, R (z + V) = R z + q')
    (hc : p' * q = q' * p) (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ B : ℤ, ∀ z, F z = 0 → R z ≤ B := by
  obtain ⟨S, hS⟩ := exists_deck_box U V hD
  refine ⟨(∑ r ∈ S, |R r|) + (|p'| + |q'|) * (∑ r ∈ S, |F r|), fun z hz => ?_⟩
  obtain ⟨r, hr, i, j, rfl⟩ := hS z
  have hFz := affine_lattice hFU hFV r i j
  have hRz := affine_lattice hRU hRV r i j
  have hM : |i * p + j * q| ≤ ∑ s ∈ S, |F s| := by
    have hlin : i * p + j * q = -F r := by
      rw [hFz] at hz
      linarith
    rw [hlin, abs_neg]
    exact Finset.single_le_sum (f := fun s => |F s|) (fun s _ => abs_nonneg _) hr
  have hb := linear_bound p q p' q' i j (∑ s ∈ S, |F s|) hc hpq hM
  have hN : |R r| ≤ ∑ s ∈ S, |R s| :=
    Finset.single_le_sum (f := fun s => |R s|) (fun s _ => abs_nonneg _) hr
  rw [hRz]
  have := le_abs_self (R r)
  linarith

end FLatticePaper.TieRankBound
