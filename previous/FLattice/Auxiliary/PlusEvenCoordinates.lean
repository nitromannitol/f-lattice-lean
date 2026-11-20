import FLattice.Auxiliary.PlusEvenProfile

/-!
# Exact coordinates for the even-plus profile

These lemmas identify the global function with its affine extension at
every valid lifted representative. All translation indices are integers,
including negative ones.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

/-- Decoding a cell in the strip recovers both indices and its binary state. -/
theorem stripHeight_at_cell (m : Parameter) (r s : ℤ) (e v : Fin 2)
    (hs0 : 0 ≤ s) (hsm : s < m.val) :
    stripHeight m (2 * m.val * r + 2 * s + (v.val : ℤ)) e =
      representativeHeight e v r s := by
  have hm := parameter_pos m
  have hv := v.isLt
  have hFirst :
      (2 * m.val * r + 2 * s + (v.val : ℤ)) / (2 * m.val) = r ∧
      (2 * m.val * r + 2 * s + (v.val : ℤ)) % (2 * m.val) =
        2 * s + (v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : 0 < 2 * m.val)).mpr
    exact ⟨by ring, by omega, by omega⟩
  have hSecond : (2 * s + (v.val : ℤ)) / 2 = s ∧
      (2 * s + (v.val : ℤ)) % 2 = (v.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by ring, by omega, by omega⟩
  have hBit : binaryState (2 * s + (v.val : ℤ)) = v := by
    apply Fin.ext
    have hValue := binaryState_val (2 * s + (v.val : ℤ))
    omega
  simp only [stripHeight, hFirst.1, hFirst.2, hSecond.1, hBit]

/-- The outer Euclidean reduction is exactly the displayed affine formula. -/
theorem profile_of_reduction (m : Parameter) (x y k q X : ℤ) (e : Fin 2)
    (hy : y = 2 * k + (e.val : ℤ))
    (hx : x - 2 * m.val * k = X + 2 * halfPeriod m * q)
    (hX0 : 0 ≤ X) (hXlt : X < 2 * halfPeriod m) :
    profile m x y = stripHeight m X e - q * X + q * m.val * (e.val : ℤ)
      - halfPeriod m * q ^ 2 - k * (e.val : ℤ) - k ^ 2 - k := by
  have he := e.isLt
  have hRow : y / 2 = k ∧ y % 2 = (e.val : ℤ) := by
    apply (Int.ediv_emod_unique (by omega : (0 : ℤ) < 2)).mpr
    exact ⟨by omega, by omega, by omega⟩
  have hCol : (x - 2 * m.val * k) / (2 * halfPeriod m) = q ∧
      (x - 2 * m.val * k) % (2 * halfPeriod m) = X := by
    apply (Int.ediv_emod_unique (by have := halfPeriod_pos m; omega)).mpr
    exact ⟨by omega, hX0, hXlt⟩
  have hBit : binaryState y = e := by
    apply Fin.ext
    have hValue := binaryState_val y
    omega
  simp only [profile, hRow.1, hRow.2, hCol.1, hCol.2, hBit]

/-- Every displayed representative has its horizontal coordinate in the strip. -/
theorem cell_coordinate_bounds (m : Parameter) (r s : ℤ) (v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    0 ≤ 2 * m.val * r + 2 * s + (v.val : ℤ) ∧
      2 * m.val * r + 2 * s + (v.val : ℤ) < 2 * halfPeriod m := by
  have hm := m.property
  have hv := v.isLt
  have hProd := mul_nonneg (by omega : 0 ≤ m.val) hr0
  constructor
  · nlinarith
  · unfold halfPeriod
    by_cases hr : r = m.val + 1
    · have hs : s ≤ m.val - 2 := by omega
      rw [hr]
      nlinarith
    · have hr' : r ≤ m.val := by omega
      have hProduct := mul_le_mul_of_nonneg_left hr' (by omega : 0 ≤ m.val)
      nlinarith

/-- The affine extension agrees with the literal global function at every
valid representative and every signed pair of translation indices. -/
theorem profile_at_lifted_cell (m : Parameter) (r s k q : ℤ) (e v : Fin 2)
    (hr0 : 0 ≤ r) (hrm : r ≤ m.val + 1)
    (hs0 : 0 ≤ s) (hsm : s < m.val)
    (hMissing : ¬(r = m.val + 1 ∧ s = m.val - 1)) :
    profile m (2 * m.val * r + 2 * s + (v.val : ℤ) +
        2 * m.val * k + 2 * halfPeriod m * q) (2 * k + (e.val : ℤ)) =
      representativeHeight e v r s - q * (2 * m.val * r + 2 * s + (v.val : ℤ))
        + q * m.val * (e.val : ℤ) - halfPeriod m * q ^ 2
        - k * (e.val : ℤ) - k ^ 2 - k := by
  obtain ⟨hX0, hXlt⟩ := cell_coordinate_bounds m r s v hr0 hrm hs0 hsm hMissing
  rw [profile_of_reduction m _ _ k q
    (2 * m.val * r + 2 * s + (v.val : ℤ)) e rfl (by ring) hX0 hXlt]
  rw [stripHeight_at_cell m r s e v hs0 hsm]

/-- Conversely, Euclidean decoding of a strip coordinate always yields a
valid cell, including the truncated final row. -/
theorem canonical_cell_bounds (m : Parameter) (X : ℤ)
    (hX0 : 0 ≤ X) (hXlt : X < 2 * halfPeriod m) :
    0 ≤ X / (2 * m.val) ∧ X / (2 * m.val) ≤ m.val + 1 ∧
    0 ≤ (X % (2 * m.val)) / 2 ∧ (X % (2 * m.val)) / 2 < m.val ∧
    ¬(X / (2 * m.val) = m.val + 1 ∧
      (X % (2 * m.val)) / 2 = m.val - 1) := by
  have hm := m.property
  have h2m : 0 < 2 * m.val := by omega
  have hj0 := Int.emod_nonneg X (ne_of_gt h2m)
  have hjlt := Int.emod_lt_of_pos X h2m
  have hr0 := Int.ediv_nonneg hX0 (le_of_lt h2m)
  have hDecode := Int.emod_add_mul_ediv X (2 * m.val)
  have hInner := Int.emod_add_mul_ediv (X % (2 * m.val)) 2
  have hBit0 := Int.emod_nonneg (X % (2 * m.val)) (by omega : (2 : ℤ) ≠ 0)
  have hBitLt := Int.emod_lt_of_pos (X % (2 * m.val)) (by omega : (0 : ℤ) < 2)
  have hrm : X / (2 * m.val) ≤ m.val + 1 := by
    by_contra h
    have hrLarge : m.val + 2 ≤ X / (2 * m.val) := by omega
    have hProduct := mul_le_mul_of_nonneg_left hrLarge (le_of_lt h2m)
    unfold halfPeriod at hXlt
    nlinarith
  refine ⟨hr0, hrm, by omega, by omega, ?_⟩
  rintro ⟨hr, hs⟩
  rw [hr] at hDecode
  rw [hs] at hInner
  unfold halfPeriod at hXlt
  nlinarith

/-- Every physical lattice point has a valid representative and signed
translation indices. No positivity restriction is placed on `x` or `y`. -/
theorem exists_valid_lifted_cell (m : Parameter) (x y : ℤ) :
    ∃ r s k q : ℤ, ∃ e v : Fin 2,
      0 ≤ r ∧ r ≤ m.val + 1 ∧ 0 ≤ s ∧ s < m.val ∧
      ¬(r = m.val + 1 ∧ s = m.val - 1) ∧
      x = 2 * m.val * r + 2 * s + (v.val : ℤ) +
        2 * m.val * k + 2 * halfPeriod m * q ∧
      y = 2 * k + (e.val : ℤ) := by
  let k := y / 2
  let q := (x - 2 * m.val * k) / (2 * halfPeriod m)
  let X := (x - 2 * m.val * k) % (2 * halfPeriod m)
  have hPeriod : 0 < 2 * halfPeriod m := by
    have := halfPeriod_pos m
    omega
  have hX0 : 0 ≤ X := Int.emod_nonneg _ (ne_of_gt hPeriod)
  have hXlt : X < 2 * halfPeriod m := Int.emod_lt_of_pos _ hPeriod
  obtain ⟨hr0, hrm, hs0, hsm, hMissing⟩ := canonical_cell_bounds m X hX0 hXlt
  refine ⟨X / (2 * m.val), (X % (2 * m.val)) / 2, k, q,
    binaryState y, binaryState (X % (2 * m.val)),
    hr0, hrm, hs0, hsm, hMissing, ?_, ?_⟩
  · rw [binaryState_val]
    have hOuter : X + 2 * halfPeriod m * q = x - 2 * m.val * k :=
      Int.emod_add_mul_ediv _ _
    have hCell := Int.emod_add_mul_ediv X (2 * m.val)
    have hInner := Int.emod_add_mul_ediv (X % (2 * m.val)) 2
    omega
  · rw [binaryState_val]
    have hRow := Int.emod_add_mul_ediv y 2
    change y = 2 * (y / 2) + y % 2
    omega

end FLattice.Auxiliary.PlusEvenProfile
