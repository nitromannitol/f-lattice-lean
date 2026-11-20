import FLattice.Auxiliary.RationalDescentDual

/-! The actual signed Euclidean parent and strict decrease of Q. -/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalDescent

/-- Ordinary Euclidean quotient of the child denominator by its numerator. -/
def quotient (p : Pair) : ℕ := p.d / p.n

/-- Ordinary Euclidean remainder. -/
def remainder (p : Pair) : ℕ := p.d % p.n

/-- The source chooses plus for an even quotient and minus otherwise. -/
def parentNumerator (p : Pair) : ℕ :=
  if quotient p % 2 = 0 then remainder p else p.n - remainder p

/-- The even branch coefficient selected by the Euclidean algorithm. -/
def coefficient (p : Pair) : ℕ :=
  if quotient p % 2 = 0 then quotient p else quotient p + 1

theorem remainder_pos (p : Pair) (hn : 1 < p.n) : 0 < remainder p := by
  by_contra h
  have hZero : p.d % p.n = 0 := by change ¬ 0 < p.d % p.n at h; omega
  have hOne := p.coprime.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hZero)
  omega

theorem remainder_lt (p : Pair) (hn : 1 < p.n) : remainder p < p.n :=
  Nat.mod_lt _ (by omega)

theorem remainder_coprime (p : Pair) : Nat.Coprime (remainder p) p.n := by
  change Nat.gcd (p.d % p.n) p.n = 1
  rw [← Nat.gcd_rec]
  exact p.coprime.gcd_eq_one

theorem parentNumerator_bounds (p : Pair) (hn : 1 < p.n) :
    0 < parentNumerator p ∧ parentNumerator p < p.n := by
  have hs0 := remainder_pos p hn
  have hsn := remainder_lt p hn
  unfold parentNumerator
  split <;> omega

/-- The actual primitive, interior signed-Euclidean parent. -/
def euclideanParent (p : Pair) (hn : 1 < p.n) : Pair where
  n := parentNumerator p
  d := p.n
  d_pos := by omega
  n_le_d := Nat.le_of_lt (parentNumerator_bounds p hn).2
  coprime := by
    unfold parentNumerator
    split
    · exact remainder_coprime p
    · exact (Nat.coprime_self_sub_left (Nat.le_of_lt (remainder_lt p hn))).mpr (remainder_coprime p)

/-- The literal selected coefficient is even. -/
theorem coefficient_even (p : Pair) : coefficient p % 2 = 0 := by
  unfold coefficient
  split <;> omega

/-- The quotient is at least two on the source's low-ratio branch. -/
theorem quotient_two_le (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d) :
    2 ≤ quotient p := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  omega

/-- The plus coefficient meets its local-transport range. -/
theorem plus_coefficient_range (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d)
    (hEven : quotient p % 2 = 0) : 2 ≤ coefficient p := by
  simpa [coefficient, hEven] using quotient_two_le p hn hLow

/-- The minus coefficient meets its local-transport range. -/
theorem minus_coefficient_range (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d)
    (hOdd : quotient p % 2 ≠ 0) : 4 ≤ coefficient p := by
  have hq := quotient_two_le p hn hLow
  simp only [coefficient, if_neg hOdd]
  omega

/-- Exact plus reconstruction of the child. -/
theorem plus_child_identity (p : Pair) (hn : 1 < p.n) (hEven : quotient p % 2 = 0) :
    p.d = coefficient p * (euclideanParent p hn).d + (euclideanParent p hn).n := by
  simp only [euclideanParent, parentNumerator, coefficient, if_pos hEven]
  exact (Nat.div_add_mod' p.d p.n).symm

/-- Exact minus reconstruction of the child. -/
theorem minus_child_identity (p : Pair) (hn : 1 < p.n) (hOdd : quotient p % 2 ≠ 0) :
    p.d = coefficient p * (euclideanParent p hn).d - (euclideanParent p hn).n := by
  have hDiv := Nat.div_add_mod' p.d p.n
  have hs := remainder_lt p hn
  change quotient p * p.n + remainder p = p.d at hDiv
  simp only [euclideanParent, parentNumerator, coefficient, if_neg hOdd]
  have hSub : p.n - remainder p + remainder p = p.n := by omega
  have hSum : (quotient p + 1) * p.n = p.d + (p.n - remainder p) := by nlinarith
  omega

/-- The actual parent preserves the sum parity and therefore κ. -/
theorem parent_sum_mod_two (p : Pair) (hn : 1 < p.n) :
    ((euclideanParent p hn).n+(euclideanParent p hn).d)%2 = (p.n+p.d)%2 := by
  have hDiv := congrArg (fun z : ℕ => z % 2) (Nat.div_add_mod' p.d p.n)
  change (quotient p * p.n + remainder p)%2 = p.d%2 at hDiv
  have hs := remainder_lt p hn
  by_cases hEven : quotient p % 2 = 0
  · simp only [Nat.add_mod, Nat.mul_mod, hEven, zero_mul, Nat.mod_mod] at hDiv
    simp only [euclideanParent, parentNumerator, if_pos hEven]
    omega
  · have hOdd : quotient p % 2 = 1 := by omega
    simp only [Nat.add_mod, Nat.mul_mod, hOdd, one_mul, Nat.mod_mod] at hDiv
    simp only [euclideanParent, parentNumerator, if_neg hEven]
    omega

theorem parent_kappa (p : Pair) (hn : 1 < p.n) :
    kappa (euclideanParent p hn).n (euclideanParent p hn).d = kappa p.n p.d := by
  unfold kappa
  rw [parent_sum_mod_two]

private theorem sizePolynomial_lt_two_square (n d : ℕ) (h : n < d) :
    sizePolynomial n d < 2*d^2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hT := sizePolynomial_add_square n (n+s+1) (by omega)
  nlinarith only [hT]

private theorem two_square_lt_sizePolynomial (n d : ℕ) (h : 2*n < d) :
    2*n^2 < sizePolynomial n d := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hT := sizePolynomial_add_square n (2*n+s+1) (by omega)
  nlinarith only [hT]

/-- The two strict source bounds which force Euclidean progress. -/
theorem parent_size_bounds (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d) :
    sizePolynomial (euclideanParent p hn).n (euclideanParent p hn).d < 2*p.n^2 ∧
      2*p.n^2 < sizePolynomial p.n p.d := by
  exact ⟨sizePolynomial_lt_two_square _ _ (parentNumerator_bounds p hn).2,
    two_square_lt_sizePolynomial _ _ hLow⟩

/-- The literal primary coordinate strictly decreases on each low-ratio branch. -/
theorem parent_primary_lt (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d) :
    primary (euclideanParent p hn) < primary p := by
  have hT := lt_trans (parent_size_bounds p hn hLow).1 (parent_size_bounds p hn hLow).2
  unfold primary
  rw [parent_kappa]
  exact Nat.mul_lt_mul_of_pos_left hT (kappa_pos p.n p.d)

end FLattice.Auxiliary.RationalDescent
