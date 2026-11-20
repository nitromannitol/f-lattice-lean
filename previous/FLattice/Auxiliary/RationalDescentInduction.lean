import FLattice.Auxiliary.RationalDescentEuclidean

/-!
# A universal arithmetic induction along the source descent

The theorem is about any predicate on primitive pairs. Its closure premises
are exactly the two endpoints, normalized upper-half duality and the actual
plus/minus branches. No matrix or graph conclusion is assumed or defined.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.RationalDescent

/-- Integer encoding of the source lexicographic order (Q, upper-half flag). -/
def measure (p : Pair) : ℕ := 2*primary p+secondary p

theorem secondary_le_one (p : Pair) : secondary p ≤ 1 := by
  unfold secondary
  split <;> omega

/-- Strict primary descent implies strict decrease of the encoded measure. -/
theorem measure_lt_of_primary_lt (p q : Pair) (h : primary p < primary q) :
    measure p < measure q := by
  have hp := secondary_le_one p
  unfold measure
  omega

/-- The exact upper-half dual strictly decreases the encoded lex measure. -/
theorem dual_measure_lt (p : Pair) (hHigh : p.d < 2*p.n) : measure (dual p) < measure p := by
  have hS := dual_secondary_lt p hHigh
  unfold measure
  rw [dual_primary]
  omega

/-- Exact Euclidean descent also decreases the encoded lex measure. -/
theorem parent_measure_lt (p : Pair) (hn : 1 < p.n) (hLow : 2*p.n < p.d) :
    measure (euclideanParent p hn) < measure p :=
  measure_lt_of_primary_lt _ _ (parent_primary_lt p hn hLow)

/-- The two endpoint and three descent closures suffice for every primitive
rational pair. All parity, gcd and termination facts are derived internally. -/
theorem induction
    (P : Pair → Prop)
    (hZero : ∀ p : Pair, p.n=0 → P p)
    (hOne : ∀ p : Pair, p.n=p.d → P p)
    (hDual : ∀ p : Pair, p.d<2*p.n → P (dual p) → P p)
    (hPlus : ∀ (child parent : Pair) (k : ℕ), 2≤k → k%2=0 →
      child.n=parent.d → child.d=k*parent.d+parent.n → P parent → P child)
    (hMinus : ∀ (child parent : Pair) (k : ℕ), 4≤k → k%2=0 →
      0<parent.n → parent.n<parent.d → child.n=parent.d →
      child.d=k*parent.d-parent.n → P parent → P child) : ∀ p : Pair, P p := by
  have hAll : ∀ q : ℕ, ∀ p : Pair, measure p=q → P p := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p hp
      have hStep : ∀ r : Pair, measure r < measure p → P r := by
        intro r hr
        exact ih (measure r) (by omega) r rfl
      by_cases hZeroN : p.n=0
      · exact hZero p hZeroN
      by_cases hOneN : p.n=p.d
      · exact hOne p hOneN
      by_cases hReciprocal : p.n=1
      · have hd : 2≤p.d := by have h := p.n_le_d; omega
        by_cases hEven : p.d%2=0
        · let e0 : Pair := ⟨0,1,by decide,by decide,by decide⟩
          apply hPlus p e0 p.d hd hEven
          · exact hReciprocal
          · simp [e0]
          · exact hZero e0 rfl
        · let e1 : Pair := ⟨1,1,by decide,by decide,by decide⟩
          apply hPlus p e1 (p.d-1) (by omega) (by omega)
          · exact hReciprocal
          · simp only [e1, mul_one]; omega
          · exact hOne e1 rfl
      have hn : 1<p.n := by omega
      by_cases hHigh : p.d<2*p.n
      · exact hDual p hHigh (hStep (dual p) (dual_measure_lt p hHigh))
      have hLow : 2*p.n<p.d := by
        by_contra h
        have hHalf : p.d=2*p.n := by omega
        have hOne := (half_endpoint p hHalf).1
        omega
      let parent := euclideanParent p hn
      have hParent : P parent := hStep parent (parent_measure_lt p hn hLow)
      by_cases hEven : quotient p%2=0
      · exact hPlus p parent (coefficient p) (plus_coefficient_range p hn hLow hEven)
          (coefficient_even p) rfl (plus_child_identity p hn hEven) hParent
      · exact hMinus p parent (coefficient p) (minus_coefficient_range p hn hLow hEven)
          (coefficient_even p) (parentNumerator_bounds p hn).1
          (parentNumerator_bounds p hn).2 rfl (minus_child_identity p hn hEven) hParent
  intro p
  exact hAll (measure p) p rfl

end FLattice.Auxiliary.RationalDescent
