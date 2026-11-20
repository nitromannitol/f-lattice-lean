import FLattice.Auxiliary.StagedLowerComparison

/-!
# Incoming rank selections rule out a proper integer gap

At every vertex, more incoming slots than the allowed deficit decrease
a rank. Such a gap cannot have every sublevel finite. This is the finite
minimum principle used to exclude strict quadratic dominators. It applies
to variable directed degrees, with incoming multiplicities retained.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FLattice.Auxiliary

/-- A proper integer gap cannot satisfy the incoming deficit inequality
when enough incoming slots strictly lower a rank at every vertex. -/
theorem not_proper_gap_of_ranked_incoming
    {V α : Type*} [LinearOrder α]
    (degree : V → ℕ) (incoming : (x : V) → Fin (degree x) → V)
    (gap : V → ℤ) (deficit : V → ℕ) (rank : V → α) (x₀ : V)
    (hSum : ∀ x, (∑ i : Fin (degree x), gap (incoming x i)) ≤
      (degree x : ℤ) * gap x + (deficit x : ℤ))
    (hSelected : ∀ x, ∃ S : Finset (Fin (degree x)), deficit x < S.card ∧
      ∀ i ∈ S, rank (incoming x i) < rank x)
    (hFinite : ∀ t : ℤ, {x | gap x ≤ t}.Finite) : False := by
  let b := gap x₀ + 1
  have hShifted : ∀ x, 0 ≤ gap x - b := by
    apply zero_le_gap_of_staged_incoming degree incoming (fun x => gap x - b)
      deficit (fun _ => 0) rank ∅
    · intro x hx
      exact False.elim (Set.notMem_empty x hx)
    · intro x _
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have h := hSum x
      rw [mul_sub]
      omega
    · intro x _
      obtain ⟨S, hCount, hRank⟩ := hSelected x
      exact ⟨S, hCount, fun i hi => Or.inr (Or.inr ⟨rfl, hRank i hi⟩)⟩
    · apply (hFinite b).subset
      intro x hx
      change gap x - b < 0 at hx
      change gap x ≤ b
      omega
  have hAt := hShifted x₀
  dsimp [b] at hAt
  omega

end FLattice.Auxiliary
