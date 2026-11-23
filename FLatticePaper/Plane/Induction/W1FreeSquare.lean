import FLatticePaper.Plane.Induction.W1HagreeNonfree

/-! # Task 82: the free-root square lemma (the table of AUDIT_FREE_THREE_STEP_RETURNS §§2–3)

Every row of the audit's return table is a unit square `Q` containing the free white root `z`, whose other three corners form a
three-edge chain of retained edges ending at `z`: `p0 → p1 → p2 → z`, where `p0` is the rejected input of `z` and each step goes to an
input of the previous point. Up to translation the rows fall into seven SHAPES (lower-left corner of `Q`, chain, and parity of `z`).

Each shape lemma proves, from its three retained edges, the private square in the form of `OldPolicyWitness.privateSquare`: `z ∈ Q` and
every other corner of `Q` is `TransGen`-joined to `z` along retained edges `x → y` with `y` an input of `x`. The retained edges of a row are
the table's content and are the hypotheses of the shape lemma. The corners, the chain's edges, and the parities are proved here.

Table (rows of the audit, both signs; `z = (z1, z2)`, `E = (1,0)`, `N = (0,1)`):
* S1 (z odd, Q = ll(z), chain `z+N → z+E+N → z+E → z`): H-midpoint; H0; Hlast−U (eta minus); V-odd, eta minus, axial (else branch).
* S2 (z even, Q = ll(z), chain `z+E → z+E+N → z+N → z`): H-diagonal; Hpenultimate−U (eta plus); Vlast (both signs).
* S3 (z even, Q = ll(z−N), chain `z+E → z+E−N → z−N → z`): H-axial; Hpenultimate−U (eta minus); V0 (eta plus); V-midpoint, even, eta plus.
* S4 (z odd, Q = ll(z−N), chain `z−N → z+E−N → z+E → z`): Hlast−U (eta plus); V-odd, eta plus, diagonal (first branch).
* S5 (z even, Q = ll(z−E), chain `z−E → z−E+N → z+N → z`): V0 (eta minus); V-midpoint, even, eta minus.
* S6 (z odd, Q = ll(z−E), chain `z+N → z−E+N → z−E → z`): Vpenultimate−V (eta minus); V-odd, eta minus, diagonal (first branch).
* S7 (z odd, Q = ll(z−E−N), chain `z−N → z−E−N → z−E → z`): V1 (eta plus); V-odd, eta plus, axial (else branch).

The bulk rows (H-midpoint, H-diagonal, H-axial, V-midpoint, V-diagonal, V-axial) take their first bulk edge from the forward or reflected
fans (FIXED_FREE §§8-9, ALL_SLOPE_STEP), which w3 has not formalized. Their shape lemmas are proved for any retained chain; the fan facts are
the hypotheses at the call sites. -/

set_option linter.unusedSimpArgs false

namespace FLatticePaper.W1FreeSquare

open FLatticePaper FLatticePaper.AndOrRank

/-- **Transport of a three-edge return to the private square** (the form of `OldPolicyWitness.privateSquare`): the three non-root
corners of a unit square `Q ∋ z` form the chain `p0 → p1 → p2 → z` of retained edges, each step to an input of the previous point, and
every other corner of `Q` is one of `p0, p1, p2`. -/
theorem private_of_return {R : Site → Site → Prop} {z p0 p1 p2 : Site} {a b : ℤ}
    (hcov : ∀ c' ∈ squareCorners a b, c' ≠ z → c' = p0 ∨ c' = p1 ∨ c' = p2)
    (hR0 : R p0 p1) (hE1 : Edge p1 p0) (hR1 : R p1 p2) (hE2 : Edge p2 p1) (hR2 : R p2 z) (hE3 : Edge z p2) :
    ∀ c' ∈ squareCorners a b, c' ≠ z → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' z := by
  intro c' hc' hne
  rcases hcov c' hc' hne with rfl | rfl | rfl
  · exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single ⟨hR0, hE1⟩) ⟨hR1, hE2⟩) ⟨hR2, hE3⟩
  · exact Relation.TransGen.tail (Relation.TransGen.single ⟨hR1, hE2⟩) ⟨hR2, hE3⟩
  · exact Relation.TransGen.single ⟨hR2, hE3⟩

/-- **S1** (z odd, Q = ll(z)): the chain z+N → z+E+N → z+E → z. -/
theorem shape_S1 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hR0 : R (z1, z2 + 1) (z1 + 1, z2 + 1)) (hR1 : R (z1 + 1, z2 + 1) (z1 + 1, z2)) (hR2 : R (z1 + 1, z2) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1, z2, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S2** (z even, Q = ll(z)): the chain z+E → z+E+N → z+N → z. -/
theorem shape_S2 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hR0 : R (z1 + 1, z2) (z1 + 1, z2 + 1)) (hR1 : R (z1 + 1, z2 + 1) (z1, z2 + 1)) (hR2 : R (z1, z2 + 1) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1, z2, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S3** (z even, Q = ll(z−N)): the chain z+E → z+E−N → z−N → z. -/
theorem shape_S3 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hR0 : R (z1 + 1, z2) (z1 + 1, z2 - 1)) (hR1 : R (z1 + 1, z2 - 1) (z1, z2 - 1)) (hR2 : R (z1, z2 - 1) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1, z2 - 1, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S4** (z odd, Q = ll(z−N)): the chain z−N → z+E−N → z+E → z. -/
theorem shape_S4 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hR0 : R (z1, z2 - 1) (z1 + 1, z2 - 1)) (hR1 : R (z1 + 1, z2 - 1) (z1 + 1, z2)) (hR2 : R (z1 + 1, z2) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1, z2 - 1, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S5** (z even, Q = ll(z−E)): the chain z−E → z−E+N → z+N → z. -/
theorem shape_S5 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 0)
    (hR0 : R (z1 - 1, z2) (z1 - 1, z2 + 1)) (hR1 : R (z1 - 1, z2 + 1) (z1, z2 + 1)) (hR2 : R (z1, z2 + 1) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1 - 1, z2, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S6** (z odd, Q = ll(z−E)): the chain z+N → z−E+N → z−E → z. -/
theorem shape_S6 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hR0 : R (z1, z2 + 1) (z1 - 1, z2 + 1)) (hR1 : R (z1 - 1, z2 + 1) (z1 - 1, z2)) (hR2 : R (z1 - 1, z2) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1 - 1, z2, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega


/-- **S7** (z odd, Q = ll(z−E−N)): the chain z−N → z−E−N → z−E → z. -/
theorem shape_S7 {R : Site → Site → Prop} (z1 z2 : ℤ) (hz : (z1 + z2) % 2 = 1)
    (hR0 : R (z1, z2 - 1) (z1 - 1, z2 - 1)) (hR1 : R (z1 - 1, z2 - 1) (z1 - 1, z2)) (hR2 : R (z1 - 1, z2) (z1, z2)) :
    ∃ a b : ℤ, (z1, z2) ∈ squareCorners a b ∧
      ∀ c' ∈ squareCorners a b, c' ≠ (z1, z2) → Relation.TransGen (fun x y => R x y ∧ Edge y x) c' (z1, z2) := by
  refine ⟨z1 - 1, z2 - 1, by simp [squareCorners], private_of_return ?_ hR0 ?_ hR1 ?_ hR2 ?_⟩
  · intro c' hc' hne
    obtain ⟨x, y⟩ := c'
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, ne_eq] at hc' hne ⊢
    omega
  all_goals
    simp only [Edge, incomingNeg, incomingPos, EvenSite]
    split_ifs <;> simp only [Prod.mk.injEq, true_and, and_true, true_or, or_true] <;> omega

end FLatticePaper.W1FreeSquare
