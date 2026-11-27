import FLatticePaper.Tiles.PointNonNeighbour
import FLatticePaper.Tiles.CommonExtensionFamily

/-! The overlap graph of the translates `dom P v1 v2 p = P + v_p` (`CommonExtFamily.dom`) is the unit-step graph, when
the point set `P` misses its non-surround and diagonal translates. This is the hypothesis `hA2` of
`family_closed_walks_zero` (`lemma:common-extension-pseudo-square`, item (ii)), for the standard tiles. -/

namespace FLatticePaper.Tiles.CommonExtStandard

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.CommonExtFamily FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause

/-- A point `z` of `P` with `z - vP d` in `P`, for a nonzero `d`, forces `d` to be a unit step. -/
theorem unit_of_contact {P : Finset (ℤ × ℤ)} {v1 v2 : ℤ × ℤ}
    (hnon : ∀ k k' : ℤ, (2 ≤ |k| ∨ 2 ≤ |k'|) → ∀ z ∈ P,
      z - (k * v1.1 + k' * v2.1, k * v1.2 + k' * v2.2) ∉ P)
    (hdiag : ∀ z ∈ P, z - (v1 + v2) ∉ P ∧ z + (v1 + v2) ∉ P ∧ z - (v1 - v2) ∉ P ∧ z + (v1 - v2) ∉ P)
    {d : ℤ × ℤ} (hd : d ≠ 0) {z : ℤ × ℤ} (hz : z ∈ P) (hzd : z - vP v1 v2 d ∈ P) :
    (d.1 = 1 ∧ d.2 = 0) ∨ (d.1 = -1 ∧ d.2 = 0) ∨ (d.1 = 0 ∧ d.2 = 1) ∨ (d.1 = 0 ∧ d.2 = -1) := by
  obtain ⟨d1, d2⟩ := d
  by_cases hns : 2 ≤ |d1| ∨ 2 ≤ |d2|
  · exact absurd hzd (hnon d1 d2 hns z hz)
  · have h1 : |d1| ≤ 1 := by
      have := not_or.mp hns
      omega
    have h2 : |d2| ≤ 1 := by
      have := not_or.mp hns
      omega
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    rcases (show d1 = -1 ∨ d1 = 0 ∨ d1 = 1 by omega) with rfl | rfl | rfl <;>
      rcases (show d2 = -1 ∨ d2 = 0 ∨ d2 = 1 by omega) with rfl | rfl | rfl
    · -- (-1,-1): the translate by -(v1+v2)
      have e : vP v1 v2 (-1, -1) = -(v1 + v2) :=
        Prod.ext (by simp only [vP, Prod.fst_neg, Prod.fst_add]; ring) (by simp only [vP, Prod.snd_neg, Prod.snd_add]; ring)
      rw [e, sub_neg_eq_add] at hzd
      exact absurd hzd (hdiag z hz).2.1
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · -- (-1,1): the translate by -(v1 - v2)
      have e : vP v1 v2 (-1, 1) = -(v1 - v2) :=
        Prod.ext (by simp only [vP, Prod.fst_neg, Prod.fst_sub]; ring) (by simp only [vP, Prod.snd_neg, Prod.snd_sub]; ring)
      rw [e, sub_neg_eq_add] at hzd
      exact absurd hzd (hdiag z hz).2.2.2
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · simp at hd
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · -- (1,-1): the translate by v1 - v2
      have e : vP v1 v2 (1, -1) = v1 - v2 :=
        Prod.ext (by simp only [vP, Prod.fst_sub]; ring) (by simp only [vP, Prod.snd_sub]; ring)
      rw [e] at hzd
      exact absurd hzd (hdiag z hz).2.2.1
    · exact Or.inl ⟨rfl, rfl⟩
    · -- (1,1): the translate by v1 + v2
      have e : vP v1 v2 (1, 1) = v1 + v2 :=
        Prod.ext (by simp only [vP, Prod.fst_add]; ring) (by simp only [vP, Prod.snd_add]; ring)
      rw [e] at hzd
      exact absurd hzd (hdiag z hz).1

/-- The overlap graph of the translates of a point set with those exclusions is the unit-step graph (`hA2`). -/
theorem adj_unit_of_contact {P : Finset (ℤ × ℤ)} {v1 v2 : ℤ × ℤ}
    (hnon : ∀ k k' : ℤ, (2 ≤ |k| ∨ 2 ≤ |k'|) → ∀ z ∈ P,
      z - (k * v1.1 + k' * v2.1, k * v1.2 + k' * v2.2) ∉ P)
    (hdiag : ∀ z ∈ P, z - (v1 + v2) ∉ P ∧ z + (v1 + v2) ∉ P ∧ z - (v1 - v2) ∉ P ∧ z + (v1 - v2) ∉ P)
    {x y : ℤ × ℤ} (h : (overlapGraph (dom (↑P : Set (ℤ × ℤ)) v1 v2)).Adj x y) :
    (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
      (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1) := by
  obtain ⟨hne, p, hpA, hpB⟩ := h
  have hA : p - vP v1 v2 x ∈ P := by
    have := hpA
    exact Finset.mem_coe.mp this
  have hB : p - vP v1 v2 y ∈ P := by
    have := hpB
    exact Finset.mem_coe.mp this
  have hz2 : (p - vP v1 v2 x) - vP v1 v2 (y - x) ∈ P := by
    have e : (p - vP v1 v2 x) - vP v1 v2 (y - x) = p - vP v1 v2 y :=
      Prod.ext (by simp only [vP, Prod.fst_sub, Prod.snd_sub]; ring) (by simp only [vP, Prod.fst_sub, Prod.snd_sub]; ring)
    rw [e]
    exact hB
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hne.symm
  have key := unit_of_contact hnon hdiag hd hA hz2
  have c1 : (y - x).1 = y.1 - x.1 := rfl
  have c2 : (y - x).2 = y.2 - x.2 := rfl
  omega

/-- **`hA2` for the odd standard family**: the overlap graph of the translates `T + v_p` is the unit-step graph. -/
theorem oddTile_hA2 (w : Farey.Word) :
    ∀ x y : ℤ × ℤ, (overlapGraph (dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)))).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1) := by
  intro x y h
  exact adj_unit_of_contact (fun k k' hns z hz => oddTile_nonneighbour w k k' hns z hz)
    (fun z hz => ⟨(oddTile_diagonal_disjoint w).1 z hz, (oddTile_diagonal_disjoint w).2.1 z hz,
      (oddTile_diagonal_disjoint w).2.2.1 z hz, (oddTile_diagonal_disjoint w).2.2.2 z hz⟩) h

/-- **`hA2` for the even standard family.** -/
theorem evenTile_hA2 (w : Farey.Word) :
    ∀ x y : ℤ × ℤ, (overlapGraph (dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)))).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1) := by
  intro x y h
  exact adj_unit_of_contact (fun k k' hns z hz => evenTile_nonneighbour w k k' hns z hz)
    (fun z hz => ⟨(evenTile_diagonal_disjoint w).1 z hz, (evenTile_diagonal_disjoint w).2.1 z hz,
      (evenTile_diagonal_disjoint w).2.2.1 z hz, (evenTile_diagonal_disjoint w).2.2.2 z hz⟩) h

end FLatticePaper.Tiles.CommonExtStandard
