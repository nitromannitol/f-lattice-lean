import FLatticePaper.Tiles.PackRotate
import FLatticePaper.Tiles.PackAssembly
import FLatticePaper.Tiles.AlmostTilingAssembly

/-! Task 50, part 2 (Q10): `NoFarAdjacency` for the tile of the almost square tiling.

A gap cell `d = c + e` (with `c ∈ T`, `e` a unit vector, `d ∉ T`) lying in a translate `T + u` of a non-surround lattice vector
`u` gives `Overlap T (u − e)`. So the gap clause follows from the non-overlap of `T` with the translates by `u − e`, `u` non-surround.
Such a translate is disjoint from the tile: for `|j| ≥ 2` by `not_overlap_unit_H`, and for `|i| ≥ 2` by the quarter turn
(`overlap_rotCells_iff`, `isBoundaryFrom_rotCells_word`), whose first word is `w₂·(−i)`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Tiles.BoundaryWalks (IsBoundaryFrom)

/-- The first word `w₁` of the packing has the first letter `1`, so its first coordinate sum is at least one. -/
theorem one_le_sum_fst_of_head {w : F2Word} (h1 : ∀ x ∈ w, x = .one ∨ x = .i) (hh : w.head? = some .one) :
    1 ≤ (F2Word.sum w).1 := by
  cases w with
  | nil => simp at hh
  | cons x u =>
    have hx : x = .one := by simpa using hh
    subst hx
    have hu := sum_fst_nonneg_of_one_i u (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
    have e : F2Word.sum (Unit4.one :: u) = Unit4.vec Unit4.one + F2Word.sum u := by simp [F2Word.sum]
    rw [e, Prod.fst_add]
    simp [Unit4.vec]
    linarith

/-- A coordinate with `2 ≤ |x|` is at least two or at most minus two. -/
theorem two_le_or_le_neg_two {x : ℤ} (h : 2 ≤ |x|) : 2 ≤ x ∨ x ≤ -2 := by
  rcases le_abs'.mp h with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

/-- **The gap translates of the packing do not overlap the tile**: for a non-surround pair `(i, j)` (`2 ≤ |i|` or `2 ≤ |j|`) and a
unit shift `e`, the translate by `i v₁ + j v₂ − e` does not overlap the tile. -/
theorem gap_not_overlap {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI))
    (i j : ℤ) (hns : 2 ≤ |i| ∨ 2 ≤ |j|) (e1 e2 : ℤ) (he1 : -1 ≤ e1 ∧ e1 ≤ 1) (he2 : -1 ≤ e2 ∧ e2 ≤ 1) :
    ¬ Overlap T (i * (F2Word.sum w1).1 + j * ((F2Word.sum w2).1 - 1) - e1,
      i * (cntI w1 + 1) + j * cntI w2 - e2) := by
  have hT2 : IsBoundaryFrom T c (boundaryWordOf w1 w2) := ((BoundaryWalks.isBoundaryWordAt_iff T c _).mp hT).2
  have hD := cntI_w2_pos hA2
  by_cases hj : 2 ≤ |j|
  · exact not_overlap_unit_H hT2 h1 h2 hA1 hD i j e1 e2 (two_le_or_le_neg_two hj) he1 he2
  · have hi : 2 ≤ |i| := hns.resolve_right hj
    obtain ⟨c', hT'⟩ := isBoundaryFrom_rotCells_word T c w1 w2 hT2
    have h1' : ∀ x ∈ w2.map Unit4.mulNegI, x = .one ∨ x = .i := hA2.1
    have h2' : ∀ x ∈ w1.map Unit4.mulI, x = .i ∨ x = .negOne := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h1 y hy with rfl | rfl <;> decide
    have hD' : 1 ≤ cntI (w1.map Unit4.mulI) := by
      rw [cntI_mulI h1]
      exact one_le_sum_fst_of_head h1 hA1.2.1
    obtain ⟨he1a, he1b⟩ := he1
    obtain ⟨he2a, he2b⟩ := he2
    have key := not_overlap_unit_H hT' h1' h2' hA2 hD' (-j) i (-e2) e1 (two_le_or_le_neg_two hi) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩
    rw [sum_fst_mulNegI, cntI_mulNegI h2, sum_fst_mulI, cntI_mulI h1] at key
    have s1 : cntI w1 = (F2Word.sum w1).2 :=
      (sum_snd w1 (fun x hx => by rcases h1 x hx with rfl | rfl <;> decide)).symm
    have s2 : cntI w2 = (F2Word.sum w2).2 :=
      (sum_snd w2 (fun x hx => by rcases h2 x hx with rfl | rfl <;> decide)).symm
    have e : rotI (i * (F2Word.sum w1).1 + j * ((F2Word.sum w2).1 - 1) - e1,
        i * (cntI w1 + 1) + j * cntI w2 - e2) =
        (-j * (F2Word.sum w2).2 + i * (-(F2Word.sum w1).2 - 1) - -e2,
          -j * (-(F2Word.sum w2).1 + 1) + i * (F2Word.sum w1).1 - e1) := by
      rw [s1, s2]
      apply Prod.ext
      · simp only [rotI]
        ring
      · simp only [rotI]
        ring
    intro hov
    apply key
    have h := (overlap_rotCells_iff T _).mpr hov
    rw [e] at h
    exact h

/-- **`NoFarAdjacency` for the tile of the almost square tiling**: a gap cell of a non-surround translate would give an overlap
of the tile with a gap translate, which `gap_not_overlap` excludes. -/
theorem noFarAdjacency_of_boundary {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hA1 : Admissible w1) (hA2 : Admissible (w2.map Unit4.mulNegI)) :
    NoFarAdjacency T (almostV₁ w1) (almostV₂ w2) := by
  refine ⟨fun d hcell hd => ?_⟩
  obtain ⟨c', hc', e, he, hcd⟩ := hcell
  have he' : -1 ≤ e.1 ∧ e.1 ≤ 1 ∧ -1 ≤ e.2 ∧ e.2 ≤ 1 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp
  by_cases hL : ∃ u ∈ latticeOf (almostV₁ w1) (almostV₂ w2), d - u ∈ T
  · obtain ⟨u, hu, hdu⟩ := hL
    obtain ⟨k, k', rfl⟩ := hu
    by_cases hz : (k, k') = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
      exfalso
      apply hd
      have h00 : d - (0 * (almostV₁ w1).1 + 0 * (almostV₂ w2).1, 0 * (almostV₁ w1).2 + 0 * (almostV₂ w2).2) = d := by
        apply Prod.ext <;> simp
      rw [h00] at hdu
      exact hdu
    · by_cases hsur : -1 ≤ k ∧ k ≤ 1 ∧ -1 ≤ k' ∧ k' ≤ 1
      · left
        exact ⟨_, ⟨k, k', hsur.1, hsur.2.1, hsur.2.2.1, hsur.2.2.2, hz, rfl⟩, hdu⟩
      · exfalso
        have hns : 2 ≤ |k| ∨ 2 ≤ |k'| := by
          by_contra hc
          simp only [not_or, not_le] at hc
          apply hsur
          obtain ⟨hk1, hk2⟩ := abs_lt.mp hc.1
          obtain ⟨hk1', hk2'⟩ := abs_lt.mp hc.2
          omega
        rw [almostV1_coords h1, almostV2_coords h2] at hdu
        subst hcd
        have hno := gap_not_overlap hT h1 h2 hA1 hA2 k k' hns e.1 e.2 ⟨he'.1, he'.2.1⟩ ⟨he'.2.2.1, he'.2.2.2⟩
        apply hno
        refine ⟨c', hc', ?_⟩
        have hv : c' - (k * (F2Word.sum w1).1 + k' * ((F2Word.sum w2).1 - 1) - e.1,
            k * (cntI w1 + 1) + k' * cntI w2 - e.2) =
            c' + e - (k * (F2Word.sum w1).1 + k' * ((F2Word.sum w2).1 - 1),
              k * (cntI w1 + 1) + k' * cntI w2) := by
          apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;> ring
        rw [hv]
        exact hdu
  · right
    intro u hu hdu
    exact hL ⟨u, hu, hdu⟩

end FLatticePaper.Tiles
