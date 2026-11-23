import FLatticePaper.Tiles.PackFrom
import FLatticePaper.Tiles.PackHStrip

/-! Task 50, part 2 (Q10): the gap translates of the H-strip.

For a boundary walk `boundaryWordOf W1 W2` (`IsBoundaryFrom`, letters and admissibility of `W1` as in the packing), the translate
of the tile by `i v₁ + j v₂ − e`, with `v₁ = (Σ W1 .1, B₁ + 1)`, `v₂ = (Σ W2 .1 − 1, B₂)` and `e` a vector with coordinates in
`[−1, 1]`, does not overlap the tile when `|j| ≥ 2`. The row inequality of the H-strip (`Nrow_le_H`, `Srow_ge_H`), the periodicity
of the entry column (`Hent_add_mul_period`) and the monotonicity (`Hent_mono_le`) give it with slack `(j − 1)(C + 1) + e₁ ≥ 0`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Tiles.BoundaryWalks (IsBoundaryFrom)

/-- **The gap translates in the H-direction**: for `|j| ≥ 2` and a unit shift `e` (coordinates in `[−1, 1]`), the translate by
`i v₁ + j v₂ − e` does not overlap the tile. -/
theorem not_overlap_unit_H {T : CellTile} {c : GInt} {W1 W2 : F2Word}
    (hT : IsBoundaryFrom T c (boundaryWordOf W1 W2))
    (h1 : ∀ x ∈ W1, x = .one ∨ x = .i) (h2 : ∀ x ∈ W2, x = .i ∨ x = .negOne)
    (hA1 : Admissible W1) (hD : 1 ≤ cntI W2) (i j e1 e2 : ℤ) (hj : 2 ≤ j ∨ j ≤ -2)
    (he1 : -1 ≤ e1 ∧ e1 ≤ 1) (he2 : -1 ≤ e2 ∧ e2 ≤ 1) :
    ¬ Overlap T (i * (F2Word.sum W1).1 + j * ((F2Word.sum W2).1 - 1) - e1,
      i * (cntI W1 + 1) + j * cntI W2 - e2) := by
  obtain ⟨he1a, he1b⟩ := he1
  obtain ⟨he2a, he2b⟩ := he2
  have hq := cntI_nonneg W1
  have hr := cntI_nonneg W2
  have hC := sum_fst_nonpos_of_i_negOne W2 h2
  refine not_overlap_of_from hT h1 h2 _ _ ?_
  intro t ht0 ht1 hd0 hd1
  rcases hj with hj | hj
  · -- `j ≥ 2`: the translate lies to the left of the tile (second disjunct)
    right
    have hN := Nrow_le_H c h1 h2 _ hd0
    have hS := Srow_ge_H c hA1 h1 h2 t ht0 ht1
    have ea : t - (i * (cntI W1 + 1) + j * cntI W2 - e2) + 1 =
        (t + 1 - j * cntI W2 + e2) + (-i) * (cntI W1 + 1) := by ring
    rw [ea, Hent_add_mul_period W1 h1 (-i)] at hN
    have ek : (-i) * (F2Word.sum W1).1 = -(i * (F2Word.sum W1).1) := by ring
    rw [ek] at hN
    have hM := Hent_mono_le W1 h1 (show t + 1 - j * cntI W2 + e2 ≤ t + 1 - cntI W2 by nlinarith)
    have hF : (j - 1) * ((F2Word.sum W2).1 - 1) ≤ -1 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ j - 2 by omega) (show (0 : ℤ) ≤ -1 - ((F2Word.sum W2).1 - 1) by omega)]
    have hjS : j * ((F2Word.sum W2).1 - 1) = ((F2Word.sum W2).1 - 1) + (j - 1) * ((F2Word.sum W2).1 - 1) := by ring
    linarith
  · -- `j ≤ −2`: the translate lies to the right of the tile (first disjunct)
    left
    have hN := Nrow_le_H c h1 h2 t ht0
    have hS := Srow_ge_H c hA1 h1 h2 _ hd0 hd1
    have ea : t - (i * (cntI W1 + 1) + j * cntI W2 - e2) + 1 - cntI W2 =
        (t + 1 - (j + 1) * cntI W2 + e2) + (-i) * (cntI W1 + 1) := by ring
    rw [ea, Hent_add_mul_period W1 h1 (-i)] at hS
    have ek : (-i) * (F2Word.sum W1).1 = -(i * (F2Word.sum W1).1) := by ring
    rw [ek] at hS
    have hM := Hent_mono_le W1 h1 (show t + 1 ≤ t + 1 - (j + 1) * cntI W2 + e2 by nlinarith)
    have hG : 1 ≤ (j + 1) * ((F2Word.sum W2).1 - 1) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -(j + 1) - 1 by omega) (show (0 : ℤ) ≤ -((F2Word.sum W2).1 - 1) - 1 by omega)]
    have hjS : (j + 1) * ((F2Word.sum W2).1 - 1) = j * ((F2Word.sum W2).1 - 1) + ((F2Word.sum W2).1 - 1) := by ring
    linarith

end FLatticePaper.Tiles
