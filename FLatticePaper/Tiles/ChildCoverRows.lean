import FLatticePaper.Tiles.StandardTiles

/-! Task 55 (R1), stated on cell rows. A child tile is a union of shifted register tiles. On a row `y`, a shifted register
tile `shift T o` has row `{x | lo (y - o.2) + o.1 ≤ x < hi (y - o.2) + o.1}`, where `lo, hi` are the row ends of the
register tile `T`. The first lemma is the end pattern of the odd child in the false phase whose only nonempty pieces on
row `y` are the two copies of `T1` at offsets `texV1Even q + texV1Even q` and `texV2 q`: the child's row is the
interval from the left end of the second copy to the right end of the first copy, under the no-gap inequalities. -/

namespace FLatticePaper.Tiles.Standard

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

/-- The row of a shifted tile: `(x, c) ∈ shift T o` iff `x - o.1` lies in the row `c - o.2` of `T`. -/
theorem mem_shift_row (T : Tile) (lo hi : ℤ → ℤ)
    (hT : ∀ x c : ℤ, ((x, c) : Site) ∈ T ↔ lo c ≤ x ∧ x < hi c) (o : Site) (x c : ℤ) :
    ((x, c) : Site) ∈ shift T o ↔ lo (c - o.2) ≤ x - o.1 ∧ x - o.1 < hi (c - o.2) := by
  rw [mem_shift]
  exact hT (x - o.1) (c - o.2)

/-- Odd child, false phase, end pattern with the two copies of `T1` only. On row `y` the four copies of `T2` are empty,
the child's row is `[A5, B4)` with `A5` the left end of the copy at `texV2 q` and `B4` the right end of the copy at
`texV1Even q + texV1Even q`, provided the no-gap inequalities hold. -/
theorem oddChildB_false_row_pattern (T1 T2 : Tile) (p q : Fraction) (y : ℤ) (lo hi : ℤ → ℤ)
    (hT1 : ∀ x c : ℤ, ((x, c) : Site) ∈ T1 ↔ lo c ≤ x ∧ x < hi c)
    (hE2 : ∀ x : ℤ, ((x, y) : Site) ∉ T2)
    (hE3 : ∀ x : ℤ, ((x, y) : Site) ∉ shift T2 (texV1Even q))
    (hE4 : ∀ x : ℤ, ((x, y) : Site) ∉ shift T2 (texV1Odd p + texV2 p))
    (hE5 : ∀ x : ℤ, ((x, y) : Site) ∉ shift T2 (texV1Odd p + texV2 p + texV1Even q))
    (hord : lo (y - (texV2 q).2) + (texV2 q).1 ≤ lo (y - (texV1Even q + texV1Even q).2) + (texV1Even q + texV1Even q).1 ∧
      lo (y - (texV1Even q + texV1Even q).2) + (texV1Even q + texV1Even q).1 ≤
        hi (y - (texV2 q).2) + (texV2 q).1 ∧
      hi (y - (texV2 q).2) + (texV2 q).1 ≤ hi (y - (texV1Even q + texV1Even q).2) + (texV1Even q + texV1Even q).1)
    (x : ℤ) :
    ((x, y) : Site) ∈ oddChildB false T1 T2 p q ↔
      lo (y - (texV2 q).2) + (texV2 q).1 ≤ x ∧
        x < hi (y - (texV1Even q + texV1Even q).2) + (texV1Even q + texV1Even q).1 := by
  simp only [oddChildB, Finset.mem_union, hE2 x, hE3 x, hE4 x, hE5 x, false_or, or_false]
  rw [mem_shift_row T1 lo hi hT1, mem_shift_row T1 lo hi hT1]
  constructor <;> intro h <;> omega

end FLatticePaper.Tiles.Standard
