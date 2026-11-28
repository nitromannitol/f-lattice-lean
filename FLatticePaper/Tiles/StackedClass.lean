import FLatticePaper.Tiles.StackedColumns

/-! The glue of the class lemmas of the packing (stage 3). Two walks `B` and `D` (letters `one` and `i`), with extreme heights
`bmin ≤ bmax` and `dmin ≤ dmax` over a column `t`, and a point of height `z2` over `t` with `bmin ≤ z2 ≤ dmax` and `dmin ≤ bmin`,
`dmax ≤ bmax`: the point lies on both walks. This is the last step of the class lemmas: the point is above the lower end of `B`
and below the upper end of `D` (the monotonicity of the two walks), and the two walks are closed under the heights between
their ends over a column (`walk_column_interval`). -/

namespace FLatticePaper.Tiles.StackedClass

open FLatticePaper.Tiles FLatticePaper.Tiles.StackedColumns

theorem point_on_both_walks (w1 w2 : F2Word) (hw1 : ∀ x ∈ w1, x = Unit4.one ∨ x = Unit4.i)
    (hw2 : ∀ x ∈ w2, x = Unit4.one ∨ x = Unit4.i) (c1 c2 : GInt) (t bmin bmax dmin dmax z2 : ℤ)
    (hbmin : ((t, bmin) : GInt) ∈ F2Word.walk c1 w1) (hbmax : ((t, bmax) : GInt) ∈ F2Word.walk c1 w1)
    (hdmin : ((t, dmin) : GInt) ∈ F2Word.walk c2 w2) (hdmax : ((t, dmax) : GInt) ∈ F2Word.walk c2 w2)
    (hdb1 : dmin ≤ bmin) (hdb2 : dmax ≤ bmax) (hlo : bmin ≤ z2) (hhi : z2 ≤ dmax) :
    ((t, z2) : GInt) ∈ F2Word.walk c1 w1 ∧ ((t, z2) : GInt) ∈ F2Word.walk c2 w2 := by
  constructor
  · exact walk_column_interval w1 hw1 c1 _ _ hbmin hbmax rfl (by omega) z2 (by omega) (by omega)
  · exact walk_column_interval w2 hw2 c2 _ _ hdmin hdmax rfl (by omega) z2 (by omega) (by omega)

end FLatticePaper.Tiles.StackedClass
