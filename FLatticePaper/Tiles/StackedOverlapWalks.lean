import FLatticePaper.Tiles.StackedClass

/-! The interface of the class lemmas of the packing (stage 3). Over a column `t`, a point `(t, z2)` of an overlap of two tiles
is sandwiched between a point of the lower walk `B` and a point of the upper walk `D`: the lower tile gives a point of `B` at or
below `z2`, the upper tile gives a point of `D` at or above `z2`. If the extremes of the two walks over `t` satisfy the span
inequalities of the class (`dmin ≤ bmin`, `dmax ≤ bmax`), the point lies on both walks (`StackedClass.point_on_both_walks`).
The class lemmas therefore reduce to the span inequalities; the tile links are supplied by the column links of the tiles. -/

namespace FLatticePaper.Tiles.StackedOverlapWalks

open FLatticePaper.Tiles FLatticePaper.Tiles.StackedClass

/-- **An overlap point in a column lies on both walks, given the spans.** -/
theorem overlap_on_walks (B D : F2Word) (hB : ∀ x ∈ B, x = Unit4.one ∨ x = Unit4.i)
    (hD : ∀ x ∈ D, x = Unit4.one ∨ x = Unit4.i) (c1 c2 : GInt) (t z2 : ℤ)
    (hspan : ∃ bmin bmax dmin dmax : ℤ,
      ((t, bmin) : GInt) ∈ F2Word.walk c1 B ∧ ((t, bmax) : GInt) ∈ F2Word.walk c1 B ∧
      ((t, dmin) : GInt) ∈ F2Word.walk c2 D ∧ ((t, dmax) : GInt) ∈ F2Word.walk c2 D ∧
      (∀ q ∈ F2Word.walk c1 B, q.1 = t → bmin ≤ q.2 ∧ q.2 ≤ bmax) ∧
      (∀ q ∈ F2Word.walk c2 D, q.1 = t → dmin ≤ q.2 ∧ q.2 ≤ dmax) ∧
      dmin ≤ bmin ∧ dmax ≤ bmax)
    (hlo : ∃ h : ℤ, h ≤ z2 ∧ ((t, h) : GInt) ∈ F2Word.walk c1 B)
    (hhi : ∃ h : ℤ, z2 ≤ h ∧ ((t, h) : GInt) ∈ F2Word.walk c2 D) :
    ((t, z2) : GInt) ∈ F2Word.walk c1 B ∧ ((t, z2) : GInt) ∈ F2Word.walk c2 D := by
  obtain ⟨bmin, bmax, dmin, dmax, h1, h2, h3, h4, hBs, hDs, hd1, hd2⟩ := hspan
  obtain ⟨h, hh, hhW⟩ := hlo
  obtain ⟨h', hh', hh'W⟩ := hhi
  have e1 : bmin ≤ z2 := le_trans (hBs _ hhW rfl).1 hh
  have e2 : z2 ≤ dmax := le_trans hh' (hDs _ hh'W rfl).2
  exact point_on_both_walks B D hB hD c1 c2 t bmin bmax dmin dmax z2 h1 h2 h3 h4 hd1 hd2 e1 e2

end FLatticePaper.Tiles.StackedOverlapWalks
