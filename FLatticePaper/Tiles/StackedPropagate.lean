/-! The order propagation of two column-convex, edge-connected cell families. Over each column `t` the cells of a tile `T` occupy
the heights `[loT t, hiT t]`, and the cells of the translate `T - v` occupy `[loS t, hiS t]`. The two families are disjoint over
each column. If consecutive columns overlap in each family (edge-connectedness), then "the translate lies below the tile" in one
column persists to the next: the two overlaps force the translate's top in column `t + 1` below the tile's bottom there. -/

namespace FLatticePaper.Tiles.StackedPropagate

/-- **One step of the propagation.** If the translate is below the tile in column `t`, it is below in column `t + 1`. -/
theorem below_succ (loT hiT loS hiS : Int → Int) (t : Int)
    (hT : ∀ s, loT (s + 1) ≤ hiT s ∧ loT s ≤ hiT (s + 1))
    (hS : ∀ s, loS (s + 1) ≤ hiS s ∧ loS s ≤ hiS (s + 1))
    (hdisj : ∀ s, hiS s < loT s ∨ hiT s < loS s)
    (hbelow : hiS t < loT t) : hiS (t + 1) < loT (t + 1) := by
  rcases hdisj (t + 1) with h | h
  · exact h
  · exfalso
    have h1 := (hS t).1
    have h2 := (hT t).2
    omega

end FLatticePaper.Tiles.StackedPropagate
