import FLatticePaper.Tiles.TilingCriteria

/-! Non-vacuity of `tiling_criteria`: the unit cell `{0}` has boundary word `1 * i * (-1) * (-i)`, i.e. `w₁ = [1]`, `w₂ = [i]`,
and it generates the regular tiling by the unit lattice `Z 1 + Z i`. -/

open FLatticePaper.Tiles

theorem unit_cell_simple : IsSimpleTile ({0} : CellTile) := by
  refine ⟨⟨0, [Unit4.one, Unit4.i, Unit4.negOne, Unit4.negI], ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · intro x hx y hy
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    exact Relation.ReflTransGen.refl

theorem unit_cell_regular :
    IsRegularTiling ({0} : CellTile) (F2Word.sum [Unit4.one]) (F2Word.sum [Unit4.i]) :=
  tiling_criteria _ [Unit4.one] [Unit4.i] unit_cell_simple ⟨0, by decide⟩

#print axioms unit_cell_regular
