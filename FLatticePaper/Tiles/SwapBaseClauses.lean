import FLatticePaper.Tiles.TileCompatInputs

/-! # Vacuous pairs of a decomposition

`PairCompat ps i j` holds when the placed domains of the entries `i` and `j` are disjoint: the constant `0` works, since the
overlap is empty. The one-base-register clauses of `SwapBaseInput` are discharged this way, from the disjointness of the tile
translates `O.dom + o1` and `O.dom + o2`. -/

namespace FLatticePaper.Tiles.SwapBaseClauses

open FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.TileCompatInputs

/-- Two entries of a decomposition, both standard pieces of one odometer `O` at the offsets `o1`, `o2`, are compatible when no
translate of `O.dom` by `o1` meets a translate by `o2`. -/
theorem pairCompat_of_disjoint (ps : List Piece) (i j : ℕ) (O : PartialOdometer) (o1 o2 a1 a2 : Site)
    (hp : ps[i]? = some (stdPiece O o1 a1)) (hq : ps[j]? = some (stdPiece O o2 a2))
    (hdisj : ∀ x ∈ O.dom, ∀ y ∈ O.dom, x + o1 ≠ y + o2) : PairCompat ps i j := by
  intro p q hp' hq'
  rw [hp] at hp'
  rw [hq] at hq'
  obtain rfl := Option.some.inj hp'
  obtain rfl := Option.some.inj hq'
  refine ⟨0, fun x hx hy _ _ => ?_⟩
  exfalso
  simp only [Piece.placed, stdPiece, Finset.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hab⟩ := hy
  exact hdisj a ha b hb hab.symm

end FLatticePaper.Tiles.SwapBaseClauses
