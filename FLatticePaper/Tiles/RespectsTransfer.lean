import FLatticePaper.Tiles.PartialBoundary

/-! # Transfer of `RespectsTiles` between odometers that agree on the placed sites

`RespectsTiles o rev ts S` only reads `S` on the domains of the placed tiles of `ts`. So if two odometers agree on the placed sites
of `ts`, a respect of one is a respect of the other. This is the step that lets the explicit families (which equal the paper
values) be used for the base odometers, once `InsideTile` puts the placed sites inside the odometer domain. -/

namespace FLatticePaper.Tiles

/-- A point of the domain of a placed tile is a placed site of the string. -/
theorem placed_of_dom (F : PTFamily) (k : ℕ) (hk : k < F.n) (x : GInt) (hx : x ∈ F.dom k) :
    x ∈ placedSites F.ts := by
  unfold PTFamily.dom at hx
  unfold placedSites
  rw [List.mem_flatMap]
  refine ⟨F.tile k, ?_, hx⟩
  unfold PTFamily.tile PTFamily.n at *
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- A respect transfers to an odometer that agrees with the original on the placed sites of the string. -/
theorem RespectsTiles.congr_placed {o : Orientation} {rev : Bool} {ts : List (ZTile × GInt)} {S S' : GInt → ℤ}
    (h : RespectsTiles o rev ts S) (hS : ∀ x ∈ placedSites ts, S x = S' x) :
    RespectsTiles o rev ts S' := by
  obtain ⟨F, hts, hodo, hresp⟩ := h
  refine ⟨F, hts, ?_, hresp⟩
  intro k hk x hx
  have hmem : x ∈ placedSites ts := by
    rw [← hts]
    exact placed_of_dom F k hk x hx
  rw [← hS x hmem]
  exact hodo k hk x hx

end FLatticePaper.Tiles
