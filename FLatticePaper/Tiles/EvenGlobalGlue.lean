import FLatticePaper.Tiles.ClosedWalkEven
import FLatticePaper.Tiles.OddGlobalGlue
import FLatticePaper.Tiles.DeckCoverage
import FLatticePaper.Tiles.StandardAll

/-! The even child of the gluing of `OddGlobalGlue`: the same route with the even tile, the even fraction and the even
closed walks. The core `glue_core` is shared; the covering comes from `deck_covers_even_all`. The covering hypotheses H2
of the closed-walk theorems are inherited. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation

/-- Every site lies in a translate of the even standard tile (the modified deck covers the tile). -/
theorem even_cover (w : Word) :
    ∀ x : ℤ × ℤ, ∃ i : ℤ × ℤ, x ∈ dom (↑(evenTile w) : Set (ℤ × ℤ)) (texV1Even (fracEven w)) (texV2 (fracEven w)) i := by
  intro x
  obtain ⟨rep, hrep, hspan⟩ := FLatticePaper.Tiles.StandardAll.deck_covers_even_all w x
  obtain ⟨k, k', hk⟩ := hspan
  have hkern : (fracEven w).modifiedDeck.kernel = texV1Even (fracEven w) :=
    FLatticePaper.Tiles.DeckCoverage.modifiedDeck_kernel_of_even (parentsAt_valid w).current_even_parity
  have hvP : vP (texV1Even (fracEven w)) (texV2 (fracEven w)) (k, k') =
      PeriodDeck.combine (fracEven w).modifiedDeck k k' := by
    simp only [PeriodDeck.combine, vP, hkern]
    rfl
  refine ⟨(k, k'), ?_⟩
  show x - vP (texV1Even (fracEven w)) (texV2 (fracEven w)) (k, k') ∈ (↑(evenTile w) : Set (ℤ × ℤ))
  have e : x - PeriodDeck.combine (fracEven w).modifiedDeck k k' = rep := by
    rw [← hk]
    exact sub_sub_cancel x rep
  rw [hvP, e, Finset.mem_coe]
  exact hrep

/-- The glued even odometer: a function on `Z^2` extending the even odometer on its tile up to a constant, with the two
translation rules of the modified deck of `fracEven w`. The covering hypotheses H2 are inherited. -/
theorem even_glue (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w true) (lastPosOf (hStringAt (hWordOf w true) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Even (fracEven w) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w true).reverse (texV1Even (fracEven w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w true) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracEven w)) ∈ cellTileOf (evenTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w true).reverse (1, -2)) z) :
    ∃ f : ℤ × ℤ → ℤ, (∃ c : ℤ, ∀ x ∈ (↑(evenTile w) : Set (ℤ × ℤ)), f x = (evenO w).val x + c) ∧
      (∃ c1 : ℤ, ∀ x : ℤ × ℤ, f (x + texV1Even (fracEven w)) = f x + c1) ∧
      (∃ c2 : ℤ, ∀ x : ℤ × ℤ, f (x + texV2 (fracEven w)) =
        f x + dotZ ((fracEven w).num, -(fracEven w).den) x + c2) := by
  obtain ⟨κ, hκ⟩ := even_hkappa S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  exact glue_core (↑(evenTile w)) (evenO w).val (fracEven w).num (fracEven w).den (texV1Even (fracEven w))
    (texV2 (fracEven w)) (0, 0) ((fracEven w).num, -(fracEven w).den) κ hκ (evenTile_hA1h w) (evenTile_hA1v w)
    (evenTile_hA2 w) rfl rfl (Or.inl rfl) (even_cover w)

end FLatticePaper.Tiles
