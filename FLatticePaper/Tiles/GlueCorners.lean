import FLatticePaper.Tiles.GlueSeams
import FLatticePaper.Tiles.SurgicalCornerThird
import FLatticePaper.Tiles.LSidesEven

/-! # The affine factors of a register at the corners of its strings

For an odometer `o` that respects the strings of its standard tile and is normalised on its first tile
(`o = o_{1/1} + β` there, the zero-slope normalisation `TileSlopeZero`), the affine factors (`tileAffine`) at the corners
`A, B, C, D` of `cornerTiles` are `0, 0, (n - 1, 1 - d), (n, 1 - d)` (`register_corners_odd`, `register_corners_even`):
the normalisation gives `A`, and (b) of the weak lemma gives `B - A = 0`, `C - D = (-1, 0)`, `C - B = (n - 1, 1 - d)`
(`corner_affine_12`, `corner_3_family_of`). The affine factor of a family at one of its tiles is `tileAffine` of the
odometer there (`family_tileAffine`), and the enlarged tile has the same affine factor as `T_{1/1}` (`tileAffine_oneD`). -/

namespace FLatticePaper.Tiles.GlueCorners

open FLatticePaper.Farey FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- The affine factor of a family at a tile is `tileAffine` of the odometer it carries. -/
theorem family_tileAffine (F : PTFamily) (o : GInt → ℤ) (hF : ∀ k < F.n, ∀ y ∈ F.dom k, o y = F.odo k y) (k : ℕ)
    (hk : k < F.n) : tileAffine o (F.tile k) = (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  unfold tileAffine
  rw [tileSlope_eq F o k (hF k hk), PTFamily.slope_tile]
  abel

/-- The normalised first tile has affine factor `0`. -/
theorem tileAffine_normal (o : GInt → ℤ) (β : ℤ) (hN : ∀ x ∈ tileShape ZTile.one, o x = zTileOdo ZTile.one x + β) :
    tileAffine o (ZTile.one, 0) = 0 := by
  unfold tileAffine
  have e : placedSites [(ZTile.one, (0 : GInt))] = tileShape ZTile.one := by
    rw [placedSites_single]
    simp
  rw [e, slopeOf_congr o (fun x => zTileOdo ZTile.one x + β) _ hN, LSidesEven.slopeOf_add_const]
  exact sub_self _

/-- The enlarged tile `T^d_{1/1}` has the affine factor of `T_{1/1}` at the same corner (the two have the same unit square). -/
theorem tileAffine_oneD (o : GInt → ℤ) (p : GInt) : tileAffine o (ZTile.oneD, p) = tileAffine o (ZTile.one, p) := by
  unfold tileAffine
  have key : ∀ t : ZTile, slopeOf o ((tileShape t).map (· + p)) = slopeOf (fun y => o (y + p)) (tileShape t) := by
    intro t
    have := slopeOf_translate (fun y => o (y + p)) (tileShape t) p
    simpa using this
  rw [placedSites_single, placedSites_single, key, key, slopeOf_eq, slopeOf_eq,
    show unitSquares (tileShape ZTile.oneD) = unitSquares (tileShape ZTile.one) by decide,
    zTileBaseSlope_oneD, zTileBaseSlope_one]

theorem headD_hStringAt (wh : BinaryWord) (hh : wh.head? = some Letter.q) :
    (hStringAt wh 0).headD (ZTile.zero, 0) = (ZTile.one, 0) := by
  obtain ⟨t, rfl⟩ := StringAppend.exists_cons_of_head wh _ hh
  cases t <;> simp [hStringAt, tileSeq, tileSeqAux, List.scanl_cons]

/-- **The corner affine factors of a normalised odd register.** -/
theorem register_corners_odd (u : Word) (T : Finset GInt) (o : GInt → ℤ)
    (hR : SurgicalWeak.RespectsAnchored T (hWordOf u false) (vWordOf u false) o) (β : ℤ)
    (hN : ∀ x ∈ tileShape ZTile.one, o x = zTileOdo ZTile.one x + β) :
    tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).1 = 0 ∧
      tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).2.1 = 0 ∧
      tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).2.2.1 =
        (((fracOdd u).num : ℚ) - 1, 1 - ((fracOdd u).den : ℚ)) ∧
      tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).2.2.2 =
        (((fracOdd u).num : ℚ), 1 - ((fracOdd u).den : ℚ)) := by
  obtain ⟨-, hA, hC, -, -⟩ := id hR
  obtain ⟨h12, hCD⟩ := corner_affine_12 _ _ o (hWordOf_head_last u false).1 (hWordOf_head_last u false).2 hA hC
  have h3 := corner_3_family_of u T o hR
  have hA0 : tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).1 = 0 := by
    show tileAffine o ((hStringAt (hWordOf u false) 0).headD (ZTile.zero, 0)) = 0
    rw [headD_hStringAt _ (hWordOf_head_last u false).1]
    exact tileAffine_normal o β hN
  have hB0 : tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).2.1 = 0 := by
    have := h12
    rw [hA0, sub_zero] at this
    exact this
  have hCv : tileAffine o (cornerTiles (hWordOf u false) (vWordOf u false) 0).2.2.1 =
      (((fracOdd u).num : ℚ) - 1, 1 - ((fracOdd u).den : ℚ)) := by
    rw [hB0, sub_zero] at h3
    exact h3
  refine ⟨hA0, hB0, hCv, ?_⟩
  rw [hCv] at hCD
  apply Prod.ext
  · have := congrArg Prod.fst hCD
    simp only [Prod.fst_sub] at this ⊢
    linarith
  · have := congrArg Prod.snd hCD
    simp only [Prod.snd_sub] at this ⊢
    linarith

/-- **The corner affine factors of a normalised even register.** -/
theorem register_corners_even (u : Word) (T : Finset GInt) (o : GInt → ℤ)
    (hR : SurgicalWeak.RespectsAnchored T (hWordOf u true) (vWordOf u true) o) (β : ℤ)
    (hN : ∀ x ∈ tileShape ZTile.one, o x = zTileOdo ZTile.one x + β) :
    tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).1 = 0 ∧
      tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).2.1 = 0 ∧
      tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).2.2.1 =
        (((fracEven u).num : ℚ) - 1, 1 - ((fracEven u).den : ℚ)) ∧
      tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).2.2.2 =
        (((fracEven u).num : ℚ), 1 - ((fracEven u).den : ℚ)) := by
  obtain ⟨-, hA, hC, -, -⟩ := id hR
  obtain ⟨h12, hCD⟩ := corner_affine_12 _ _ o (hWordOf_head_last u true).1 (hWordOf_head_last u true).2 hA hC
  have h3 := corner_3_family_even_of u T o hR
  have hA0 : tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).1 = 0 := by
    show tileAffine o ((hStringAt (hWordOf u true) 0).headD (ZTile.zero, 0)) = 0
    rw [headD_hStringAt _ (hWordOf_head_last u true).1]
    exact tileAffine_normal o β hN
  have hB0 : tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).2.1 = 0 := by
    have := h12
    rw [hA0, sub_zero] at this
    exact this
  have hCv : tileAffine o (cornerTiles (hWordOf u true) (vWordOf u true) 0).2.2.1 =
      (((fracEven u).num : ℚ) - 1, 1 - ((fracEven u).den : ℚ)) := by
    rw [hB0, sub_zero] at h3
    exact h3
  refine ⟨hA0, hB0, hCv, ?_⟩
  rw [hCv] at hCD
  apply Prod.ext
  · have := congrArg Prod.fst hCD
    simp only [Prod.fst_sub] at this ⊢
    linarith
  · have := congrArg Prod.snd hCD
    simp only [Prod.snd_sub] at this ⊢
    linarith

end FLatticePaper.Tiles.GlueCorners
