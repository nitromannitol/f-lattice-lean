import FLatticePaper.Tiles.ConnectedAltL
import FLatticePaper.Tiles.AltPiecesAgree
import FLatticePaper.Tiles.GlueEnds

/-! # The L-pieces of a corrected parent on their retained sides

When the alternate decomposition of the parent word is corrected, two entries of the parent piece's decomposition are elongated
L-corrections. On the sides that `lemma:l_correc_properties` keeps (`paperLSides`), an L-correction equals the standard tile
odometer up to one constant (`JointFamily.LSidesAgree`). So on those sides the parent piece equals the standard register, its
affine factor and one constant (`L_identity`). The corners used for the constants lie on the kept sides: the start and end tiles
of the side strings at the standard anchors (`odd_side_right`, `even_side_more`, with `ConnectedAltL.odd_side_corners` and
`even_side_corners`). -/

namespace FLatticePaper.Tiles.AltLSides

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

theorem getLastD_mem' {α : Type*} (l : List α) (d : α) (h : l ≠ []) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

/-- `D` and `D - 1` on the right side of the odd tile of `wd`. -/
theorem odd_side_right (wd : Word) :
    vP1 (wd ++ [Digit.two]) + vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ)) ∈
        placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .vPlus) ∧
      vP1 (wd ++ [Digit.two]) + vP2 (wd ++ [Digit.two]) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈
        placedSites (sideString (hWordOf wd false) (vWordOf wd false) 0 .vPlus) := by
  obtain ⟨hX, hY⟩ := ConnectedAltL.fracOdd_snoc_two wd
  have hs : sideString (hWordOf wd false) (vWordOf wd false) 0 .vPlus =
      vStringAt (vWordOf wd false) (texV1Odd (StandardClause.fracOdd wd) - (1, 1)) := by
    simp only [sideString]
    rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_odd wd]
  rw [hs]
  have hne : vStringAt (vWordOf wd false) (texV1Odd (StandardClause.fracOdd wd) - (1, 1)) ≠ [] :=
    GlueStringDecomp.vStringAt_ne _ _ (by
      intro h; have := (StringCorners.vertWord_head_last wd).1
      change (vWordOf wd false).head? = some Letter.p at this
      rw [h] at this; simp at this)
  have hl := GlueEnds.right_last (vWordOf wd false) (texV1Odd (StandardClause.fracOdd wd) - (1, 1))
    (StringCorners.vertWord_head_last wd).2
  rw [StdCornerAnchors.stdAnchorC_odd wd] at hl
  have hmem := getLastD_mem' _ (ZTile.zero, 0) hne
  rw [hl] at hmem
  have m1 := JointRot.mem_placedSites_of hmem (u := ((1 : ℤ), (1 : ℤ))) (by simp [tileShape])
  have m2 := JointRot.mem_placedSites_of hmem (u := ((0 : ℤ), (1 : ℤ))) (by simp [tileShape])
  rw [← hX, ← hY]
  constructor
  · convert m1 using 1; ext <;> simp; ring
  · convert m2 using 1; ext <;> simp; ring

/-- The corners `1`, `Y + 1` on the left side, `X - i`, `D`, `D - 1` on the right side and `D` on the top side of the even tile of
`wd`. -/
theorem even_side_more (wd : Word) :
    ((1 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vMinus) ∧
    vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (0 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vMinus) ∧
    vQ1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ)) ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vPlus) ∧
    vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vPlus) ∧
    vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .vPlus) ∧
    vQ1 (wd ++ [Digit.three]) + vQ2 (wd ++ [Digit.three]) + ((1 : ℤ), (-1 : ℤ)) ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 .hMinus) := by
  obtain ⟨hX, hY⟩ := ConnectedAltL.fracEven_snoc_three wd
  have hV := JointRot.side_vMinus (vWordOf wd true) (texV2 (StandardClause.fracEven wd))
    (StringCorners.vWord_even_head_last wd).1 (StringCorners.vWord_even_head_last wd).2 (StdCornerAnchors.stdAnchorY_even wd)
  have hwv : vWordOf wd true ≠ [] := by
    intro h; have := (StringCorners.vWord_even_head_last wd).1; rw [h] at this; simp at this
  have hVp := JointRot.side_vPlus (vWordOf wd true) hwv (lastPosOf (hStringAt (hWordOf wd true) 0))
  rw [hY] at hV
  have hs : sideString (hWordOf wd true) (vWordOf wd true) 0 .vPlus =
      vStringAt (vWordOf wd true) (texV1Even (StandardClause.fracEven wd) - (1, 1)) := by
    simp only [sideString]
    rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_even wd]
  have hne : vStringAt (vWordOf wd true) (texV1Even (StandardClause.fracEven wd) - (1, 1)) ≠ [] :=
    GlueStringDecomp.vStringAt_ne _ _ hwv
  have hl := GlueEnds.right_last (vWordOf wd true) (texV1Even (StandardClause.fracEven wd) - (1, 1))
    (StringCorners.vWord_even_head_last wd).2
  rw [StdCornerAnchors.stdAnchorC_even wd] at hl
  have hmem := getLastD_mem' _ (ZTile.zero, 0) hne
  rw [hl] at hmem
  have m1 := JointRot.mem_placedSites_of hmem (u := ((1 : ℤ), (1 : ℤ))) (by simp [tileShape])
  have m2 := JointRot.mem_placedSites_of hmem (u := ((0 : ℤ), (1 : ℤ))) (by simp [tileShape])
  -- the top side
  have hwh : (hWordOf wd true).reverse ≠ [] := by
    intro h; rw [List.reverse_eq_nil_iff] at h; have := (hWordOf_head_last wd true).1; rw [h] at this; simp at this
  have hlast : (hWordOf wd true).reverse.getLast? = some Letter.q := by
    rw [List.getLast?_reverse]; exact (hWordOf_head_last wd true).1
  obtain ⟨t, ht, htl⟩ := GlueEnds.top_last (hWordOf wd true).reverse
    (lastPosOf (vRevStringAt (vWordOf wd true).reverse 0)) hlast
  have hmt := getLastD_mem' _ (ZTile.zero, 0) (GlueStringDecomp.hRevStringAt_ne (hWordOf wd true).reverse
    (lastPosOf (vRevStringAt (vWordOf wd true).reverse 0)) hwh)
  rw [htl] at hmt
  have m3 := JointRot.mem_placedSites_of hmt (u := ((1 : ℤ), (1 : ℤ))) (by rcases ht with rfl | rfl <;> simp [tileShape])
  rw [GlueStringDecomp.lp_top_even] at m3
  refine ⟨hV.1, hV.2, ?_, ?_, ?_, ?_⟩
  · have e : lastPosOf (hStringAt (hWordOf wd true) 0) + ((1 : ℤ), (0 : ℤ)) = vQ1 (wd ++ [Digit.three]) - ((0 : ℤ), (1 : ℤ)) := by
      rw [show (0 : GInt) = ((0 : ℤ), (0 : ℤ)) from rfl, StdCornerAnchors.stdAnchorX_even wd, hX]
      refine Prod.ext ?_ ?_ <;> (simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega)
    rw [e] at hVp; exact hVp
  · rw [hs, ← hX, ← hY]; convert m1 using 1; ext <;> simp; ring
  · rw [hs, ← hX, ← hY]; convert m2 using 1; ext <;> simp; ring
  · simp only [sideString]
    rw [← hX, ← hY]; convert m3 using 1
    rw [StdCornerAnchors.stdAnchorY_even wd]; ext <;> simp <;> ring

/-- **The parent piece on the kept sides of an L-entry.** If `H` respects `ps` and the L-entry `stdPiece L off aff` of `ps` agrees
with `T` up to `c` on `S`, then on `S + off` the parent equals `T`, the affine factor and one constant. -/
theorem L_identity (H T L : PartialOdometer) (ps : List Piece) (hR : RespectsPieces H ps) (off aff : ℤ × ℤ)
    (hmem : stdPiece L off aff ∈ ps) (S : Set (ℤ × ℤ)) (c : ℤ)
    (hS : ∀ y ∈ S, y ∈ L.dom ∧ y ∈ T.dom ∧ L.val y = T.val y + c) :
    (∀ x, x - off ∈ S → x ∈ (↑H.dom : Set (ℤ × ℤ))) ∧
      ∃ b : ℤ, ∀ x, x - off ∈ S → H.val x = T.val (x - off) + dotS aff x + b := by
  have hpl : ∀ x, x - off ∈ S → x ∈ (stdPiece L off aff).placed := fun x hx =>
    (AltPiecesAgree.mem_placed_std L off aff x).mpr (hS _ hx).1
  refine ⟨fun x hx => ?_, ?_⟩
  · have : x ∈ pieceUnion ps := JointGlue.mem_pieceUnion.mpr ⟨_, hmem, hpl x hx⟩
    rw [← hR.1] at this
    exact this
  · obtain ⟨b, hb⟩ := hR.2 _ hmem
    refine ⟨b + c, fun x hx => ?_⟩
    have e1 := hb x (hpl x hx) (by simp [stdPiece])
    have e2 := (hS _ hx).2.2
    simp only [stdPiece] at e1
    rw [e1, e2]
    ring

end FLatticePaper.Tiles.AltLSides
