import FLatticePaper.Tiles.VertStringReflect
import FLatticePaper.Tiles.GlueStringDecomp
import FLatticePaper.Tiles.StdCornerAnchors
import FLatticePaper.Tiles.StringCorners
import FLatticePaper.Tiles.EvenMidVMinus

/-! # The even-first companion of the midpoint: the half-turn of the vertical side `vMinus` is the side `vPlus`

For a word `v` and a last letter `x`, `VertStringReflect.vRev_reflect_gen` says that the reversed vertical string of `v ++ [x]`
at `c` is the point reflection of the forward vertical string of `v ++ [x]` at `a`, with constant
`K = a + lastPosOf (vStringAt (v ++ [x]) 0) + shR x + c`. Each tile shape is symmetric under its half-turn (`sT t − s`), so a
point `z` of the reversed string is sent to `K − z`, a point of the forward string (`vRev_reflect_points`).

For the even register of `wd` with last letter `q` of `vWordOf wd true`, the constant is the centre `D = texV1Even F + texV2 F +
(1, −1)` with `F = fracEven wd`: `lastPosOf (hStringAt (hWordOf wd true) 0) = texV1Even F − (1, 1)`
(`StdCornerAnchors.stdAnchorX_even`), `lastPosOf (vStringAt (vWordOf wd true) 0) = texV2 F + (1, −1)` (`GlueStringDecomp.lp_right_even`),
and `shR q = (1, 1)`. So every point of `vMinus` at `0` is reflected to `D − z` on `vPlus` (`vMinus_to_vPlus`), and the even-first
midpoint `m` gives `D − m` on `vPlus` (`mid_vPlus`). -/

namespace FLatticePaper.Tiles.VPlusReflect

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.VertStringReflect
  FLatticePaper.Tiles.ReflectedCover FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.StdCornerAnchors
  FLatticePaper.Tiles.GlueStringDecomp FLatticePaper.Tiles.StringCorners FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.Standard

/-- Each tile shape of a zero-one tile is symmetric under its half-turn `s ↦ sT t − s`. -/
theorem tileShape_refl (t : ZTile) (ht : t ≠ ZTile.oneD) (s : GInt) (hs : s ∈ tileShape t) :
    sT t - s ∈ tileShape t := by
  cases t with
  | zero =>
    simp only [tileShape, sT, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | one =>
    simp only [tileShape, sT, List.mem_cons, List.mem_nil_iff, or_false] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  | oneD => exact absurd rfl ht

/-- The letters of a vertical string are never the enlarged tile. -/
theorem vStringAt_ne_oneD (w : BinaryWord) (c : GInt) (Q : ZTile × GInt) (hQ : Q ∈ vStringAt w c) :
    Q.1 ≠ ZTile.oneD := by
  obtain ⟨t, p⟩ := Q
  have h := (List.of_mem_zip hQ).1
  obtain ⟨l, -, hl⟩ := List.mem_map.mp h
  rw [← hl]
  cases l <;> simp [letterZTile]

/-- **The reflection of a point of the reversed vertical string, at the origin.** For a word `v ++ [x]`, a point `z` of the
reversed vertical string at `(0, 0)` is sent by `K − z` to a point of the forward vertical string at `a`, where
`K = a + lastPosOf (vStringAt (v ++ [x]) (0, 0)) + shR x`. -/
theorem vRev_reflect_points (v : BinaryWord) (x : Letter) (a z : GInt)
    (hz : z ∈ placedSites (vRevStringAt (v ++ [x]).reverse (0, 0))) :
    a + lastPosOf (vStringAt (v ++ [x]) (0, 0)) + shR x - z ∈ placedSites (vStringAt (v ++ [x]) a) := by
  have h := vRev_reflect_gen v x a (0, 0)
  rw [h] at hz
  unfold placedSites at hz ⊢
  rw [List.mem_flatMap] at hz ⊢
  obtain ⟨T, hT, hzT⟩ := hz
  rw [List.mem_reverse, List.mem_map] at hT
  obtain ⟨Q, hQ, hTQ⟩ := hT
  rw [List.mem_map] at hzT
  obtain ⟨s, hs, hsz⟩ := hzT
  subst hTQ
  refine ⟨Q, hQ, ?_⟩
  rw [List.mem_map]
  dsimp only at hs hsz ⊢
  refine ⟨sT Q.1 - s, tileShape_refl Q.1 (vStringAt_ne_oneD _ _ Q hQ) s hs, ?_⟩
  rw [← hsz]
  simp only [add_zero, Prod.mk_zero_zero]
  abel

/-- **The half-turn of the vertical side `vMinus` lies on `vPlus`.** For the even register `F = fracEven wd` the constant is
`D = texV1Even F + texV2 F + (1, −1)`: a point of `vMinus` at `0` is sent to `D − z`, a point of `vPlus`. -/
theorem vMinus_to_vPlus (wd : Word) (z : GInt)
    (hz : z ∈ placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vMinus)) :
    texV1Even (fracEven wd) + texV2 (fracEven wd) + ((1 : ℤ), (-1 : ℤ)) - z ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vPlus) := by
  obtain ⟨v, hv⟩ := List.getLast?_eq_some_iff.mp (vWord_even_head_last wd).2
  have hz' : z ∈ placedSites (vRevStringAt (vWordOf wd true).reverse (0, 0)) := hz
  rw [hv] at hz'
  have key := vRev_reflect_points v Letter.q (lastPosOf (hStringAt (hWordOf wd true) (0, 0))) z hz'
  rw [← hv] at key
  have ha := stdAnchorX_even wd
  have hl : lastPosOf (vStringAt (vWordOf wd true) (0, 0)) = texV2 (fracEven wd) + ((1 : ℤ), (-1 : ℤ)) := by
    rw [lp_right_even wd (0, 0)]
    ext <;> simp
  have hq : shR Letter.q = ((1 : ℤ), (1 : ℤ)) := rfl
  rw [ha, hl, hq] at key
  show texV1Even (fracEven wd) + texV2 (fracEven wd) + ((1 : ℤ), (-1 : ℤ)) - z ∈
    placedSites (vStringAt (vWordOf wd true) (lastPosOf (hStringAt (hWordOf wd true) (0, 0))))
  rw [ha]
  have e : texV1Even (fracEven wd) + texV2 (fracEven wd) + ((1 : ℤ), (-1 : ℤ)) - z =
      texV1Even (fracEven wd) - ((1 : ℤ), (1 : ℤ)) + (texV2 (fracEven wd) + ((1 : ℤ), (-1 : ℤ))) +
        ((1 : ℤ), (1 : ℤ)) - z := by abel
  rw [e]
  exact key

/-- **The even-first companion of the midpoint (`mid_vPlus`).** The point `D − m`, with `D = texV1Even q + texV2 q + (1, −1)` for the
even register `q` of `wd ++ [three]` and `m` the midpoint on `vMinus` (`EvenMidVMinus.mid_vMinus`), is a site of the side `vPlus`. -/
theorem mid_vPlus (wd : Word) (hn : ¬ IsBase (wd ++ [Digit.three])) (hW : W1Odd (wd ++ [Digit.three]) = false) (m : ℤ × ℤ)
    (hm : (2 : ℤ) • m = texV2 (parentsAt (wd ++ [Digit.three])).odd + texV2 (parentsAt (wd ++ [Digit.three])).even +
      ((1 : ℤ), (-1 : ℤ))) :
    texV1Even (parentsAt (wd ++ [Digit.three])).even + texV2 (parentsAt (wd ++ [Digit.three])).even +
      ((1 : ℤ), (-1 : ℤ)) - m ∈
      placedSites (sideString (hWordOf wd true) (vWordOf wd true) 0 Side.vPlus) := by
  have hmin := EvenMidVMinus.mid_vMinus wd hn hW m hm
  have hE : (parentsAt (wd ++ [Digit.three])).even = fracEven wd := by
    rw [parentsAt_append_singleton]
    rfl
  rw [hE]
  exact vMinus_to_vPlus wd m hmin

end FLatticePaper.Tiles.VPlusReflect
