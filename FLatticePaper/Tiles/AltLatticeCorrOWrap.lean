import FLatticePaper.Tiles.AltLatticeCorrOMain
import FLatticePaper.Tiles.AltLatticeCorrEWrap

/-! # Item (b) of `lemma:weak_alternate_odometer_properties` at the corrected odd child, from the family

At `w = u 2` the odd alternate tile odometer is the decomposition `tileAltOddPieces` with the elongated odd L-corrections of
`u` in place of `T(p₁)^{+,2}` (`o^{L,-}`) and `T(p₁)^{-,1}` (`o^{L,+}`). Their agreement with `o_{p₁}` (`LSidesAgree`,
`lemma:l_correct_existence`) is used on the bottom string `w_h` (`o^{L,-}`), on the reversed string `rev w_h` at the top
(`o^{L,+}`), and at one point of the reversed vertical string `rev w_v` (`JointRot.side_vMinus`). With the half-turn (b) of the
odd alternate tile odometer and slope zero (`JointRot.slope_tileAltOdd`), it is lattice self-compatible along `v_{p₀,2}`. -/

namespace FLatticePaper.Tiles.AltLatticeCorrOWrap

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (JointData JSlice FirstTileNormal stdPiece altOff altAff W1Odd)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

/-- **The decomposition of the odd alternate tile odometer at `u 2`** is `pieces6c`: the L-corrections of `u` on
`T(p₁)^{+,2}` and `T(p₁)^{-,1}`, and no alternate parent piece. -/
theorem tileAltOdd_eq2 (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer)
    (lO : Word → Bool → Bool → PartialOdometer) (u : Word) :
    JointFamily.tileAltOddPieces S pO pE aO aE lO (u ++ [Digit.two]) =
      AltLatticeCorrOMain.pieces6c (u ++ [Digit.two]) (pO u)
        (SurgicalWeak.regOdo S pO pE (SurgicalWeak.regsAt (u ++ [Digit.two])).2 false) (lO u false true) (lO u true true) := by
  have hc : decide ((u ++ [Digit.two]).getLast? = some Digit.two) = true := by simp
  have ht : (SurgicalAlt.altTypeOf (u ++ [Digit.two])).bind
      (fun ty => SurgicalAlt.altQ1Coeff (JointFamily.W1Odd (u ++ [Digit.two])) ty) = none := by
    rw [AltRotStep.altTypeOf_snoc]
    simp [SurgicalAlt.altQ1Coeff]
  simp only [JointFamily.tileAltOddPieces, hc, ConnectedAltL.regs_snoc_two, ht, SurgicalWeak.regOdo, if_true,
    List.dropLast_concat, AltLatticeCorrOMain.pieces6c, List.append_nil]

/-- A point of the bottom walk of `T(p₀(u))`, in overlap form, lies on the string `w_h` at the origin. -/
theorem bottom_on_hPlus (u : Word) (y : Site) (h1 : y ∈ oddTile u) (h2 : y + texV2 (fracOdd u) ∈ oddTile u) :
    y ∈ placedSites (hStringAt (hWordOf u false) 0) := by
  have hb := OverlapSides.odd_bottom_of_overlap u y h1 (by rwa [sub_neg_eq_add])
  exact (StdPseudoAnchoredSets.placed_hStringAt_iff _ y).2 (HBottom.hB_odd u y hb)

/-- The half-turn image `A + B + (1,-1) - y` of a point `y` of the bottom walk lies on the reversed string `rev w_h` placed at
the end of `rev w_v` (the top side). -/
theorem top_on_hMinus (u : Word) (y : Site) (h1 : y ∈ oddTile u) (h2 : y + texV2 (fracOdd u) ∈ oddTile u) :
    texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) - y ∈
      placedSites (hRevStringAt (hWordOf u false).reverse (lastPosOf (vRevStringAt (vWordOf u false).reverse 0))) := by
  rw [ReflectedCoverConverse.placed_hRev_iff (hWordOf u false) .p (hWordOf_head_last u false).2,
    StdCornerAnchors.stdAnchorY_odd, StdCornerAnchors.stdAnchorX_odd]
  have e : texV2 (fracOdd u) + ((1 : ℤ), (-2 : ℤ)) + (texV1Odd (fracOdd u) - ((1 : ℤ), (1 : ℤ))) + ReflectedCover.shR .p -
      (texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) - y) = y := by
    show texV2 (fracOdd u) + ((1 : ℤ), (-2 : ℤ)) + (texV1Odd (fracOdd u) - ((1 : ℤ), (1 : ℤ))) + ((1 : ℤ), (2 : ℤ)) -
      (texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) - y) = y
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [e]
  exact bottom_on_hPlus u y h1 h2

/-- The two pins on the reversed vertical string `rev w_v` at the origin: `1` and `B + 1`. -/
theorem pins (u : Word) : ((1 : ℤ), (0 : ℤ)) ∈ placedSites (vRevStringAt (vWordOf u false).reverse 0) ∧
    texV2 (fracOdd u) + ((1 : ℤ), (0 : ℤ)) ∈ placedSites (vRevStringAt (vWordOf u false).reverse 0) :=
  JointRot.side_vMinus (vWordOf u false) (texV2 (fracOdd u)) (StringCorners.vertWord_head_last u).1
    (StringCorners.vertWord_head_last u).2 (StdCornerAnchors.stdAnchorY_odd u)

set_option maxHeartbeats 400000 in
/-- **Item (b) at the corrected odd child, along `v_{p₀,2}`, from the family** (`w = u 2`, the text data): an odometer
respecting `tileAltOddPieces` over the family below `w`, on the printed odd alternate tile, with the half-turn (b) of the odd
alternate tile odometer, is lattice self-compatible along `v_{p₀,2}` with the factor `a_{p₀,2}`. -/
theorem odd_W_corr_family (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hlS : D.lSides = JointFamily.paperLSides) (f : Word → JSlice) (u : Word) (hw : ¬ IsBase (u ++ [Digit.two]))
    (hg : GoodBelow D f (u ++ [Digit.two]).length) (o : PartialOdometer)
    (hR : JointFamily.RespectsPieces o (JointFamily.tileAltOddPieces D.S (fun v => (JointFamily.below f (u ++ [Digit.two]) v).tOdd)
      (fun v => (JointFamily.below f (u ++ [Digit.two]) v).tEven) (fun v => (JointFamily.below f (u ++ [Digit.two]) v).aOdd)
      (fun v => (JointFamily.below f (u ++ [Digit.two]) v).aEven) (fun v => (JointFamily.below f (u ++ [Digit.two]) v).lOdd)
      (u ++ [Digit.two])))
    (hdom : o.dom = altOddTile AltRotStep.B (u ++ [Digit.two]))
    (hHT : JointFamily.AltHalfTurn o (JointFamily.altD (u ++ [Digit.two]) true) (JointFamily.altE (u ++ [Digit.two]))) :
    JointFamily.LatticeSelfCompatible o (texV2 ((parentsAt (u ++ [Digit.two])).current .odd))
      (offsetA ((parentsAt (u ++ [Digit.two])).current .odd).num ((parentsAt (u ++ [Digit.two])).current .odd).den true) := by
  have lu : u.length < (u ++ [Digit.two]).length := by simp
  have h1 : (SurgicalWeak.regsAt (u ++ [Digit.two])).1 = some u := ConnectedAltL.regs_snoc_two u
  obtain ⟨-, ⟨u2, h2⟩⟩ := JointRot.regs_some _ hw
  have l2 := JointInduction.regsAt_lt _ u2 (Or.inr h2)
  -- slope zero and the normalised half-turn
  have sl := fun (k : Word) (hk : k.length < (u ++ [Digit.two]).length) => JointRot.family_slopes D f k.length
    (fun v hv => (hg v (lt_of_le_of_lt hv hk)).1) (JointRot.baseSlopes_paper D hS hA) k le_rfl
  have hs : JointRot.SlopeZero o := by
    refine JointRot.slope_tileAltOdd _ _ _ _ _ _ (u ++ [Digit.two]) o hR ?_ ?_
    · rw [h1]; show JointRot.SlopeZero (JointFamily.below f (u ++ [Digit.two]) u).tOdd
      rw [JointRot.below_of_lt f _ _ lu]; exact (sl u lu).1
    · rw [h2]; show JointRot.SlopeZero (JointFamily.below f (u ++ [Digit.two]) u2).tEven
      rw [JointRot.below_of_lt f _ _ l2]; exact (sl u2 l2).2.1
  have HT := AltLatticeCorrEWrap.halfTurnId_of_alt o _ _ hHT hs
  rw [AltLatticeEvenV.altD_true] at HT
  -- the pieces
  rw [tileAltOdd_eq2, h2, SurgicalWeak.regOdo, JointRot.below_of_lt f _ _ l2, JointRot.below_of_lt f _ _ lu] at hR
  -- the L-corrections of `u` and their sides
  have hdef : JointFamily.OddLDefined u := by
    refine JointRot.oddLDefined_of_mem _ ?_
    by_contra hc
    refine hw (Or.inr (Or.inr fun d hd => ?_))
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · by_contra hne
      exact hc ⟨d, hd, hne⟩
    · rfl
  obtain ⟨-, -, cm, hcm⟩ := (hg u lu).1.2.2.2.1 false true hdef
  obtain ⟨-, -, cp, hcp⟩ := (hg u lu).1.2.2.2.1 true true hdef
  have hW : W1Odd (u ++ [Digit.two]) = W1Odd u := AltRotStep.phase_snoc_two u
  have smh : Side.hPlus ∈ D.lSides true (W1Odd u) false true := by
    rw [hlS]; cases W1Odd u <;> simp [JointFamily.paperLSides]
  have sph : Side.hMinus ∈ D.lSides true (W1Odd u) true true := by
    rw [hlS]; cases W1Odd u <;> simp [JointFamily.paperLSides]
  have smv : W1Odd u = true → Side.vMinus ∈ D.lSides true (W1Odd u) false true := by
    intro h; rw [hlS, h]; simp [JointFamily.paperLSides]
  have spv : W1Odd u = false → Side.vMinus ∈ D.lSides true (W1Odd u) true true := by
    intro h; rw [hlS, h]; simp [JointFamily.paperLSides]
  -- the parents
  obtain ⟨βP, hdP0, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u lu
  obtain ⟨βQ, hdQ0, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
  have hp : (parentsAt (u ++ [Digit.two])).odd = fracOdd u := (WeakStepAssembly.regsAt_parents _).1 u h1
  have hq : (parentsAt (u ++ [Digit.two])).even = fracEven u2 := (WeakStepAssembly.regsAt_parents _).2 u2 h2
  have htP : (stateAt (u ++ [Digit.two])).tOdd = oddTile u := (WeakStepPaper.regsAt_tiles _).1 u h1
  have htQ : (stateAt (u ++ [Digit.two])).tEven = evenTile u2 := (WeakStepPaper.regsAt_tiles _).2.2.1 u2 h2
  have botP0 := AltLatticeOddWWrap.std_bottom_odd D hS hA f _ hg u lu βP hcP
  have botQ0 := AltLatticeOddWWrap.std_bottom_even D hS hA f _ hg u2 l2 βQ hcQ
  have hCp : AltGlueOdd.Cp (u ++ [Digit.two]) = texV1Odd (fracOdd u) + texV2 (fracOdd u) + ((1 : ℤ), (-1 : ℤ)) := by
    simp only [AltGlueOdd.Cp, hp]
  have e : AltItem4.latV (u ++ [Digit.two]) false 0 1 = texV2 ((parentsAt (u ++ [Digit.two])).current .odd) := by
    ext <;> simp [AltItem4.latV, AltItem4.fracOf, SiteInduction.curO]
  rw [← e]
  refine AltLatticeCorrOMain.odd_W_corr u hw (f u).tOdd (f u2).tEven ((f u).lOdd false true) ((f u).lOdd true true)
    (by rw [hdP0, htP]) (by rw [hdQ0, htQ]) ?_ ?_ βP βQ cm cp ?_ ?_ ?_ ?_ ?_ ?_ o hR hdom _ HT
  · intro z hz
    obtain ⟨m, eq⟩ := hhP z hz
    simp only [AltGlueOdd.Cp, JointFamily.aP2, hp, offsetA]
    exact ⟨m, eq⟩
  · intro z hz
    obtain ⟨m, eq⟩ := hhQ z hz
    simp only [AltGlueOdd.Cq, JointFamily.aQ2, hq, offsetA]
    exact ⟨m, eq⟩
  · intro y a b
    rw [htP] at a
    rw [htP, hp] at b
    exact botP0 y a b
  · intro y a b
    rw [htQ] at a
    rw [htQ, hq] at b
    exact botQ0 y a b
  · -- `o^{L,-}` on the bottom walk
    intro y a b
    rw [htP] at a
    rw [htP, hp] at b
    obtain ⟨m, -, ev⟩ := hcm _ smh y (bottom_on_hPlus u y a b)
    exact ⟨m, ev⟩
  · -- `o^{L,-}` at `B + 1` when `W₁` is odd
    intro hph
    have hu : W1Odd u = true := by rw [← hW]; simpa [W1Odd] using hph
    rw [hp]
    obtain ⟨m, -, ev⟩ := hcm _ (smv hu) _ (pins u).2
    exact ⟨m, ev⟩
  · -- `o^{L,+}` on the top walk
    intro y a b
    rw [htP] at a
    rw [htP, hp] at b
    rw [hCp]
    obtain ⟨m, -, ev⟩ := hcp _ sph _ (top_on_hMinus u y a b)
    exact ⟨m, ev⟩
  · -- `o^{L,+}` at `1` when `W₁` is even
    intro hph
    have hu : W1Odd u = false := by rw [← hW]; simpa [W1Odd] using hph
    obtain ⟨m, -, ev⟩ := hcp _ (spv hu) _ (pins u).1
    exact ⟨m, ev⟩

end FLatticePaper.Tiles.AltLatticeCorrOWrap
