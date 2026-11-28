import FLatticePaper.Tiles.AltLatticeOddWFamily
import FLatticePaper.Tiles.AltSevenFamily

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`, odd alternate child along `W`, from the family

At an uncorrected word `u x` (`x = 1, 3`), an odometer respecting the decomposition `tileAltOddPieces` over the family below the
word, on the printed alternate tile, is lattice self-compatible along `W = v_{p₀,2}` with the factor `a_{p₀,2}`: the parents'
data come from the family (`AltSevenFamily.regOdd_data`, `regEven_data` for the standard parents, `alt_parent_data` for the
alternate parent), and `AltLatticeOddWMain.odd_W_parents` concludes. -/

namespace FLatticePaper.Tiles.AltLatticeOddWWrap

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (JointData JSlice FirstTileNormal)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)

/-- The corner value at the origin fixes the constant of the normalisation. -/
theorem first_normal_of_corners (o : PartialOdometer) (β β' : ℤ) (X Y e : Site)
    (hc : TileTranslation.StdCornerValues o 0 β X Y e) (hN : FirstTileNormal o 0 β') : FirstTileNormal o 0 β := by
  have h1 := (hN 0 (by simp only [tileShape]; exact List.mem_cons_self)).2
  have h2 := hc.1.2
  simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero] at h1 h2
  have h0 : zTileOdo ZTile.one 0 = 0 := by simp [zTileOdo, oneOdometer, Prod.ext_iff]
  have e : β' = β := by linarith
  rw [← e]; exact hN

/-- The odd standard parent `u` of the family is `β` on the bottom walk of `T(p₀(u))`, in overlap form. -/
theorem std_bottom_odd (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) (β : ℤ)
    (hc : TileTranslation.StdCornerValues (f u).tOdd 0 β (texV1Odd (fracOdd u)) (texV2 (fracOdd u))
      ((fracOdd u).num, -(fracOdd u).den)) :
    ∀ y, y ∈ oddTile u → y + texV2 (fracOdd u) ∈ oddTile u → (f u).tOdd.val y = β := by
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨β', hN⟩ := sl.1
  have hRA := (hg u hu).1.2.2.1.2.2.2.2.1
  exact AltLatticeOddWFamily.bot_odd u _ β hRA.2.1 (first_normal_of_corners _ _ _ _ _ _ hc hN)

/-- The even standard parent `u` of the family is `β` on the bottom walk of `T(q₀(u))`, in overlap form. -/
theorem std_bottom_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (u : Word) (hu : u.length < n) (β : ℤ)
    (hc : TileTranslation.StdCornerValues (f u).tEven 0 β (texV1Even (fracEven u)) (texV2 (fracEven u))
      ((fracEven u).num, -(fracEven u).den)) :
    ∀ y, y ∈ evenTile u → y + texV2 (fracEven u) ∈ evenTile u → (f u).tEven.val y = β := by
  have sl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv hu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨β', hN⟩ := sl.2.1
  have hRA := (hg u hu).1.2.2.1.2.2.2.2.2.1
  exact AltLatticeOddWFamily.bot_even u _ β hRA.2.1 (first_normal_of_corners _ _ _ _ _ _ hc hN)

set_option maxHeartbeats 400000 in
/-- **Item (b) of `lemma:weak_alternate_odometer_properties` for the odd alternate child along `v_{p₀,2}`, from the family**
(words `u x` with `x = 1, 3`, the text data): an odometer respecting the decomposition `tileAltOddPieces` over the family below
the word, defined on the printed odd alternate tile, is lattice self-compatible along `v_{p₀,2}` with the factor `a_{p₀,2}`
(the second half of `JointFamily.AltLatticeOdd`). -/
theorem odd_W_family (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (hAB : JointFamily.PaperAltBdry D) (hAnc : JointFamily.PaperAltAnc D) (f : Word → JSlice) (u : Word) (xd : Digit)
    (hx : xd ≠ Digit.two) (hw : ¬ IsBase (u ++ [xd])) (hg : GoodBelow D f (u ++ [xd]).length) (o : PartialOdometer)
    (hR : JointFamily.RespectsPieces o (JointFamily.tileAltOddPieces D.S (fun v => (JointFamily.below f (u ++ [xd]) v).tOdd) (fun v => (JointFamily.below f (u ++ [xd]) v).tEven) (fun v => (JointFamily.below f (u ++ [xd]) v).aOdd) (fun v => (JointFamily.below f (u ++ [xd]) v).aEven)
      (fun v => (JointFamily.below f (u ++ [xd]) v).lOdd) (u ++ [xd])))
    (hdom : o.dom = altOddTile AltRotStep.B (u ++ [xd])) :
    JointFamily.LatticeSelfCompatible o (texV2 ((parentsAt (u ++ [xd])).current .odd))
      (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true) := by
  rw [AltLatticeOddWFamily.tileAltOdd_eq _ _ _ _ _ _ u xd hx] at hR
  obtain ⟨⟨u1, h1⟩, -⟩ := JointRot.regs_some _ hw
  have h2 := AltLatticeOddWFamily.regs2_snoc u xd hx
  have l1 := JointInduction.regsAt_lt _ u1 (Or.inl h1)
  have lu : u.length < (u ++ [xd]).length := by simp
  rw [h1, SurgicalWeak.regOdo, JointRot.below_of_lt f _ _ l1, JointRot.below_of_lt f _ _ lu] at hR
  obtain ⟨βP, hdP0, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
  obtain ⟨βQ, hdQ0, hcQ, hhQ⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u lu
  have hsl := JointRot.family_slopes D f u.length (fun v hv => (hg v (lt_of_le_of_lt hv lu)).1)
    (JointRot.baseSlopes_paper D hS hA) u le_rfl
  obtain ⟨βH, hdH, h0, HH, botH⟩ :=
    AltLatticeOddWFamily.alt_parent_data D hAB f u (hg u lu).1 (hg u lu).2 hsl.2.2.2 (hAnc u).1
  have hp : (parentsAt (u ++ [xd])).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents _).1 u1 h1
  have hq : (parentsAt (u ++ [xd])).even = fracEven u := (WeakStepAssembly.regsAt_parents _).2 u h2
  have htP : (stateAt (u ++ [xd])).tOdd = oddTile u1 := (WeakStepPaper.regsAt_tiles _).1 u1 h1
  have htQ : (stateAt (u ++ [xd])).tEven = evenTile u := (WeakStepPaper.regsAt_tiles _).2.2.1 u h2
  have botP0 := std_bottom_odd D hS hA f _ hg u1 l1 βP hcP
  have botQ0 := std_bottom_even D hS hA f _ hg u lu βQ hcQ
  have e : AltItem4.latV (u ++ [xd]) false 0 1 = texV2 ((parentsAt (u ++ [xd])).current .odd) := by
    ext <;> simp [AltItem4.latV, AltItem4.fracOf, SiteInduction.curO]
  rw [← e]
  refine AltLatticeOddWMain.odd_W_parents u xd hx hw (f u1).tOdd (f u).tEven (f u).aEven (by rw [hdP0, htP])
    (by rw [hdQ0, htQ]) hdH h0 ?_ ?_ HH βP βQ βH ?_ ?_ ?_ ?_ ?_ ?_ ?_ o hR hdom
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
  · intro y a b
    rw [htQ] at a
    rw [htQ, hq] at b
    exact botH y a b
  · have c := hcP.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero] at c
    linarith
  · have c := hcP.2.2.2.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at c
    rw [hp]; linarith
  · have c := hcQ.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, sub_zero] at c
    linarith
  · have c := hcQ.2.2.2.1.2
    simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at c
    rw [hq]; linarith

end FLatticePaper.Tiles.AltLatticeOddWWrap
