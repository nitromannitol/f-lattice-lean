import FLatticePaper.Tiles.PaperAltDomains
import FLatticePaper.Tiles.AltStairRespects
import FLatticePaper.Tiles.NearStairVerticalRespects
import FLatticePaper.Tiles.GlueChain
import FLatticePaper.Tiles.RespectsTranslate
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseAltLattice

/-! # The alternate base odometers at the empty word (`BaseWeakAltInput`, the word `[]`)

The odd alternate child of `[]` is the near-stair alternate `paperNearStairAltTile 3`, read at the shift `(0,1)`; its half string
`w_v = p q` is the vertical string of `pqWord 0`, respected by `pq_respectsPartialV 0` at the lower-left point `(0,1)`, and the
translate by `(0,-1)` respects it at the anchor `(0,0)` (`RespectsHalfV`). The even alternate child is the stair alternate
`paperStairAltTile 3` read at `0`, whose half string `w_h = q p` is respected by `altStair_respectsPartialHAt 0` at `(0,0)`
(`RespectsHalfH`). The lattice clauses are `BaseAltLattice` at `k = 0`. -/

namespace FLatticePaper.Tiles.BaseAltEmpty

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.PaperAltDomains
open FLatticePaper.Tiles.PaperAltBase (paperAltBaseTiles)
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.JointFamily (WeakAltPropsU AltLatticeOddV2 AltLatticeEvenV2 LatticeSelfCompatible)
open FLatticePaper.Tiles.BaseWeakLattice
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.BaseAltLattice (altLattice_stair altLattice_nearStair)
open FLatticePaper.Tiles.GlueChain (vRevStringAt_shift vStringAt_shift)
open FLatticePaper.Tiles.AltRotStep (isLowerLeftPt_unique)

/-- The odd alternate odometer of `[]`: the odd alternate base tile, with the paper value read at `x + (0,1)`. -/
noncomputable def oddO : PartialOdometer :=
  ⟨SurgicalAltTiles.altOddTile paperAltBaseTiles [], fun x => paperNearStairAltValue 3 (x + ((0 : ℤ), (1 : ℤ)))⟩

/-- The even alternate odometer of `[]`: the even alternate base tile, with the paper value. -/
noncomputable def evenE : PartialOdometer :=
  ⟨SurgicalAltTiles.altEvenTile paperAltBaseTiles [], fun x => paperStairAltValue 3 x⟩

theorem oddO_mem (x : GInt) : x ∈ oddO.dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile 3 := by
  show x ∈ SurgicalAltTiles.altOddTile paperAltBaseTiles [] ↔ _
  rw [altOddTile_base [] (Or.inl rfl)]
  simp only [paperAltBaseTiles, if_true]
  rw [mem_shift_down, nearStairAltF_iff 3 le_rfl]

theorem evenE_mem (x : GInt) : x ∈ evenE.dom ↔ x ∈ paperStairAltTile 3 := by
  show x ∈ SurgicalAltTiles.altEvenTile paperAltBaseTiles [] ↔ _
  rw [altEvenTile_base [] (Or.inl rfl)]
  simp only [paperAltBaseTiles, if_true]
  rw [stairAltF_iff 3 le_rfl]

/-- The empty word satisfies the alternate base condition, with the odometers of this file. -/
theorem paperAltBaseCond_empty : PaperAltBaseCond [] oddO evenE := by
  refine ⟨fun _ => ⟨fun x => oddO_mem x, fun x _ => rfl, fun x => evenE_mem x, fun x _ => rfl⟩, ?_, ?_⟩
  · intro k hk h
    have := congrArg List.length h
    simp at this
    omega
  · intro k hk h
    have := congrArg List.length h
    simp at this
    omega

/-- **`RespectsHalfV` at the empty word.** The reversed vertical string `pqWord 0` at the anchor `(0,0)`, and the forward string
translated from `(2,3)`-type anchor, respected by `oddO.val`. -/
theorem respectsHalfV_empty (anc : AltAnchors) (h0 : anc.cHat [] false = 0) :
    RespectsHalfV (altRevVAnchor anc []) (FLatticePaper.Tiles.SiteStrings.vWordOf [] false) oddO.val := by
  have hA : altRevVAnchor anc [] = ((0 : ℤ), (0 : ℤ)) := by
    unfold altRevVAnchor altOffsetS
    simp [h0, FLatticePaper.Farey.phase]
  have hw : FLatticePaper.Tiles.SiteStrings.vWordOf [] false = pqWord 0 := by decide
  rw [hA, hw]
  unfold RespectsHalfV
  obtain ⟨c, hLL, c', -, hrev, hfwd⟩ := pq_respectsPartialV 0
  have e3 : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
  rw [e3] at hrev hfwd
  have hc : c = ((0 : ℤ), (1 : ℤ)) := isLowerLeftPt_unique hLL (pq_lowerLeft 0)
  subst hc
  have hf : (fun x => paperNearStairAltValue 3 (x - ((0 : ℤ), (-1 : ℤ)))) = oddO.val := by
    funext x
    simp only [oddO]
    congr 1
  have hT := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hrev
  rw [vRevStringAt_shift, show ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) by ext <;> simp] at hT
  rw [hf] at hT
  refine ⟨hT, c' + ((0 : ℤ), (-1 : ℤ)), ?_⟩
  have hT2 := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hfwd
  rw [vStringAt_shift, hf] at hT2
  exact hT2

/-- **`RespectsHalfH` at the empty word.** The forward string `stairH 0 = q p` at `(0,0)`, and the reversed one at the anchor of
`altStair_respectsPartialHAt 0`. -/
theorem respectsHalfH_empty (anc : AltAnchors) (h0 : anc.cHat [] true = 0) :
    RespectsHalfH (altFwdHAnchor anc []) (FLatticePaper.Tiles.SiteStrings.hWordOf [] true) evenE.val := by
  have hA : altFwdHAnchor anc [] = ((0 : ℤ), (0 : ℤ)) := by
    unfold altFwdHAnchor
    rw [h0]
    rfl
  have hw : FLatticePaper.Tiles.SiteStrings.hWordOf [] true = stairH 0 := by decide
  rw [hA, hw]
  unfold RespectsHalfH
  obtain ⟨c', -, hf, hr⟩ := altStair_respectsPartialHAt 0
  have e3 : (2 * ((0 : ℕ) : ℤ) + 3) = 3 := by norm_num
  rw [e3] at hf hr
  exact ⟨hf, c', hr⟩

/-- **The weak alternate lattice clauses at the empty word** (`WeakAltPropsU`). -/
theorem weakAltPropsU_empty : WeakAltPropsU [] oddO evenE := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · unfold AltLatticeOddV2
    have hp : (parentsAt ([] : Word)).current .odd = ⟨1, 2⟩ := by
      have h := cur_odd_three 0
      simpa using h
    show LatticeSelfCompatible oddO (texV2 ((parentsAt ([] : Word)).current .odd))
      (offsetA ((parentsAt ([] : Word)).current .odd).num ((parentsAt ([] : Word)).current .odd).den true)
    rw [hp]
    have key := altLattice_nearStair 0 oddO
      (fun x => by rw [oddO_mem x]; norm_num) (fun x _ => rfl)
    simpa using key
  · unfold AltLatticeEvenV2
    have hq : (parentsAt ([] : Word)).current .even = ⟨1, 3⟩ := by
      have h := cur_even_three 0
      simpa using h
    show LatticeSelfCompatible evenE (texV2 ((parentsAt ([] : Word)).current .even))
      (offsetA ((parentsAt ([] : Word)).current .even).num ((parentsAt ([] : Word)).current .even).den true)
    rw [hq]
    have key := altLattice_stair 0 evenE
      (fun x => by rw [evenE_mem x]; norm_num) (fun x _ => rfl)
    simpa using key

end FLatticePaper.Tiles.BaseAltEmpty
