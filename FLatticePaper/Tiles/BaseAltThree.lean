import FLatticePaper.Tiles.PaperAltDomains
import FLatticePaper.Tiles.AltStairRespects
import FLatticePaper.Tiles.LadderVerticalRespects
import FLatticePaper.Tiles.BaseHpStair
import FLatticePaper.Tiles.SpecialCells
import FLatticePaper.Tiles.GlueChain
import FLatticePaper.Tiles.RespectsTranslate
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseAltLattice

/-! # The alternate base odometers at the words `3^k`, `k ≥ 1` (`BaseWeakAltInput`)

The odd alternate child of `3^k` is the ladder alternate `paperLadderAltTile (2k+2)`, read at `x - (1,1)`; its vertical half string
`w_v = p^{2k+1} q` is respected by `lv_respectsPartialV` at the lower-left point `(-1,-1)`, and the translate by `(1,1)` respects
it at the anchor `(0,0)`. The even alternate child is the stair alternate `paperStairAltTile (2k+3)`, read at `0`, whose half string
`w_h = q p^{k+1}` is respected by `altStair_respectsPartialHAt k` at `(0,0)`. The lattice clauses are `BaseAltLattice`. -/

namespace FLatticePaper.Tiles.BaseAltThree

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase mem_shift)
open FLatticePaper.Tiles.PaperAltDomains
open FLatticePaper.Tiles.PaperAltBase (paperAltBaseTiles)
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.JointFamily (WeakAltPropsU AltLatticeOddV2 AltLatticeEvenV2 LatticeSelfCompatible)
open FLatticePaper.Tiles.BaseWeakLattice
open FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.BaseAltLattice (altLattice_stair altLattice_ladder)
open FLatticePaper.Tiles.GlueChain (vRevStringAt_shift vStringAt_shift)
open FLatticePaper.Tiles.AltRotStep (isLowerLeftPt_unique)

/-- The odd alternate odometer of `3^k`: the ladder alternate `paperLadderAltTile (2k+2)`, read at `x - (1,1)`. -/
noncomputable def oddT (k : ℕ) : PartialOdometer :=
  ⟨SurgicalAltTiles.altOddTile paperAltBaseTiles (List.replicate k Digit.three),
    fun x => paperLadderAltValue (2 * (k : ℤ) + 2) (x - ((1 : ℤ), (1 : ℤ)))⟩

/-- The even alternate odometer of `3^k`: the stair alternate `paperStairAltTile (2k+3)`, read at `x`. -/
noncomputable def evenT (k : ℕ) : PartialOdometer :=
  ⟨SurgicalAltTiles.altEvenTile paperAltBaseTiles (List.replicate k Digit.three),
    fun x => paperStairAltValue (2 * (k : ℤ) + 3) x⟩

theorem sub11_eq (x : GInt) : x - ((1 : ℤ), (1 : ℤ)) = x + ((-1 : ℤ), (-1 : ℤ)) := by
  ext <;> simp [sub_eq_add_neg]

theorem replicate_three_ne_nil (k : ℕ) (hk : 1 ≤ k) : List.replicate k Digit.three ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem oddT_mem (k : ℕ) (hk : 1 ≤ k) (x : GInt) :
    x ∈ (oddT k).dom ↔ x - ((1 : ℤ), (1 : ℤ)) ∈ paperLadderAltTile (2 * (k : ℤ) + 2) := by
  show x ∈ SurgicalAltTiles.altOddTile paperAltBaseTiles (List.replicate k Digit.three) ↔ _
  rw [altOddTile_base _ (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))]
  have h0 := replicate_three_ne_nil k hk
  simp only [paperAltBaseTiles, if_neg h0, List.length_replicate, if_true]
  rw [mem_shift, ladderAltF_iff _ (by omega)]

theorem evenT_mem (k : ℕ) (hk : 1 ≤ k) (x : GInt) :
    x ∈ (evenT k).dom ↔ x ∈ paperStairAltTile (2 * (k : ℤ) + 3) := by
  show x ∈ SurgicalAltTiles.altEvenTile paperAltBaseTiles (List.replicate k Digit.three) ↔ _
  rw [altEvenTile_base _ (Or.inr (Or.inl fun d hd => List.eq_of_mem_replicate hd))]
  have h0 := replicate_three_ne_nil k hk
  simp only [paperAltBaseTiles, if_neg h0, List.length_replicate, if_true]
  rw [stairAltF_iff _ (by omega)]

/-- The word `3^k` (`k ≥ 1`) satisfies the alternate base condition, with the odometers of this file. -/
theorem paperAltBaseCond_three (k : ℕ) (hk : 1 ≤ k) :
    PaperAltBaseCond (List.replicate k Digit.three) (oddT k) (evenT k) := by
  refine ⟨fun h => absurd h (replicate_three_ne_nil k hk), fun k' hk' h => ?_, fun k' hk' h => ?_⟩
  · have hkk : k' = k := by
      have := congrArg List.length h
      simpa using this.symm
    subst hkk
    exact ⟨fun x => oddT_mem k' hk' x, fun x _ => rfl, fun x => evenT_mem k' hk' x, fun x _ => rfl⟩
  · exfalso
    have hmem : Digit.three ∈ List.replicate k Digit.three := List.mem_replicate.mpr ⟨by omega, rfl⟩
    rw [h] at hmem
    have := (List.mem_replicate.mp hmem).2
    exact absurd this (by decide)

/-- **`RespectsHalfV` at `3^k`.** -/
theorem respectsHalfV_three (k : ℕ) (hk : 1 ≤ k) (anc : AltAnchors)
    (h0 : anc.cHat (List.replicate k Digit.three) false = 0) :
    RespectsHalfV (altRevVAnchor anc (List.replicate k Digit.three))
      (FLatticePaper.Tiles.SiteStrings.vWordOf (List.replicate k Digit.three) false) (oddT k).val := by
  have hA : altRevVAnchor anc (List.replicate k Digit.three) = ((0 : ℤ), (0 : ℤ)) := by
    unfold altRevVAnchor altOffsetS
    simp [h0, FLatticePaper.Farey.phase, List.count_replicate]
  have hw : FLatticePaper.Tiles.SiteStrings.vWordOf (List.replicate k Digit.three) false =
      FLatticePaper.Tiles.lvWord k := by
    rw [SpecialCells.vWord_three_false]
    rfl
  rw [hA, hw]
  unfold RespectsHalfV
  obtain ⟨c, hLL, c', -, hrev, hfwd⟩ := lv_respectsPartialV k hk
  have hc : c = ((-1 : ℤ), (-1 : ℤ)) := isLowerLeftPt_unique hLL (lv_lowerLeft k hk)
  subst hc
  have hT := RespectsTranslate.respectsTiles_translate _ _ _ _ ((1 : ℤ), (1 : ℤ)) hrev
  rw [vRevStringAt_shift, show ((-1 : ℤ), (-1 : ℤ)) + ((1 : ℤ), (1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) by ext <;> simp] at hT
  refine ⟨hT, c' + ((1 : ℤ), (1 : ℤ)), ?_⟩
  have hT2 := RespectsTranslate.respectsTiles_translate _ _ _ _ ((1 : ℤ), (1 : ℤ)) hfwd
  rw [vStringAt_shift] at hT2
  exact hT2

/-- **`RespectsHalfH` at `3^k`.** -/
theorem respectsHalfH_three (k : ℕ) (anc : AltAnchors) (h0 : anc.cHat (List.replicate k Digit.three) true = 0) :
    RespectsHalfH (altFwdHAnchor anc (List.replicate k Digit.three))
      (FLatticePaper.Tiles.SiteStrings.hWordOf (List.replicate k Digit.three) true) (evenT k).val := by
  have hA : altFwdHAnchor anc (List.replicate k Digit.three) = ((0 : ℤ), (0 : ℤ)) := by
    unfold altFwdHAnchor
    rw [h0]
    rfl
  have hw : FLatticePaper.Tiles.SiteStrings.hWordOf (List.replicate k Digit.three) true =
      FLatticePaper.Tiles.stairH k := BaseHpStair.hWordOf_three_true k
  rw [hA, hw]
  unfold RespectsHalfH
  obtain ⟨c', -, hf, hr⟩ := altStair_respectsPartialHAt k
  exact ⟨hf, c', hr⟩

/-- **The weak alternate lattice clauses at `3^k`** (`WeakAltPropsU`). -/
theorem weakAltPropsU_three (k : ℕ) (hk : 1 ≤ k) :
    WeakAltPropsU (List.replicate k Digit.three) (oddT k) (evenT k) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · unfold AltLatticeOddV2
    show LatticeSelfCompatible (oddT k) (texV2 ((parentsAt (List.replicate k Digit.three)).current .odd))
      (offsetA ((parentsAt (List.replicate k Digit.three)).current .odd).num
        ((parentsAt (List.replicate k Digit.three)).current .odd).den true)
    rw [cur_odd_three k]
    have key := altLattice_ladder k hk (oddT k)
      (fun x => by rw [oddT_mem k hk x, sub11_eq]) (fun x _ => by
        show paperLadderAltValue _ (x - ((1 : ℤ), (1 : ℤ))) = _
        rw [sub11_eq])
    exact key
  · unfold AltLatticeEvenV2
    show LatticeSelfCompatible (evenT k) (texV2 ((parentsAt (List.replicate k Digit.three)).current .even))
      (offsetA ((parentsAt (List.replicate k Digit.three)).current .even).num
        ((parentsAt (List.replicate k Digit.three)).current .even).den true)
    rw [cur_even_three k]
    exact altLattice_stair k (evenT k) (fun x => evenT_mem k hk x) (fun x _ => rfl)

end FLatticePaper.Tiles.BaseAltThree
