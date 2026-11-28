import FLatticePaper.Tiles.PaperAltDomains
import FLatticePaper.Tiles.NearStairVerticalRespects
import FLatticePaper.Tiles.NearLadderAltRespects
import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.SpecialCells
import FLatticePaper.Tiles.GlueChain
import FLatticePaper.Tiles.RespectsTranslate
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.BaseAltLattice

/-! # The alternate base odometers at the words `2^k`, `k ≥ 1` (`BaseWeakAltInput`)

The odd alternate child of `2^k` is the near-stair alternate `paperNearStairAltTile (2k+3)`, read at `x + (0,1)`; its vertical half
string `w_v = p q^{k+1}` is respected by `pq_respectsPartialV k` at the lower-left point `(0,1)`, and the translate by `(0,-1)` respects
it at the anchor `(0,0)`. The even alternate child is the near-ladder alternate `paperNearLadderAltTile (2k+2)`, read at `x + (0,1)`,
whose half string `w_h = q^{2k+1} p` is respected by `nla_respectsPartialH k` at `(0,1)`, translated by `(0,-1)` to the anchor `(0,0)`.
The lattice clauses are `BaseAltLattice`. -/

namespace FLatticePaper.Tiles.BaseAltTwo

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
open FLatticePaper.Tiles.BaseAltLattice (altLattice_nearStair altLattice_nearLadder)
open FLatticePaper.Tiles.GlueChain (vRevStringAt_shift vStringAt_shift hStringAt_shift hRevStringAt_shift)
open FLatticePaper.Tiles.AltRotStep (isLowerLeftPt_unique)

/-- The odd alternate odometer of `2^k`: the near-stair alternate `paperNearStairAltTile (2k+3)`, read at `x + (0,1)`. -/
noncomputable def oddW (k : ℕ) : PartialOdometer :=
  ⟨SurgicalAltTiles.altOddTile paperAltBaseTiles (List.replicate k Digit.two),
    fun x => paperNearStairAltValue (2 * (k : ℤ) + 3) (x + ((0 : ℤ), (1 : ℤ)))⟩

/-- The even alternate odometer of `2^k`: the near-ladder alternate `paperNearLadderAltTile (2k+2)`, read at `x + (0,1)`. -/
noncomputable def evenW (k : ℕ) : PartialOdometer :=
  ⟨SurgicalAltTiles.altEvenTile paperAltBaseTiles (List.replicate k Digit.two),
    fun x => paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + ((0 : ℤ), (1 : ℤ)))⟩

theorem replicate_two_ne_nil (k : ℕ) (hk : 1 ≤ k) : List.replicate k Digit.two ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem replicate_two_ne_three (k : ℕ) (hk : 1 ≤ k) : List.replicate k Digit.two ≠ List.replicate k Digit.three := by
  intro h
  have hmem : Digit.two ∈ List.replicate k Digit.two := List.mem_replicate.mpr ⟨by omega, rfl⟩
  rw [h] at hmem
  exact absurd (List.mem_replicate.mp hmem).2 (by decide)

theorem oddW_mem (k : ℕ) (hk : 1 ≤ k) (x : GInt) :
    x ∈ (oddW k).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3) := by
  show x ∈ SurgicalAltTiles.altOddTile paperAltBaseTiles (List.replicate k Digit.two) ↔ _
  rw [altOddTile_base _ (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))]
  have h0 := replicate_two_ne_nil k hk
  have h3 := replicate_two_ne_three k hk
  simp only [paperAltBaseTiles, if_neg h0, if_neg h3, List.length_replicate]
  rw [mem_shift_down, nearStairAltF_iff _ (by omega)]

theorem evenW_mem (k : ℕ) (hk : 1 ≤ k) (x : GInt) :
    x ∈ (evenW k).dom ↔ x + ((0 : ℤ), (1 : ℤ)) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2) := by
  show x ∈ SurgicalAltTiles.altEvenTile paperAltBaseTiles (List.replicate k Digit.two) ↔ _
  rw [altEvenTile_base _ (Or.inr (Or.inr fun d hd => List.eq_of_mem_replicate hd))]
  have h0 := replicate_two_ne_nil k hk
  have h3 := replicate_two_ne_three k hk
  simp only [paperAltBaseTiles, if_neg h0, if_neg h3, List.length_replicate]
  rw [mem_shift_down, nearLadderAltF_iff _ (by omega)]

/-- The word `2^k` (`k ≥ 1`) satisfies the alternate base condition, with the odometers of this file. -/
theorem paperAltBaseCond_two (k : ℕ) (hk : 1 ≤ k) :
    PaperAltBaseCond (List.replicate k Digit.two) (oddW k) (evenW k) := by
  refine ⟨fun h => absurd h (replicate_two_ne_nil k hk), fun k' hk' h => ?_, fun k' hk' h => ?_⟩
  · exfalso
    have hmem : Digit.two ∈ List.replicate k Digit.two := List.mem_replicate.mpr ⟨by omega, rfl⟩
    rw [h] at hmem
    exact absurd (List.mem_replicate.mp hmem).2 (by decide)
  · have hkk : k' = k := by
      have := congrArg List.length h
      simpa using this.symm
    subst hkk
    exact ⟨fun x => oddW_mem k' hk' x, fun x _ => rfl, fun x => evenW_mem k' hk' x, fun x _ => rfl⟩

/-- **`RespectsHalfV` at `2^k`.** -/
theorem respectsHalfV_two (k : ℕ) (anc : AltAnchors)
    (h0 : anc.cHat (List.replicate k Digit.two) false = 0) :
    RespectsHalfV (altRevVAnchor anc (List.replicate k Digit.two))
      (FLatticePaper.Tiles.SiteStrings.vWordOf (List.replicate k Digit.two) false) (oddW k).val := by
  have hA : altRevVAnchor anc (List.replicate k Digit.two) = ((0 : ℤ), (0 : ℤ)) := by
    unfold altRevVAnchor altOffsetS
    simp [h0, FLatticePaper.Farey.phase, List.count_replicate]
  have hw : FLatticePaper.Tiles.SiteStrings.vWordOf (List.replicate k Digit.two) false = pqWord k := by
    rw [SpecialCells.vWord_two_false]
    rfl
  rw [hA, hw]
  unfold RespectsHalfV
  obtain ⟨c, hLL, c', -, hrev, hfwd⟩ := pq_respectsPartialV k
  have hc : c = ((0 : ℤ), (1 : ℤ)) := isLowerLeftPt_unique hLL (pq_lowerLeft k)
  subst hc
  have hf : (fun x => paperNearStairAltValue (2 * (k : ℤ) + 3) (x - ((0 : ℤ), (-1 : ℤ)))) = (oddW k).val := by
    funext x
    simp only [oddW]
    congr 1
  have hT := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hrev
  rw [vRevStringAt_shift, show ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) by ext <;> simp] at hT
  rw [hf] at hT
  refine ⟨hT, c' + ((0 : ℤ), (-1 : ℤ)), ?_⟩
  have hT2 := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hfwd
  rw [vStringAt_shift, hf] at hT2
  exact hT2

/-- **`RespectsHalfH` at `2^k`.** -/
theorem respectsHalfH_two (k : ℕ) (hk : 1 ≤ k) (anc : AltAnchors)
    (h0 : anc.cHat (List.replicate k Digit.two) true = 0) :
    RespectsHalfH (altFwdHAnchor anc (List.replicate k Digit.two))
      (FLatticePaper.Tiles.SiteStrings.hWordOf (List.replicate k Digit.two) true) (evenW k).val := by
  have hA : altFwdHAnchor anc (List.replicate k Digit.two) = ((0 : ℤ), (0 : ℤ)) := by
    unfold altFwdHAnchor
    rw [h0]
    rfl
  have hw : FLatticePaper.Tiles.SiteStrings.hWordOf (List.replicate k Digit.two) true = nlaWord k :=
    BaseHpNearEven.hWordOf_two_true k
  rw [hA, hw]
  unfold RespectsHalfH
  obtain ⟨c, hLL, c', -, hf, hr⟩ := nla_respectsPartialH k hk
  have hc : c = ((0 : ℤ), (1 : ℤ)) := isLowerLeftPt_unique hLL (nla_lowerLeft k hk)
  subst hc
  have hfun : (fun x => paperNearLadderAltValue (2 * (k : ℤ) + 2) (x - ((0 : ℤ), (-1 : ℤ)))) = (evenW k).val := by
    funext x
    simp only [evenW]
    congr 1
  have hT := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hf
  rw [hStringAt_shift, show ((0 : ℤ), (1 : ℤ)) + ((0 : ℤ), (-1 : ℤ)) = ((0 : ℤ), (0 : ℤ)) by ext <;> simp] at hT
  rw [hfun] at hT
  refine ⟨hT, c' + ((0 : ℤ), (-1 : ℤ)), ?_⟩
  have hT2 := RespectsTranslate.respectsTiles_translate _ _ _ _ ((0 : ℤ), (-1 : ℤ)) hr
  rw [hRevStringAt_shift, hfun] at hT2
  exact hT2

/-- **The weak alternate lattice clauses at `2^k`** (`WeakAltPropsU`). -/
theorem weakAltPropsU_two (k : ℕ) (hk : 1 ≤ k) :
    WeakAltPropsU (List.replicate k Digit.two) (oddW k) (evenW k) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · unfold AltLatticeOddV2
    show LatticeSelfCompatible (oddW k) (texV2 ((parentsAt (List.replicate k Digit.two)).current .odd))
      (offsetA ((parentsAt (List.replicate k Digit.two)).current .odd).num
        ((parentsAt (List.replicate k Digit.two)).current .odd).den true)
    rw [cur_odd_two k]
    exact altLattice_nearStair k (oddW k) (fun x => oddW_mem k hk x) (fun x _ => rfl)
  · unfold AltLatticeEvenV2
    show LatticeSelfCompatible (evenW k) (texV2 ((parentsAt (List.replicate k Digit.two)).current .even))
      (offsetA ((parentsAt (List.replicate k Digit.two)).current .even).num
        ((parentsAt (List.replicate k Digit.two)).current .even).den true)
    rw [cur_even_two k]
    exact altLattice_nearLadder k hk (evenW k) (fun x => evenW_mem k hk x) (fun x _ => rfl)

end FLatticePaper.Tiles.BaseAltTwo
