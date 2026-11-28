import FLatticePaper.Tiles.AltShiftValues
import FLatticePaper.Tiles.AltItem4Rot
import FLatticePaper.Tiles.WeakAltStepAssembly

/-! # The compatibility of the registers with their translates by the alternate shifts, from the family

For a good family below a non-base word `w` with registers `u₁`, `u₂`, the odd tile odometer of `u₁` is compatible with its
translate by `S_p` and the even tile odometer of `u₂` with its translate by `S_q`, both with the affine factor `a_{p,2}`
(`shift_compat_family`): the input `AltShiftCompatInput` of the weak alternate step, at every non-base word.

The right-walk heights of an even tile odometer (`right_walk_even`) come from the quarter turn (`TileRotation` with the odd tile
odometer of the swapped word, `MixedCompatEdges.four_traces` on the side `v⁺`): a point `z` of the right walk, `z, z - v_{q,1}` in
`T(q)`, is `i y + v_{q,1} - i` for a point `y` of the bottom walk of `T(R q)` (`rot_standard_tiles`). -/

namespace FLatticePaper.Tiles.AltShiftFamily

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile swapW)
open FLatticePaper.Tiles.JointFamily (JointData JSlice LatticeSelfCompatible)
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.AltShiftGeom (shP shQ)

/-- The odd child of the swapped word is the rotation `((d - n)/2, (d + n)/2)` of the even child `n/d`. -/
theorem fracOdd_swapW (v : Word) :
    fracOdd (swapW v) = ⟨((fracEven v).den - (fracEven v).num) / 2, ((fracEven v).den + (fracEven v).num) / 2⟩ := by
  have hq : (fracEven v).Even := (parentsAt_valid v).current_even_parity
  show SiteInduction.curO (swapW v) = _
  rw [AltItem4.curO_swapW]
  exact Fraction.rotate_of_even hq

set_option maxHeartbeats 400000 in
/-- **The right-walk heights of an even tile odometer of the family**: `o_q(z) + h₀(z - v_{q,1})` is constant on the points
`z` with `z, z - v_{q,1}` in `T(q)`. -/
theorem right_walk_even (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (n : ℕ) (hg : GoodBelow D f n) (v : Word) (hv : v.length < n) :
    ∃ k : ℤ, ∀ z, z ∈ evenTile v → z - texV1Even (fracEven v) ∈ evenTile v →
      (f v).tEven.val z + JointFamily.h0 (z - texV1Even (fracEven v)) = k := by
  have hsv : (swapW v).length < n := by rwa [JointRot.length_swapW]
  have sl := fun (k : Word) (hk : k.length < n) => JointRot.family_slopes D f k.length
    (fun l hl => (hg l (lt_of_le_of_lt hl hk)).1) (JointRot.baseSlopes_paper D hS hA) k le_rfl
  obtain ⟨β, hβ⟩ := (sl v hv).2.1
  obtain ⟨βr, hβr⟩ := (sl (swapW v) hsv).1
  obtain ⟨-, hdQ, -, -⟩ := AltSevenFamily.regEven_data D hS hA f n hg v hv
  obtain ⟨-, hdR, -, -⟩ := AltSevenFamily.regOdd_data D hS hA f n hg (swapW v) hsv
  have resQ := (WeakStepAssembly.slice_respects D f v (hg v hv).1).2
  have resR := (WeakStepAssembly.slice_respects D f (swapW v) (hg (swapW v) hsv).1).1
  obtain ⟨k, hk⟩ := MixedCompatEdges.four_traces (f v).tEven (f (swapW v)).tOdd
    (fun z => z ∈ evenTile v ∧ z + texV2 (fracEven v) ∈ evenTile v)
    (fun y => y ∈ oddTile (swapW v) ∧ y + texV2 (fracOdd (swapW v)) ∈ oddTile (swapW v))
    (texV1Even (fracEven v)) (fracEven v).num (fracEven v).den β βr hβ hβr
    (fun z hz => AltLatticeOddWFamily.bot_even v _ β resQ.2.1 hβ z hz.1 hz.2)
    (fun y hy => AltLatticeOddWFamily.bot_odd (swapW v) _ βr resR.2.1 hβr y hy.1 hy.2)
    (fun y hy => by rw [hdR]; exact hy.1) (hg v hv).2.2.1.2.2.2.1 (hg v hv).2.2.2.1.2.1 .vPlus
  refine ⟨k, fun z h1 h2 => ?_⟩
  -- the point of the rotated tile
  have hq : ((fracEven v).num + (fracEven v).den) % 2 = 0 := (parentsAt_valid v).current_even_parity
  have hrq := fracOdd_swapW v
  have hrot := (Standard.rot_standard_tiles (swapW v)).1
  rw [StandardHalfTurn.swapW_swapW] at hrot
  have htF : Standard.tF ((parentsAt (swapW v)).current .odd) = ((0 : ℤ), (1 : ℤ)) - texV1Even (fracEven v) := by
    rw [show (parentsAt (swapW v)).current .odd = fracOdd (swapW v) from rfl, hrq]
    ext <;> simp only [Standard.tF, Standard.tV, texV1Even, Prod.fst_sub, Prod.snd_sub] <;> omega
  have hB : texV2 (fracOdd (swapW v)) = (-(fracEven v).num, (fracEven v).den) := by
    rw [hrq]; ext <;> simp only [texV2] <;> omega
  have m1 : z + Standard.tF ((parentsAt (swapW v)).current .odd) ∈ Standard.rot (oddTile (swapW v)) := by
    rw [hrot, mem_shift, add_sub_cancel_right]; exact h1
  have m2 : z - texV1Even (fracEven v) + Standard.tF ((parentsAt (swapW v)).current .odd) ∈
      Standard.rot (oddTile (swapW v)) := by
    rw [hrot, mem_shift, add_sub_cancel_right]; exact h2
  simp only [Standard.rot, Finset.mem_image] at m1 m2
  obtain ⟨y, hy, hyz⟩ := m1
  obtain ⟨y', hy', hyz'⟩ := m2
  rw [htF] at hyz hyz'
  have c1 := congrArg Prod.fst hyz
  have c2 := congrArg Prod.snd hyz
  have c3 := congrArg Prod.fst hyz'
  have c4 := congrArg Prod.snd hyz'
  simp only [mulI, texV1Even, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at c1 c2 c3 c4
  have ey : y' = y + texV2 (fracOdd (swapW v)) := by
    rw [hB]; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> linarith
  have hz : z = mulI y + (texV1Even (fracEven v) - ((0 : ℤ), (1 : ℤ))) := by
    rw [hyz]; abel
  have e := hk z (by rw [hdQ]; exact h1) ⟨y, ⟨hy, ey ▸ hy'⟩, hz⟩
  simp only [MixedCompatEdges.edgeHeight] at e
  linarith

set_option maxHeartbeats 400000 in
/-- **The alternate shift compatibility of the registers** (`AltShiftCompatInput`, at every non-base word): over a good family
below `w`, the odd tile odometer of the odd register `u₁` is compatible with its translate by `S_p`, and the even tile odometer of
the even register `u₂` with its translate by `S_q`, both with the affine factor `a_{p,2}`. -/
theorem shift_compat_family (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w u1 u2 : Word) (hg : GoodBelow D f w.length) (hw : ¬ IsBase w)
    (hr : SurgicalWeak.regsAt w = (some u1, some u2)) :
    LatticeSelfCompatible (f u1).tOdd
        (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1
        (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) ∧
      LatticeSelfCompatible (f u2).tEven
        (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2
        (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) := by
  have h1 : (SurgicalWeak.regsAt w).1 = some u1 := by rw [hr]
  have h2 : (SurgicalWeak.regsAt w).2 = some u2 := by rw [hr]
  have l1 := JointInduction.regsAt_lt _ u1 (Or.inl h1)
  have l2 := JointInduction.regsAt_lt _ u2 (Or.inr h2)
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents _).1 u1 h1
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents _).2 u2 h2
  have htP : (stateAt w).tOdd = oddTile u1 := (WeakStepPaper.regsAt_tiles _).1 u1 h1
  have htQ : (stateAt w).tEven = evenTile u2 := (WeakStepPaper.regsAt_tiles _).2.2.1 u2 h2
  refine ⟨?_, ?_⟩
  · -- the odd register
    obtain ⟨βP, hdP0, hcP, hhP⟩ := AltSevenFamily.regOdd_data D hS hA f _ hg u1 l1
    have botP0 := AltLatticeOddWWrap.std_bottom_odd D hS hA f _ hg u1 l1 βP hcP
    refine AltShiftValues.shift_P hw (f u1).tOdd (by rw [hdP0, htP]) ?_ βP ?_
    · intro z hz
      obtain ⟨m, eq⟩ := hhP z hz
      simp only [AltGlueOdd.Cp, JointFamily.aP2, hp, offsetA]
      exact ⟨m, eq⟩
    · intro y a b
      rw [htP] at a
      rw [htP, hp] at b
      exact botP0 y a b
  · -- the even register
    obtain ⟨-, hdQ0, -, -⟩ := AltSevenFamily.regEven_data D hS hA f _ hg u2 l2
    obtain ⟨k, hk⟩ := right_walk_even D hS hA f _ hg u2 l2
    obtain ⟨α, β, hN, hT1, -⟩ := (hg u2 l2).2.2.1.2.1
    obtain ⟨β0, hN0⟩ := (JointRot.family_slopes D f u2.length (fun l hl => (hg l (lt_of_le_of_lt hl l2)).1)
      (JointRot.baseSlopes_paper D hS hA) u2 le_rfl).2.1
    obtain ⟨rfl, rfl⟩ := JointRot.firstTileNormal_unique _ _ _ _ _ hN hN0
    refine AltShiftValues.shift_Q hw (f u2).tEven (by rw [hdQ0, htQ]) k ?_ ?_
    · intro z a b
      rw [htQ] at a b
      rw [hq] at b ⊢
      exact hk z a b
    · intro z a b
      rw [htQ] at a b
      rw [hq] at b ⊢
      have e := hT1 z (by rw [hdQ0]; exact a) (by rw [hdQ0]; exact b)
      simp only [JointFamily.normed, dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, sub_zero] at e
      change (f u2).tEven.val (z + texV1Even (fracEven u2)) - β = (f u2).tEven.val z - β at e
      linarith

/-- **`AltShiftCompatInput`** of the weak alternate step, for every joint data. -/
theorem altShiftCompatInput_paper (D : JointData) : WeakAltStepAssembly.AltShiftCompatInput D :=
  fun hS hA f w u1 u2 hg hw hr => shift_compat_family D hS hA f w u1 u2 hg hw hr

end FLatticePaper.Tiles.AltShiftFamily
