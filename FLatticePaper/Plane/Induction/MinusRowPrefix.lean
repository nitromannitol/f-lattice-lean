import FLatticePaper.Plane.Induction.MinusRowH
import FLatticePaper.Plane.Induction.ListForce
import FLatticePaper.Plane.Induction.RouteStay
import FLatticePaper.Plane.Induction.RestrictedH0Core
import FLatticePaper.Plane.Induction.ConeBoundary
import FLatticePaper.Plane.Induction.EasyNoFort

/-! # The minus-row prefix below the H block is outside the fort

The prefix of the minus row before the H block is `V_r, …, V_1, H_0, V_0` (positions `0 .. r+1`). `V_r..V_1` are removed by
`ListForce.minus_removed_route` (with `RouteStay.minus_route_stays`), and `H_0`, `V_0` are removed by the restricted H_0 core
`RestrictedH0Core.h0_core_restricted_minus` (its candidates are `ListForce.minus_hcand_route`). The inputs are those of
`EasyNoFort.minus_fort_empty`, with its `hcore` replaced by the H_0 core. -/

namespace FLatticePaper.MinusRowPrefix

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
open FLatticePaper.MinusRowWiring FLatticePaper.MinusRowEndpoint

/-- The position `r` of the minus row carries `H_0`. -/
theorem minusRow_get_H0 (r L d : ℤ) :
    (minusRow r L d)[r.toNat]? = some (FreeLabel.H 0) := by
  unfold minusRow
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]; omega)]
  rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
  have hsub : r.toNat - ((List.range r.toNat).map fun i : ℕ => FreeLabel.V (r - (i : ℤ))).length = 0 := by
    simp only [List.length_map, List.length_range]
    omega
  rw [hsub]
  simp

/-- `hFirst = (1,0)` is a closed site. -/
theorem hFirst_closed (frame : ChildFrame) (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den) :
    FLatticePaper.Induction.hFirst ∈ frame.closedPolygon := by
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [ConeBoundary.periodDenominator_eq frame]
    nlinarith
  have hodd : ¬ EvenSite FLatticePaper.Induction.hFirst := by
    unfold EvenSite FLatticePaper.Induction.hFirst
    norm_num
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_neg hodd]
  unfold FLatticePaper.Induction.hFirst
  simp only [ChildFrame.tGrade, ChildFrame.sGrade]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals omega

/-- `vFirst = (0,0)` is a closed site. -/
theorem vFirst_closed (frame : ChildFrame) (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den) :
    FLatticePaper.Induction.vFirst ∈ frame.closedPolygon := by
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [ConeBoundary.periodDenominator_eq frame]
    nlinarith
  have hev : EvenSite FLatticePaper.Induction.vFirst := by
    unfold EvenSite FLatticePaper.Induction.vFirst
    norm_num
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos hev]
  unfold FLatticePaper.Induction.vFirst
  simp only [ChildFrame.tGrade, ChildFrame.sGrade]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals omega

/-- **The minus-row prefix is outside the fort.** Positions `0 .. r − 1` (`V_r..V_1`), `r` (`H_0`) and `r + 1` (`V_0`). -/
theorem minus_prefix_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) (hr0 : 0 ≤ r)
    (hrL2 : r ≤ frame.child.den + frame.child.num - 2)
    (hn1 : 1 ≤ frame.child.num) (hd : 2 * frame.child.num ≤ frame.child.den)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {M : Field} (hrec : FLatticePaper.RecurrentField M)
    (hM : ∀ s ∈ frame.closedPolygon, F s = M s)
    (hH0w : laplacian F ((1 : ℤ), (0 : ℤ)) = 0) (hV0w : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hH0p : ∀ i, FreePolicy.FreePresc frame (-1) ((1 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (1 : ℤ)))
    (hV0p : ∀ i, FreePolicy.FreePresc frame (-1) ((0 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (0 : ℤ)))
    {S : Set Site} (hR : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) :
    ∀ (k : ℕ) (e : Site), k < r.toNat + 2 → (minusSites frame r)[k]? = some e → e ∉ S := by
  have hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z :=
    fun z h1 h2 => hP.strips.2 z (by omega) (by omega)
  have hroute := RouteStay.minus_route_stays frame hS hO hd hR r hrL2
  have hcand : ∀ z ∈ S, z ∈ frame.closedPolygon → ¬ frame.openRect z →
      z = FLatticePaper.Induction.hFirst ∨ z = FLatticePaper.Induction.vFirst :=
    fun z hz hc ho => ListForce.minus_hcand_route frame F hP r hr0 hrL2 hPH hJH hpat S hK hroute z hz hc ho
  have hcore := RestrictedH0Core.h0_core_restricted_minus frame hrec hM hR hcand hH0w hV0w hH0p hV0p
  have hV := ListForce.minus_removed_route frame F hP r hr0 hrL2 hpat S hK hroute
  intro k e hk he
  by_cases hkr : k < r.toNat
  · have hget : (minusSites frame r)[k]? = some (RowAt.vAt frame (r - (k : ℤ))) := by
      unfold minusSites rowSites
      rw [List.getElem?_map, minusRow_get_V r _ _ k (by omega)]
      simp [labelSite]
    rw [hget] at he
    rw [← Option.some.inj he]
    exact hV k hkr
  · by_cases hkr' : k = r.toNat
    · subst hkr'
      have hget : (minusSites frame r)[r.toNat]? = some FLatticePaper.Induction.hFirst := by
        unfold minusSites rowSites
        rw [List.getElem?_map, minusRow_get_H0]
        simp only [Option.map_some, labelSite]
        rw [RowAt.hAt_zero frame, HChain.hpath_zero]
      rw [hget] at he
      rw [← Option.some.inj he]
      exact fun h => hcore _ h (hFirst_closed frame hn1 hd)
    · have hk1 : k = r.toNat + 1 := by omega
      subst hk1
      have hget : (minusSites frame r)[r.toNat + 1]? = some FLatticePaper.Induction.vFirst := by
        unfold minusSites rowSites
        rw [List.getElem?_map, minusRow_get_V0]
        simp only [Option.map_some, labelSite]
        have h0 := RowAt.vAt_nat frame 0 (by omega)
        simp only [Nat.cast_zero] at h0
        rw [h0, VChain.vpath_zero]
      rw [hget] at he
      rw [← Option.some.inj he]
      exact fun h => hcore _ h (vFirst_closed frame hn1 hd)

/-- **The minus row up to the end of the H block is outside the fort.** Positions `0 .. r+1` are the prefix
(`V_r..V_1`, `H_0`, `V_0`), positions `r+2 .. r+d` the H block; `r = odd.den + odd.num` is the break. -/
theorem minus_row_up_to_H_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num) (hr0 : 0 ≤ frame.parents.odd.den + frame.parents.odd.num)
    (hrL2 : frame.parents.odd.den + frame.parents.odd.num ≤ frame.child.den + frame.child.num - 2)
    (hcap : ∀ (K : ℕ), 3 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2 →
      ∀ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num →
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F (-1) (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.parents.odd.den + frame.parents.odd.num then 0 else -1)
    (hPH : ∀ h : Site, frame.freeH h → frame.price F h ≤ frame.cutPrice ∧
      (frame.price F h = frame.cutPrice → h = FLatticePaper.Induction.hFirst))
    (hJH : ∀ h : Site, frame.freeH h → frame.roundedSlip F (-1) h = 0)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    {M : Field} (hrec : FLatticePaper.RecurrentField M) (hM : ∀ s ∈ frame.closedPolygon, F s = M s)
    (hH0w : laplacian F ((1 : ℤ), (0 : ℤ)) = 0) (hV0w : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hH0p : ∀ i, FreePolicy.FreePresc frame (-1) ((1 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (1 : ℤ)))
    (hV0p : ∀ i, FreePolicy.FreePresc frame (-1) ((0 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (0 : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z) :
    ∀ (k : ℕ) (e : Site), k < (frame.parents.odd.den + frame.parents.odd.num).toNat + 2 + (frame.child.den - 1).toNat →
      (minusSites frame (frame.parents.odd.den + frame.parents.odd.num))[k]? = some e → e ∉ S := by
  intro k e hk he
  by_cases hpre : k < (frame.parents.odd.den + frame.parents.odd.num).toNat + 2
  · exact minus_prefix_removed frame F hP _ hr0 hrL2 hn1 hnd hpat hPH hJH hO hrec hM hH0w hV0w hH0p hV0p hS hK k e hpre he
  · exact MinusRowH.minus_H_block_removed frame F hP hsig hZ2 hZ3 hn1 hnd hNo hr0 hcap hS hK
      (fun j e' hj hje => minus_prefix_removed frame F hP _ hr0 hrL2 hn1 hnd hpat hPH hJH hO hrec hM hH0w hV0w hH0p hV0p hS hK j e' hj hje)
      k e (by omega) (by omega) he

end FLatticePaper.MinusRowPrefix
