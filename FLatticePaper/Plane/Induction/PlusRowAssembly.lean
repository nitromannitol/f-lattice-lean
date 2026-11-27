import FLatticePaper.Plane.Induction.PlusRowPrefix
import FLatticePaper.Plane.Induction.ZoneI1

/-! # The plus row up to the end of the H block is outside the restricted fort (eta = 1, easy regime)

The positions `0, …, r + 2` are the prefix (`PlusRowPrefix.plus_prefix_removed`); the positions `r + 3, …, P0 - 1` are the positive V
tail `V_1, …, V_{L-r-2}`, which is taken as the hypothesis `hTail` (w1's block, `plus_href_row`); the positions `P0, …` are the H block
(`PlusRowH.plus_H_block_removed`), where `P0 = (r+1) + 2 + (L-r-2)`. -/

namespace FLatticePaper.PlusRowAssembly

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows FLatticePaper.PlusRowWiring

/-- **The plus row up to the end of its H block.** -/
theorem plus_row_up_to_H_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hnb2 : 2 ≤ frame.child.num)
    (hpa : 0 ≤ frame.parents.odd.num) (hpb : frame.parents.odd.num + 1 ≤ frame.parents.odd.den)
    (hpc : 1 ≤ frame.parents.even.num) (hpe : frame.parents.even.num ≤ frame.parents.even.den)
    (hcap : ∀ (K : ℕ), 3 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (r : ℤ) (hr : r = frame.parents.odd.den + frame.parents.odd.num)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      frame.roundedSlip F 1 (VChain.vpath frame k) =
        if (k : ℤ) ≤ frame.child.den + frame.child.num - r - 2 then 0 else 1)
    (hSwin : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hOwin : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hv1 : RowAt.vAt frame (-1) = ((1 : ℤ), (-1 : ℤ))) (hv2 : RowAt.vAt frame (-2) = ((1 : ℤ), (-2 : ℤ)))
    (hw1 : laplacian F ((1 : ℤ), (-1 : ℤ)) = 0)
    (hp1 : FreePolicy.FreePresc frame 1 ((1 : ℤ), (-1 : ℤ)) ((2 : ℤ), (-1 : ℤ)))
    (hy : laplacian F ((2 : ℤ), (-1 : ℤ)) = -1) (hz : laplacian F ((2 : ℤ), (-2 : ℤ)) = 0)
    (hnfz : ¬ FreeClosure.freeClosure frame ((2 : ℤ), (-2 : ℤ)))
    (hwp : frame.price F ((2 : ℤ), (0 : ℤ)) ≤ frame.cutPrice)
    (hwj : frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≤ 0)
    (hwne : frame.price F ((2 : ℤ), (0 : ℤ)) ≠ frame.cutPrice ∨ frame.roundedSlip F 1 ((2 : ℤ), (0 : ℤ)) ≠ 0)
    (hw0 : laplacian F ((1 : ℤ), (0 : ℤ)) = 0)
    (hp0 : FreePolicy.FreePresc frame 1 ((1 : ℤ), (0 : ℤ)) ((1 : ℤ), (-1 : ℤ)))
    (hwV : laplacian F ((0 : ℤ), (0 : ℤ)) = 0)
    (hpV : FreePolicy.FreePresc frame 1 ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)))
    (hL : 0 < frame.child.den + frame.child.num)
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z)
    (hTail : ∀ (j : ℕ) (e : Site), (r + 1).toNat + 2 ≤ j →
      j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat →
      (plusSites frame r)[j]? = some e → e ∉ S) :
    ∀ (j : ℕ) (e : Site), j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + (frame.child.den - 1).toNat →
      (plusSites frame r)[j]? = some e → e ∉ S := by
  have hcn := ZoneI1.child_num_eq frame
  have hcd := ZoneI1.child_den_eq frame
  have hr1 : 1 ≤ r := by omega
  have hrL2 : r ≤ frame.child.den + frame.child.num - 2 := by omega
  have hpre := PlusRowPrefix.plus_prefix_removed frame F hP r hr1 hrL2 hpat hSwin hOwin hnd hv1 hv2 hw1 hp1 hy hz
    hnfz hwp hwj hwne hw0 hp0 hwV hpV hS hK
  have hEarly : ∀ (j : ℕ) (e' : Site), j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat →
      (plusSites frame r)[j]? = some e' → e' ∉ S := by
    intro j e' hj he
    by_cases hjr : j < (r + 1).toNat + 2
    · exact hpre j e' hjr he
    · exact hTail j e' (by omega) hj he
  intro j e hj he
  by_cases hjP : j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat
  · exact hEarly j e hjP he
  · exact PlusRowH.plus_H_block_removed frame F hP hsig hZ2 hZ3 hn1 hnd hnb2 hpa hpb hpc hpe hL hcap r hr hS hK
      hEarly j e (by omega) (by omega) he

end FLatticePaper.PlusRowAssembly
