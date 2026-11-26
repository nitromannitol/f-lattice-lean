import FLatticePaper.Plane.Induction.RefuteTree
import FLatticePaper.Plane.Induction.RowPair
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.OddPhaseAlternate
import FLatticePaper.Plane.Induction.Seams

/-! # Easy-frame H labels, rank 1 (even label whose east step is free)

For `1 ≤ m`, `m + 1 < d`, an even `z = hpath m` whose east neighbour `z + (1,0)` is free has successor `hpath (m+1) = z + (1,0)`.
The label `H_{m−d} = hAt (m − d) = z − U` is refuted by the earlier label `H_{m+1−d}` through the white rule:
* its colour is the colour of `z`, which is white (`FreeHWhite.laplacian_eq_zero_of_freeH`, deck invariance by `U`);
* its prescribed input is `p = hAt (m−d) + (1,0)`, permitted through the translate `U` (`FreePresc`, `prescribedH = (1,0)` on even free
  H sites other than `hFirst` and `hLast`);
* `p = hAt (m+1−d)` (`hAt_sub_den`, `hsucc`), which is the earlier entry. -/

namespace FLatticePaper.EasyHRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree

/-- `combine 1 0` is the period `U = (d, n)`. -/
theorem combine_one_zero_eq_Uvec (frame : ChildFrame) :
    frame.child.modifiedDeck.combine 1 0 = RowAt.Uvec frame := by
  rw [← FLatticePaper.OddPhaseAlternate.kernel_eq_combine, frame.child_modifiedDeck_kernel]
  rfl

/-- The H label `H_{m − d}` is `hpath m − U` (`RowAt.hAt`). -/
theorem hAt_sub_den (frame : ChildFrame) {m : ℕ} (hm : (m : ℤ) < frame.child.den) :
    RowAt.hAt frame ((m : ℤ) - frame.child.den) = HChain.hpath frame m - RowAt.Uvec frame := by
  have h := RowAt.hAt_add_den frame ((m : ℤ) - frame.child.den)
  rw [show (m : ℤ) - frame.child.den + frame.child.den = (m : ℤ) by ring, RowAt.hAt_nat frame m hm] at h
  exact eq_sub_of_add_eq h.symm

/-- The successor along the east step when the east neighbour is free. -/
theorem hsucc_east {frame : ChildFrame} {z : Site} (hfree : (z.1 + 1, z.2) ∈ frame.freeH) :
    HChain.hsucc frame z = (z.1 + 1, z.2) := by
  unfold HChain.hsucc
  rw [if_pos hfree]

/-- **Rank 1 (even label, free east step).** `H_{m−d}` is refuted by `H_{m+1−d}`, which is earlier. -/
theorem refuted_even_H_east_free (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  set z := HChain.hpath frame m with hz
  set e := RowAt.hAt frame ((m : ℤ) - frame.child.den) with he
  have hzfree : z ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hdom : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := RowPair.hpath_fst frame m
    have h2 : FLatticePaper.Induction.hFirst.1 = 1 := rfl
    rw [← hz, h, h2] at h1
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    have h1 := RowPair.hpath_fst frame m
    have h2 : frame.hLast.1 = frame.child.den := rfl
    rw [← hz, h, h2] at h1
    omega
  -- the colour of `e` is the colour of `z` (deck invariance by `U`)
  have hU := combine_one_zero_eq_Uvec frame
  have heU : e + frame.child.modifiedDeck.combine 1 0 = z := by
    rw [hU, he, hAt_sub_den frame (by omega), ← hz]
    abel
  have hcol : laplacian F e = 0 := by
    have h := laplacian_add_combine hper e 1 0
    rw [heU] at h
    rw [← h]
    exact FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  -- the prescribed input `e + (1,0)` is permitted through the translate `U`
  have hpres : EvenSite z := hev
  have hprescH : frame.prescribedH (-1) z = ((1 : ℤ), (0 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_pos hpres]
  have hFP : FreePolicy.FreePresc frame (-1) e (e + ((1 : ℤ), (0 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame e := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hperm : permitsQ1 frame F (-1) e (e + ((1 : ℤ), (0 : ℤ))) :=
    Or.inr ⟨hcol, Or.inl ⟨hfc, hFP⟩⟩
  -- the prescribed input is the earlier label `H_{m+1−d}`
  have hsucc_eq : HChain.hsucc frame z = (z.1 + 1, z.2) := hsucc_east hfree
  have hnext : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = e + ((1 : ℤ), (0 : ℤ)) := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      hAt_sub_den frame (show ((m + 1 : ℕ) : ℤ) < frame.child.den by push_cast; omega)]
    have hp : HChain.hpath frame (m + 1) = (z.1 + 1, z.2) := by
      rw [HChain.hpath_succ, ← hz, hsucc_eq]
    rw [hp, he, hAt_sub_den frame (by omega), ← hz]
    ext
    · simp only [Prod.fst_sub, Prod.fst_add]
      ring
    · simp
  have hEp : E (e + ((1 : ℤ), (0 : ℤ))) := by
    rw [← hnext]
    exact hE
  exact Refuted.white hcol hperm (Refuted.earlier hEp)

end FLatticePaper.EasyHRank
