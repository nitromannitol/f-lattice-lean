import FLatticePaper.Plane.Induction.OddAxialRank

/-! # The rank-3 chain with the east-north input white (no lateness)

`refuted_odd_H_white_q` is the rank-3 chain of `OddAxialRank.refuted_odd_H_axial` with the colour of `z + (1,1)` as an input
instead of the late hypothesis. Its colour is `0` in the late case (`colour_q_odd`) and in the other case the field is binary
(`Packet.binary`), so the minus-row H entries with `lap (z+(1,1)) = 0` are refuted by this chain for every `t(z)`. -/

namespace FLatticePaper.MinusRowOdd

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.EasyHRank
open FLatticePaper.EasyHRankDiag FLatticePaper.OddAxialRank

theorem refuted_odd_H_white_q (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hqw : laplacian F (HChain.hpath frame m + ((1 : ℤ), (1 : ℤ))) = 0)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  set z := HChain.hpath frame m with hz
  set l := RowAt.hAt frame ((m : ℤ) - frame.child.den) with hl
  have hzfree : z ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hx2 : 2 ≤ z.1 := by omega
  have hxd : z.1 < frame.child.den := by omega
  have hdom : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h3 : z.1 = 1 := congrArg Prod.fst h
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    have h3 : z.1 = frame.child.den := congrArg Prod.fst h
    omega
  have hEast := EasyHRankDiag.east_freeH_of_odd frame hzfree hodd (by omega) hxd
  have hsucc_eq : HChain.hpath frame (m + 1) = (z.1 + 1, z.2) := by
    rw [HChain.hpath_succ, ← hz, EasyHRank.hsucc_east hEast]
  have hU := EasyHRank.combine_one_zero_eq_Uvec frame
  have hA : l = z - RowAt.Uvec frame := by
    rw [hl, EasyHRank.hAt_sub_den frame (by omega), ← hz]
  have heU : l + frame.child.modifiedDeck.combine 1 0 = z := by
    rw [hU, hA]
    abel
  have hlodd : ¬ EvenSite l := by
    rw [hA]
    obtain ⟨hnodd, hdodd⟩ := frame.child_odd
    unfold EvenSite at hodd ⊢
    unfold RowAt.Uvec
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  -- the successor and the label of the east entry
  have hAt_next : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = (z.1 + 1, z.2) - RowAt.Uvec frame := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      EasyHRank.hAt_sub_den frame (show ((m + 1 : ℕ) : ℤ) < frame.child.den by push_cast; omega), hsucc_eq]
  have hE_l : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = l + ((1 : ℤ), (0 : ℤ)) := by
    rw [hAt_next, hA]
    refine Prod.ext ?_ ?_
    · simp only [RowAt.Uvec, Prod.fst_sub, Prod.fst_add]
      omega
    · simp [RowAt.Uvec]
  have hE' : E (l + ((1 : ℤ), (0 : ℤ))) := by
    rw [← hE_l]
    exact hE
  -- colours: the label, the north input, the east-north input
  have hcol : laplacian F l = 0 := by
    have h := laplacian_add_combine hper l 1 0
    rw [heU] at h
    rw [← h]
    exact FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  obtain ⟨hrng1, hrng2⟩ := odd_t_range frame hzfree hodd hx2 hxd
  have hcolP : laplacian F (z + ((0 : ℤ), (1 : ℤ))) = 0 :=
    colour_north_odd frame hP.strips hodd hrng1 hrng2
  have hcolQ : laplacian F (z + ((1 : ℤ), (1 : ℤ))) = 0 := hqw
  -- strict interior, hence nonfree
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hzfree
    exact hzfree.1
  have hnfP : Nonfree frame (z + ((0 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_north_odd frame hzfree hodd hx2 hxd)
  have hnfQ : Nonfree frame (z + ((1 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_q_odd frame hd2 hzfree hodd hx2 hxd hEast)
  -- the label-level translates by `−U`
  have hcomb_neg : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← hU]
    ext <;> simp [PeriodDeck.combine]
  have hPl : l + ((0 : ℤ), (1 : ℤ)) = (z + ((0 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 := by
    rw [hcomb_neg, hA]
    abel
  have hQl : l + ((1 : ℤ), (1 : ℤ)) = (z + ((1 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 := by
    rw [hcomb_neg, hA]
    abel
  have hcolPl : laplacian F (l + ((0 : ℤ), (1 : ℤ))) = 0 := by
    rw [hPl, laplacian_add_combine hper]
    exact hcolP
  have hcolQl : laplacian F (l + ((1 : ℤ), (1 : ℤ))) = 0 := by
    rw [hQl, laplacian_add_combine hper]
    exact hcolQ
  have hnfPl : Nonfree frame (l + ((0 : ℤ), (1 : ℤ))) := by
    rw [hPl]
    exact PassageRank.nonfree_add_span frame hnfP ⟨-1, 0, rfl⟩
  have hnfQl : Nonfree frame (l + ((1 : ℤ), (1 : ℤ))) := by
    rw [hQl]
    exact PassageRank.nonfree_add_span frame hnfQ ⟨-1, 0, rfl⟩
  have hncfPl : ¬ FreeClosure.freeClosure frame (l + ((0 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfPl s hs ((Set.mem_union _ _ _).2 h)
  have hncfQl : ¬ FreeClosure.freeClosure frame (l + ((1 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfQl s hs ((Set.mem_union _ _ _).2 h)
  -- parities of the label, its north input and its east-north input
  have hPl_even : EvenSite (l + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hlodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hQl_odd : ¬ EvenSite (l + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hlodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  -- the label is white with its prescribed north input (odd entries)
  have hcomb_pos : frame.child.modifiedDeck.combine 1 0 = RowAt.Uvec frame := hU
  have hprescH : frame.prescribedH (-1) z = ((0 : ℤ), (1 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_neg hodd]
  have hFP : FreePolicy.FreePresc frame (-1) l (l + ((0 : ℤ), (1 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame l := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hpermL : permitsQ1 frame F (-1) l (l + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcol, Or.inl ⟨hfc, hFP⟩⟩
  -- the north input `p'` has the horizontal input `q'`
  have hQl_eq_pos : incomingPos (l + ((0 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (1 : ℤ)) := by
    unfold incomingPos
    rw [if_pos hPl_even]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermP : permitsQ1 frame F (-1) (l + ((0 : ℤ), (1 : ℤ))) (l + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcolPl, Or.inr ⟨hncfPl, Or.inr hQl_eq_pos.symm⟩⟩
  -- the east-north input `q'` has the vertical input `ℓ + (1,0)`, the earlier entry
  have hEneg : incomingNeg (l + ((1 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hQl_odd]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermQ : permitsQ1 frame F (-1) (l + ((1 : ℤ), (1 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolQl, Or.inr ⟨hncfQl, Or.inl (by rw [hE_l, hEneg])⟩⟩
  have hRq : Refuted frame F (-1) E C (l + ((1 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolQl hpermQ (Refuted.earlier hE)
  have hRp : Refuted frame F (-1) E C (l + ((0 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolPl hpermP hRq
  exact Refuted.white hcol hpermL hRp

end FLatticePaper.MinusRowOdd
