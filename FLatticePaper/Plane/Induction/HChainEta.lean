import FLatticePaper.Plane.Induction.EasyHRankDiag
import FLatticePaper.Plane.Induction.MinusRowOdd
import FLatticePaper.Plane.Induction.MinusRowRemoval
import FLatticePaper.Plane.Induction.MinusRowEndpoint

/-! # The H-cut refutation chains for an arbitrary sign η

The H-cut chains are the minus-row chains with the sign `η` in place of `−1`: their prescribed inputs on H-chain sites are η-free
(`prescribedH` changes only at `hFirst`), so each proof goes through verbatim. Used for the plus row (`η = 1`) and the minus row
(`η = −1`, recovering the original statements). -/

namespace FLatticePaper.HChainEta

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.EasyHRank FLatticePaper.EasyHRankDiag FLatticePaper.MinusRowWiring FLatticePaper.MinusRowRemoval
open FLatticePaper.MinusRowEndpoint FLatticePaper.OddAxialRank

theorem refuted_even_H_east_free_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
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
  have hprescH : frame.prescribedH η z = ((1 : ℤ), (0 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_pos hpres]
  have hFP : FreePolicy.FreePresc frame η e (e + ((1 : ℤ), (0 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame e := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hperm : permitsQ1 frame F η e (e + ((1 : ℤ), (0 : ℤ))) :=
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

theorem refuted_even_H_diag_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    (hZ : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
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
  have hA : e = z - RowAt.Uvec frame := by
    rw [he, EasyHRank.hAt_sub_den frame (by omega), ← hz]
  have hU := EasyHRank.combine_one_zero_eq_Uvec frame
  have heU : e + frame.child.modifiedDeck.combine 1 0 = z := by
    rw [hU, hA]
    abel
  have hevE : EvenSite e := by
    rw [hA]
    unfold EvenSite at hev ⊢
    have hdn : (frame.child.den + frame.child.num) % 2 = 0 := by
      obtain ⟨hn, hd⟩ := frame.child_odd
      omega
    unfold RowAt.Uvec
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  -- the label is white (deck invariance by `U`)
  have hcol : laplacian F e = 0 := by
    have h := laplacian_add_combine hper e 1 0
    rw [heU] at h
    rw [← h]
    exact FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  have hprescH : frame.prescribedH η z = ((1 : ℤ), (0 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_pos hev]
  have hFP : FreePolicy.FreePresc frame η e (e + ((1 : ℤ), (0 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame e := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hperm : permitsQ1 frame F η e (e + ((1 : ℤ), (0 : ℤ))) :=
    Or.inr ⟨hcol, Or.inl ⟨hfc, hFP⟩⟩
  -- the east neighbour `z + (1,0)`: white and nonfree
  have ht1 : 2 ≤ frame.tGrade z := (tGrade_bounds_of_freeH frame hzfree hev).1
  have ht2 : frame.tGrade z ≤ frame.child.den + frame.child.num - 2 :=
    (tGrade_bounds_of_freeH frame hzfree hev).2
  have hcolp : laplacian F (z + ((1 : ℤ), (0 : ℤ))) = 0 :=
    EastColour.lap_east_zero_of_even_H frame hP.strips hZ hev ht1 ht2
  have hpz : z + ((1 : ℤ), (0 : ℤ)) = (z.1 + 1, z.2) := by
    ext <;> simp
  have hnfp : Nonfree frame (z + ((1 : ℤ), (0 : ℤ))) := by
    rw [hpz]
    exact east_nonfree_of_diag frame hd2 hzfree hev hdiag
  -- the translate by `−U`: `e + (1,0) = (z + (1,0)) + combine (−1) 0`
  have hcomb_neg : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← hU]
    ext <;> simp [PeriodDeck.combine]
  have hsp_eq : e + ((1 : ℤ), (0 : ℤ)) = (z + ((1 : ℤ), (0 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 := by
    rw [hcomb_neg, hA]
    abel
  have hcolq : laplacian F (e + ((1 : ℤ), (0 : ℤ))) = 0 := by
    rw [hsp_eq, laplacian_add_combine hper]
    exact hcolp
  have hnfq : ¬ FreeClosure.freeClosure frame (e + ((1 : ℤ), (0 : ℤ))) := by
    have hnf2 : Nonfree frame (e + ((1 : ℤ), (0 : ℤ))) := by
      rw [hsp_eq]
      exact PassageRank.nonfree_add_span frame hnfp ⟨-1, 0, rfl⟩
    rintro ⟨s, hs, h⟩
    exact hnf2 s hs ((Set.mem_union _ _ _).2 h)
  -- the earlier entry is the vertical input of the east neighbour of the label
  have hodd_q : ¬ EvenSite (e + ((1 : ℤ), (0 : ℤ))) := by
    unfold EvenSite at hevE ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hnext : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = (z.1 + 1, z.2 + 1) - RowAt.Uvec frame := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      EasyHRank.hAt_sub_den frame (show ((m + 1 : ℕ) : ℤ) < frame.child.den by push_cast; omega),
      HChain.hpath_succ, ← hz, hsucc_diag hdiag]
  have hedge : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = incomingPos (e + ((1 : ℤ), (0 : ℤ))) := by
    unfold incomingPos
    rw [if_neg hodd_q, hnext, hA]
    ext <;> simp [RowAt.Uvec] <;> ring
  have hpermq : permitsQ1 frame F η (e + ((1 : ℤ), (0 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolq, Or.inr ⟨hnfq, Or.inr hedge⟩⟩
  have hRq : Refuted frame F η E C (e + ((1 : ℤ), (0 : ℤ))) :=
    Refuted.white hcolq hpermq (Refuted.earlier hE)
  exact Refuted.white hcol hperm hRq

/-! ## The odd axial step: an odd free H point before `hLast` has a free east neighbour -/

theorem refuted_odd_H_white_q_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hqw : laplacian F (HChain.hpath frame m + ((1 : ℤ), (1 : ℤ))) = 0)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
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
  have hprescH : frame.prescribedH η z = ((0 : ℤ), (1 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_neg hodd]
  have hFP : FreePolicy.FreePresc frame η l (l + ((0 : ℤ), (1 : ℤ))) := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ⟨?_, ?_⟩⟩
    · rw [heU]
      exact hzfree
    · rw [heU, hprescH]
  have hfc : FreeClosure.freeClosure frame l := by
    refine ⟨frame.child.modifiedDeck.combine 1 0, ⟨1, 0, rfl⟩, Or.inl ?_⟩
    rw [heU]
    exact hzfree
  have hpermL : permitsQ1 frame F η l (l + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcol, Or.inl ⟨hfc, hFP⟩⟩
  -- the north input `p'` has the horizontal input `q'`
  have hQl_eq_pos : incomingPos (l + ((0 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (1 : ℤ)) := by
    unfold incomingPos
    rw [if_pos hPl_even]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermP : permitsQ1 frame F η (l + ((0 : ℤ), (1 : ℤ))) (l + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hcolPl, Or.inr ⟨hncfPl, Or.inr hQl_eq_pos.symm⟩⟩
  -- the east-north input `q'` has the vertical input `ℓ + (1,0)`, the earlier entry
  have hEneg : incomingNeg (l + ((1 : ℤ), (1 : ℤ))) = l + ((1 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hQl_odd]
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hpermQ : permitsQ1 frame F η (l + ((1 : ℤ), (1 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolQl, Or.inr ⟨hncfQl, Or.inl (by rw [hE_l, hEneg])⟩⟩
  have hRq : Refuted frame F η E C (l + ((1 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolQl hpermQ (Refuted.earlier hE)
  have hRp : Refuted frame F η E C (l + ((0 : ℤ), (1 : ℤ))) :=
    Refuted.white hcolPl hpermP hRq
  exact Refuted.white hcol hpermL hRp

theorem refuted_north_chain_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    {E C : Site → Prop}
    (hy : RefuteTree.Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (1 : ℤ)))) :
    RefuteTree.Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  set z := HChain.hpath frame m with hz
  set e := RowAt.hAt frame ((m : ℤ) - frame.child.den) with he_def
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : z.1 < frame.child.den := by omega
  have hx2 : 2 ≤ z.1 := by omega
  have he : e = z - RowAt.Uvec frame := EasyHRank.hAt_sub_den frame (m := m) (by omega)
  have hU := EasyHRank.combine_one_zero_eq_Uvec frame
  have hcomb_neg : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← hU]
    ext <;> simp [PeriodDeck.combine]
  have hUmem : RowAt.Uvec frame ∈ frame.child.modifiedDeck.span := ⟨1, 0, hU.symm⟩
  have hlapz : laplacian F z = 0 := FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  have hdom : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [FLatticePaper.Induction.hFirst] at h1
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [ChildFrame.hLast] at h1
    omega
  have hprescN : frame.prescribedH η z = ((0 : ℤ), (1 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_neg hodd]
  have heU : e + RowAt.Uvec frame = z := by rw [he]; abel
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hodd' : (z.1 + z.2) % 2 = 1 := by unfold EvenSite at hodd; omega
  have hpar_e : (e.1 + e.2) % 2 = 1 := by
    rw [he]; simp only [Prod.fst_sub, Prod.snd_sub, RowAt.Uvec]; omega
  have hlape : laplacian F e = 0 := by
    have h := laplacian_add_combine hP.periods e 1 0
    rw [hU, heU, hlapz] at h
    exact h.symm
  have hrng := odd_t_range frame hzfree hodd hx2 hzd
  have hcolN : laplacian F (z + ((0 : ℤ), (1 : ℤ))) = 0 :=
    colour_north_odd frame hP.strips hodd hrng.1 hrng.2
  have hw_lap : laplacian F (e + ((0 : ℤ), (1 : ℤ))) = 0 := by
    have h := laplacian_add_combine hP.periods (z + ((0 : ℤ), (1 : ℤ))) (-1) 0
    rw [hcomb_neg, hcolN] at h
    have e_eq : z + ((0 : ℤ), (1 : ℤ)) + -RowAt.Uvec frame = e + ((0 : ℤ), (1 : ℤ)) := by
      rw [he]; abel
    rw [e_eq] at h
    exact h
  have hnfP : Nonfree frame (z + ((0 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_north_odd frame hzfree hodd hx2 hzd)
  have hnfw : Nonfree frame (e + ((0 : ℤ), (1 : ℤ))) := by
    rw [show e + ((0 : ℤ), (1 : ℤ)) = (z + ((0 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 by
      rw [hcomb_neg, he]; abel]
    exact PassageRank.nonfree_add_span frame hnfP ⟨-1, 0, rfl⟩
  have hncf : ¬ FreeClosure.freeClosure frame (e + ((0 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfw s hs ((Set.mem_union _ _ _).2 h)
  have hwE : EvenSite (e + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hincPos_w : incomingPos (e + ((0 : ℤ), (1 : ℤ))) = e + ((1 : ℤ), (1 : ℤ)) := by
    unfold incomingPos
    rw [if_pos hwE]
    exact Prod.ext (by simp; try ring) (by simp; try ring)
  have hpermW : permitsQ1 frame F η (e + ((0 : ℤ), (1 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hw_lap, Or.inr ⟨hncf, Or.inr hincPos_w.symm⟩⟩
  have hRw : RefuteTree.Refuted frame F η E C (e + ((0 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.white hw_lap hpermW hy
  have hfreeE : FreeClosure.freeClosure frame e :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl (by rw [heU]; exact hzfree)⟩
  have hpresE : FreePolicy.FreePresc frame η e (e + ((0 : ℤ), (1 : ℤ))) :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl ⟨by rw [heU]; exact hzfree, by rw [heU, hprescN]⟩⟩
  have hpermE : permitsQ1 frame F η e (e + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hlape, Or.inl ⟨hfreeE, hpresE⟩⟩
  exact RefuteTree.Refuted.white hlape hpermE hRw

theorem refuted_rank4_chain_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) (r : ℤ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH)
    (hblack : laplacian F ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) = -1) :
    RefuteTree.Refuted frame F η (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)))
      (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  set z := HChain.hpath frame m with hz
  set e := RowAt.hAt frame ((m : ℤ) - frame.child.den) with he_def
  have hz1 : z.1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : z.1 < frame.child.den := by omega
  have hx2 : 2 ≤ z.1 := by omega
  have he : e = z - RowAt.Uvec frame := EasyHRank.hAt_sub_den frame (m := m) (by omega)
  have hU := EasyHRank.combine_one_zero_eq_Uvec frame
  have hcomb_neg : frame.child.modifiedDeck.combine (-1) 0 = -RowAt.Uvec frame := by
    rw [← hU]
    ext <;> simp [PeriodDeck.combine]
  have hUmem : RowAt.Uvec frame ∈ frame.child.modifiedDeck.span := ⟨1, 0, hU.symm⟩
  have hlapz : laplacian F z = 0 := FLatticePaper.Induction.laplacian_eq_zero_of_freeH frame hP.strips hzfree
  have hdom : z ≠ FLatticePaper.Induction.hFirst := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [FLatticePaper.Induction.hFirst] at h1
    omega
  have hlast : z ≠ frame.hLast := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [ChildFrame.hLast] at h1
    omega
  have hprescN : frame.prescribedH η z = ((0 : ℤ), (1 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_neg hodd]
  have heU : e + RowAt.Uvec frame = z := by rw [he]; abel
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hodd' : (z.1 + z.2) % 2 = 1 := by unfold EvenSite at hodd; omega
  have hpar_e : (e.1 + e.2) % 2 = 1 := by
    rw [he]; simp only [Prod.fst_sub, Prod.snd_sub, RowAt.Uvec]; omega
  have hlape : laplacian F e = 0 := by
    have h := laplacian_add_combine hP.periods e 1 0
    rw [hU, heU, hlapz] at h
    exact h.symm
  have hnext : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) = e + ((1 : ℤ), (0 : ℤ)) := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      EasyHRank.hAt_sub_den frame (m := m + 1) (by push_cast; omega)]
    have hs : HChain.hpath frame (m + 1) = (z.1 + 1, z.2) := hsucc_east hfree
    rw [hs, he]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  have hrng := odd_t_range frame hzfree hodd hx2 hzd
  have hcolN : laplacian F (z + ((0 : ℤ), (1 : ℤ))) = 0 :=
    colour_north_odd frame hP.strips hodd hrng.1 hrng.2
  have hw_lap : laplacian F (e + ((0 : ℤ), (1 : ℤ))) = 0 := by
    have h := laplacian_add_combine hP.periods (z + ((0 : ℤ), (1 : ℤ))) (-1) 0
    rw [hcomb_neg, hcolN] at h
    have e_eq : z + ((0 : ℤ), (1 : ℤ)) + -RowAt.Uvec frame = e + ((0 : ℤ), (1 : ℤ)) := by
      rw [he]; abel
    rw [e_eq] at h
    exact h
  have hnfP : Nonfree frame (z + ((0 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_north_odd frame hzfree hodd hx2 hzd)
  have hnfw : Nonfree frame (e + ((0 : ℤ), (1 : ℤ))) := by
    rw [show e + ((0 : ℤ), (1 : ℤ)) = (z + ((0 : ℤ), (1 : ℤ))) + frame.child.modifiedDeck.combine (-1) 0 by
      rw [hcomb_neg, he]; abel]
    exact PassageRank.nonfree_add_span frame hnfP ⟨-1, 0, rfl⟩
  have hncf : ¬ FreeClosure.freeClosure frame (e + ((0 : ℤ), (1 : ℤ))) := by
    rintro ⟨s, hs, h⟩
    exact hnfw s hs ((Set.mem_union _ _ _).2 h)
  have hwE : EvenSite (e + ((0 : ℤ), (1 : ℤ))) := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hincPos_w : incomingPos (e + ((0 : ℤ), (1 : ℤ))) = e + ((1 : ℤ), (1 : ℤ)) := by
    unfold incomingPos
    rw [if_pos hwE]
    exact Prod.ext (by simp; try ring) (by simp; try ring)
  have hpermW : permitsQ1 frame F η (e + ((0 : ℤ), (1 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hw_lap, Or.inr ⟨hncf, Or.inr hincPos_w.symm⟩⟩
  have hblack' : laplacian F (z + ((1 : ℤ), (1 : ℤ))) = -1 := hblack
  have hy_lap : laplacian F (e + ((1 : ℤ), (1 : ℤ))) = -1 := by
    have h := laplacian_add_combine hP.periods (z + ((1 : ℤ), (1 : ℤ))) (-1) 0
    rw [hcomb_neg, hblack'] at h
    have e2 : z + ((1 : ℤ), (1 : ℤ)) + -RowAt.Uvec frame = e + ((1 : ℤ), (1 : ℤ)) := by
      rw [he]; abel
    rw [e2] at h
    exact h
  have hodd_y : ¬ EvenSite (e + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hinNeg : incomingNeg (e + ((1 : ℤ), (1 : ℤ))) = e + ((1 : ℤ), (0 : ℤ)) := by
    unfold incomingNeg
    rw [if_neg hodd_y]
    exact Prod.ext (by simp; try ring) (by simp; try ring)
  have hinPos : incomingPos (e + ((1 : ℤ), (1 : ℤ))) = e + ((1 : ℤ), (2 : ℤ)) := by
    unfold incomingPos
    rw [if_neg hodd_y]
    exact Prod.ext (by simp; try ring) (by simp; try ring)
  have hRneg : RefuteTree.Refuted frame F η (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingNeg (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinNeg, ← hnext]
    exact RefuteTree.Refuted.earlier (hAt_mem_earlier frame r m hm2)
  have hRpos : RefuteTree.Refuted frame F η (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingPos (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinPos]
    exact RefuteTree.Refuted.core rfl
  have hRy : RefuteTree.Refuted frame F η (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.black hy_lap hRneg hRpos
  have hRw : RefuteTree.Refuted frame F η (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((0 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.white hw_lap hpermW hRy
  have hfreeE : FreeClosure.freeClosure frame e :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl (by rw [heU]; exact hzfree)⟩
  have hpresE : FreePolicy.FreePresc frame η e (e + ((0 : ℤ), (1 : ℤ))) :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl ⟨by rw [heU]; exact hzfree, by rw [heU, hprescN]⟩⟩
  have hpermE : permitsQ1 frame F η e (e + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hlape, Or.inl ⟨hfreeE, hpresE⟩⟩
  exact RefuteTree.Refuted.white hlape hpermE hRw

theorem refuted_odd_diag_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    RefuteTree.Refuted frame F η E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  apply refuted_north_chain_eta frame F η hP hm1 hm2 hzfree hodd
  have hs : HChain.hpath frame (m + 1) = ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) := by
    show HChain.hsucc frame (HChain.hpath frame m) = _
    unfold HChain.hsucc
    rw [if_neg hdiag]
  have hnext : RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den) =
      RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (1 : ℤ)) := by
    rw [show (m : ℤ) + 1 - frame.child.den = ((m + 1 : ℕ) : ℤ) - frame.child.den by push_cast; ring,
      EasyHRank.hAt_sub_den frame (m := m + 1) (by push_cast; omega), hs,
      EasyHRank.hAt_sub_den frame (m := m) (by omega)]
    exact Prod.ext (by simp only [Prod.fst_add, Prod.fst_sub]; ring) (by simp only [Prod.snd_add, Prod.snd_sub]; ring)
  rw [← hnext]
  exact RefuteTree.Refuted.earlier hE

theorem refuted_hAt_neg_one_eta (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {E C : Site → Prop}
    (hE : E FLatticePaper.Induction.vFirst) :
    RefuteTree.Refuted frame F η E C (RowAt.hAt frame (-1)) := by
  have hsum := hAt_neg_one_add_U frame
  have hlapL : laplacian F frame.hLast = 0 := EndpointStrips.lap_hL hP.strips
  have hlap : laplacian F (RowAt.hAt frame (-1)) = 0 := by
    have h := laplacian_add_combine hP.periods (RowAt.hAt frame (-1)) 1 0
    rw [EasyHRank.combine_one_zero_eq_Uvec frame, hsum, hlapL] at h
    exact h.symm
  have he := hAt_neg_one_eq frame
  have hfree : FreeClosure.freeClosure frame (RowAt.hAt frame (-1)) :=
    ⟨RowAt.Uvec frame, Rank4Fort.uvec_mem_span frame, Or.inl (by rw [hsum]; exact EndpointStrips.fHL frame)⟩
  have hpres : FreePolicy.FreePresc frame η (RowAt.hAt frame (-1)) FLatticePaper.Induction.vFirst :=
    ⟨RowAt.Uvec frame, Rank4Fort.uvec_mem_span frame,
      Or.inl ⟨by rw [hsum]; exact EndpointStrips.fHL frame, by rw [hsum, FaceRows.prescH_hLast, he]; rfl⟩⟩
  have hperm : permitsQ1 frame F η (RowAt.hAt frame (-1)) FLatticePaper.Induction.vFirst :=
    Or.inr ⟨hlap, Or.inl ⟨hfree, hpres⟩⟩
  exact RefuteTree.Refuted.white hlap hperm (RefuteTree.Refuted.earlier hE)


end FLatticePaper.HChainEta
