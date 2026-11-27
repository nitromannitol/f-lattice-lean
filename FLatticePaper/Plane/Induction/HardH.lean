import FLatticePaper.Plane.Induction.HardHGap
import FLatticePaper.Plane.Induction.EasyHRankDiag
import FLatticePaper.Plane.Induction.OddAxialRank
import FLatticePaper.Plane.Induction.HChainEta

namespace FLatticePaper.HardH

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.EasyHRank
open FLatticePaper.EasyHRankDiag FLatticePaper.OddAxialRank FLatticePaper.HGap

/-- The hd2-free gap at a free even H point (F6). -/
theorem sGrade_lt_of_freeH_even_free (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    frame.sGrade z < frame.child.periodDenominator + 2 - 2 * frame.child.den := by
  obtain ⟨hn0, hnd, hnd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hcop : IsCoprime frame.child.den frame.child.num := frame.child_reduced.symm
  have hid := FLatticePaper.FreeVOrdinate.T_mul_ordinate frame z
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨hE, -, hsp⟩ := hz
  unfold ChildFrame.closedPolygon at hE
  simp only [Set.mem_setOf_eq, if_pos hev] at hE
  obtain ⟨-, -, -, hs_hi⟩ := hE
  -- the parity of `t` at an even site (`n`, `d` odd)
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have hev' : (z.1 + z.2) % 2 = 0 := by
    unfold EvenSite at hev
    exact hev
  have e : frame.tGrade z = (z.1 - z.2) + 2 * (a * z.1 - b * z.2) := by
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  have htev : frame.tGrade z % 2 = 0 := by
    rw [e]
    generalize a * z.1 - b * z.2 = X
    omega
  unfold ChildFrame.hSpectrum at hsp
  obtain ⟨ht1, ht2⟩ : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    rcases hsp with ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · exact ⟨h2, h3⟩
    · omega
  by_contra hcon
  push Not at hcon
  rw [hT] at hcon hs_hi hid
  exact FLatticePaper.HardHGap.gap_arith_free (n := frame.child.num) (d := frame.child.den) (t := frame.tGrade z)
    (s := frame.sGrade z) (u := z.2) (by omega) (by omega) hdodd hcop hid ht1 ht2 htev hcon hs_hi

theorem den_sub_num_lt_tGrade_free (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) (hdiag : (z.1 + 1, z.2) ∉ frame.freeH) :
    frame.child.den - frame.child.num < frame.tGrade z := by
  by_contra hle
  push Not at hle
  apply hdiag
  obtain ⟨ht1, -⟩ := tGrade_bounds_of_freeH frame hz hev
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
    exact hz.1
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hs := sGrade_lt_of_freeH_even_free frame hz hev
  have hs0 : 0 ≤ frame.sGrade z := by
    unfold ChildFrame.closedPolygon at hcl
    simp only [Set.mem_setOf_eq, if_pos hev] at hcl
    exact hcl.2.2.1
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hT0 : 0 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have eTp : frame.tGrade (z.1 + 1, z.2) = frame.tGrade z + frame.child.num := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have eSp : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have eTb : frame.tGrade (z.1 + 1, z.2 - 1) = frame.tGrade z + frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hpodd : ¬ EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite
    dsimp only
    omega
  have hbev : EvenSite (z.1 + 1, z.2 - 1) := by
    unfold EvenSite
    dsimp only
    omega
  have htpar := tGrade_even_parity frame hev
  have hmem : (z.1 + 1, z.2) ∈ frame.freeH := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · unfold ChildFrame.closedPolygon
      simp only [Set.mem_setOf_eq]
      rw [if_neg hpodd, eTp, eSp]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · intro hc
      unfold ChildFrame.closedPolygon at hc
      simp only [Set.mem_setOf_eq] at hc
      rw [if_pos hbev, eTb] at hc
      linarith [hc.2.1]
    · unfold ChildFrame.hSpectrum
      right
      rw [eTp]
      refine ⟨by omega, by linarith, by linarith⟩
  exact hmem

theorem east_nonfree_of_diag_free (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) (hdiag : (z.1 + 1, z.2) ∉ frame.freeH) :
    Nonfree frame (z.1 + 1, z.2) := by
  have ht := den_sub_num_lt_tGrade_free frame hz hev hdiag
  obtain ⟨ht1, ht2⟩ := tGrade_bounds_of_freeH frame hz hev
  have hs := sGrade_lt_of_freeH_even_free frame hz hev
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
    exact hz.1
  have hs0 : 0 ≤ frame.sGrade z := by
    unfold ChildFrame.closedPolygon at hcl
    simp only [Set.mem_setOf_eq, if_pos hev] at hcl
    exact hcl.2.2.1
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  have hbigT : frame.child.den + frame.child.num - 2 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have eTT : W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hTd]
    unfold W1.w1T
    ring
  obtain ⟨q, hq⟩ : ∃ q : Site, q = (z.1 + 1 + (frame.child.num - frame.child.den),
      z.2 + (frame.child.num + frame.child.den)) := ⟨_, rfl⟩
  have hqodd : ¬ EvenSite q := by
    rw [hq]
    unfold EvenSite
    dsimp only
    omega
  have eTq : W1.w1t frame.child.num frame.child.den q = frame.tGrade z + frame.child.num - W1.w1T frame.child.num frame.child.den := by
    rw [hq]
    unfold W1.w1t W1.w1T ChildFrame.tGrade
    dsimp only
    ring
  have eSq : W1.w1s frame.child.num frame.child.den q = frame.sGrade z + (frame.child.den + frame.child.num) := by
    rw [hq]
    unfold W1.w1s ChildFrame.sGrade
    dsimp only
    ring
  have hSI : W1.StrictInterior frame.child.num frame.child.den q := by
    unfold W1.StrictInterior
    simp only [W1.w1b, W1.w1a, W1.w1h, W1.w1c, hqodd, if_false]
    rw [eTq, eSq, eTT]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hnq : Nonfree frame q := strictInterior_nonfree frame hSI
  have hVn : -frame.child.modifiedDeck.transverse ∈ frame.child.modifiedDeck.span :=
    ⟨0, -1, by ext <;> simp [PeriodDeck.combine]⟩
  have hVeq : frame.child.modifiedDeck.transverse =
      (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
    EndpointDeck.transverse_eq_Vdeck frame
  have hqp : q + -frame.child.modifiedDeck.transverse = (z.1 + 1, z.2) := by
    rw [hq, hVeq]
    ext <;> simp <;> ring
  have := PassageRank.nonfree_add_span frame hnq hVn
  rwa [hqp] at this

theorem si_q_odd_free (frame : ChildFrame) {z : Site}
    (hz : z ∈ frame.freeH) (hodd : ¬ EvenSite z) (hx2 : 2 ≤ z.1) (hxd : z.1 < frame.child.den)
    (hE : (z.1 + 1, z.2) ∈ frame.freeH) :
    FLatticePaper.W1.StrictInterior frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ))) := by
  obtain ⟨hn0, hnd, hd2', hd3, hTd⟩ := frame.child_facts
  have hrange := odd_t_range frame hz hodd hx2 hxd
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
    exact hz.1
  have hslo : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z := by
    unfold ChildFrame.closedPolygon at hcl
    simp only [Set.mem_setOf_eq] at hcl
    rw [if_neg hodd] at hcl
    exact hcl.2.2.1
  have hEven : EvenSite (z.1 + 1, z.2) := by
    unfold EvenSite at hodd ⊢
    dsimp only
    omega
  have hHE := sGrade_lt_of_freeH_even_free frame hE hEven
  have eSE : frame.sGrade (z.1 + 1, z.2) = frame.sGrade z + (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hqO : ¬ EvenSite (z + ((1 : ℤ), (1 : ℤ))) := by
    unfold EvenSite at hodd ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have eT : FLatticePaper.W1.w1t frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eS : FLatticePaper.W1.w1s frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.sGrade z + 2 * frame.child.den := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have eA : FLatticePaper.W1.w1b frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ))) = frame.child.den := by
    unfold FLatticePaper.W1.w1b
    rw [if_neg hqO]
  have eA2 : FLatticePaper.W1.w1a frame.child.num (z + ((1 : ℤ), (1 : ℤ))) = frame.child.num := by
    unfold FLatticePaper.W1.w1a
    rw [if_neg hqO]
  have eH : FLatticePaper.W1.w1h frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = frame.child.den + frame.child.num - 2 := by
    unfold FLatticePaper.W1.w1h
    rw [if_neg hqO]
  have eC : FLatticePaper.W1.w1c frame.child.num frame.child.den (z + ((1 : ℤ), (1 : ℤ)))
      = 2 - frame.child.den + frame.child.num := by
    unfold FLatticePaper.W1.w1c
    rw [if_neg hqO]
  have eTT : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := by
    rw [hTd]
    unfold FLatticePaper.W1.w1T
    ring
  have hT : 2 * frame.child.den < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  unfold FLatticePaper.W1.StrictInterior
  rw [eA, eA2, eH, eC, eT, eS, eTT]
  rw [eSE] at hHE
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hrange.1, hrange.2]


theorem refuted_even_H_diag_free (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    
    (hZ : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hev : EvenSite (HChain.hpath frame m))
    (hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH)
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
  have hprescH : frame.prescribedH (-1) z = ((1 : ℤ), (0 : ℤ)) := by
    unfold ChildFrame.prescribedH
    rw [if_neg hdom, if_neg hlast, if_pos hev]
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
    exact east_nonfree_of_diag_free frame hzfree hev hdiag
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
  have hpermq : permitsQ1 frame F (-1) (e + ((1 : ℤ), (0 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolq, Or.inr ⟨hnfq, Or.inr hedge⟩⟩
  have hRq : Refuted frame F (-1) E C (e + ((1 : ℤ), (0 : ℤ))) :=
    Refuted.white hcolq hpermq (Refuted.earlier hE)
  exact Refuted.white hcol hperm hRq

/-! ## The odd axial step: an odd free H point before `hLast` has a free east neighbour -/

theorem refuted_odd_H_axial_free (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    
    (hZ : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hlate : frame.child.den + 2 - 2 * frame.child.num ≤ frame.tGrade (HChain.hpath frame m))
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
  have hcolQ : laplacian F (z + ((1 : ℤ), (1 : ℤ))) = 0 :=
    colour_q_odd frame hP.strips hZ hodd hrng2 hlate
  -- strict interior, hence nonfree
  have hcl : z ∈ frame.closedPolygon := by
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hzfree
    exact hzfree.1
  have hnfP : Nonfree frame (z + ((0 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_north_odd frame hzfree hodd hx2 hxd)
  have hnfQ : Nonfree frame (z + ((1 : ℤ), (1 : ℤ))) :=
    strictInterior_nonfree frame (si_q_odd_free frame hzfree hodd hx2 hxd hEast)
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

end FLatticePaper.HardH
