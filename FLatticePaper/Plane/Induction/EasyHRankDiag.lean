import FLatticePaper.Plane.Induction.EasyHRank
import FLatticePaper.Plane.Induction.EastColour
import FLatticePaper.Plane.Induction.HGap
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.PassageRank

/-! # Rank 2 of the easy H entries: the diagonal successor (east step not free)

For a free even H point `z = hpath m` (`1 ≤ m`, `m + 1 < d`) whose east neighbour `(z.1 + 1, z.2)` is not free, the successor is the
diagonal `z + (1,1)` (`HChain.hsucc`). The label `H_{m−d} = z − U` (`RowAt.hAt`) is refuted by the white rule through its prescribed
input `p − U`, with `p = z + (1,0)`:
* the label is white (`z` free) and its prescribed input is `p − U` (`FreePresc`, `prescribedH = (1,0)` on the even label);
* `p` is white (`EastColour.lap_east_zero_of_even_H`, with the child's extended even zero input `hZ`) and nonfree
  (`east_nonfree_of_diag`: the translate `p + transverse` lies in the strict interior, in the easy regime `2n ≤ d`);
* `p − U` is white and nonfree, so its permitted input is any input; the input `z + (1,1) − U = hAt (m+1−d)` is the earlier entry.

The split is numerical (`scratchpad/rank2.py`): on all proper words of length ≤ 6 the diagonal case always has an even `z`
(56028 cases), and in the easy regime every odd chain entry has a free east step. -/

namespace FLatticePaper.EasyHRankDiag

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.EasyHRank

/-- The parity of `t` at an even site (`n`, `d` odd). -/
theorem tGrade_even_parity (frame : ChildFrame) {z : Site} (hev : EvenSite z) : frame.tGrade z % 2 = 0 := by
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨a, ha⟩ : ∃ a, frame.child.num = 2 * a + 1 := ⟨frame.child.num / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, frame.child.den = 2 * b + 1 := ⟨frame.child.den / 2, by omega⟩
  have e : frame.tGrade z = (z.1 - z.2) + 2 * (a * z.1 - b * z.2) := by
    unfold ChildFrame.tGrade
    rw [ha, hb]
    ring
  have hev' : (z.1 + z.2) % 2 = 0 := hev
  rw [e]
  generalize a * z.1 - b * z.2 = X
  omega

/-- The grades of a free even H point: `2 ≤ t ≤ d + n − 2`. -/
theorem tGrade_bounds_of_freeH (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z) :
    2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨-, -, hsp⟩ := hz
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨-, h2, h3⟩ | ⟨h1, -⟩
  · exact ⟨h2, h3⟩
  · have := tGrade_even_parity frame hev
    omega

/-- The diagonal successor: if the east neighbour of `z` is not free, `hsucc z = z + (1,1)`. -/
theorem hsucc_diag {frame : ChildFrame} {z : Site} (h : (z.1 + 1, z.2) ∉ frame.freeH) :
    HChain.hsucc frame z = (z.1 + 1, z.2 + 1) := by
  unfold HChain.hsucc
  rw [if_neg h]

/-- **The east step of a diagonal free even H point is not free.** If `z` is a free even H point with `t(z) ≤ d − n`, the east
neighbour is in the closed polygon with odd H spectrum, so it is free; hence a diagonal step has `t(z) > d − n`. -/
theorem den_sub_num_lt_tGrade (frame : ChildFrame) (hd2 : 2 * frame.child.num ≤ frame.child.den) {z : Site}
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
  have hs := HGap.sGrade_lt_of_freeH_even frame hd2 hz hev
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

/-- **The east neighbour of a diagonal free even H point is nonfree.** In the easy regime `2n ≤ d`: its translate by the transverse
deck vector lies in the strict interior (`t` by `t(z) > d − n`, `s` by the gap `s(z) < T + 2 − 2d`). -/
theorem east_nonfree_of_diag (frame : ChildFrame) (hd2 : 2 * frame.child.num ≤ frame.child.den) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) (hdiag : (z.1 + 1, z.2) ∉ frame.freeH) :
    Nonfree frame (z.1 + 1, z.2) := by
  have ht := den_sub_num_lt_tGrade frame hd2 hz hev hdiag
  obtain ⟨ht1, ht2⟩ := tGrade_bounds_of_freeH frame hz hev
  have hs := HGap.sGrade_lt_of_freeH_even frame hd2 hz hev
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

/-- **Rank 2, the diagonal case.** For a free even H point `z = hpath m` whose east neighbour is not free, the label `H_{m−d}` is
refuted by the white rule through `z + (1,0) − U`, which is refuted by the earlier entry `H_{m+1−d} = z + (1,1) − U`. -/
theorem refuted_even_H_diag (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hd2 : 2 * frame.child.num ≤ frame.child.den)
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
  have hpermq : permitsQ1 frame F (-1) (e + ((1 : ℤ), (0 : ℤ))) (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) :=
    Or.inr ⟨hcolq, Or.inr ⟨hnfq, Or.inr hedge⟩⟩
  have hRq : Refuted frame F (-1) E C (e + ((1 : ℤ), (0 : ℤ))) :=
    Refuted.white hcolq hpermq (Refuted.earlier hE)
  exact Refuted.white hcol hperm hRq

end FLatticePaper.EasyHRankDiag
