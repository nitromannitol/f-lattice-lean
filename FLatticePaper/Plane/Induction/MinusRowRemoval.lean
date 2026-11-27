import FLatticePaper.Plane.Induction.MinusRowEndpoint
import FLatticePaper.Plane.Induction.OddAxialRank
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.StrictNonfree
import FLatticePaper.Plane.Induction.PassageRank
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeClosure

/-! # Row removal with a position-dependent core, and the rank-4 chain at an east-free odd black H entry

`row_removed_pos`: the row removal of `RefuteTree.row_removed_of_refuted` with the core `C k` allowed to depend on the position `k`;
its hypothesis `hC` may use the earlier entries (induction), which is what the rank-4 start exclusion needs.

`refuted_rank4_chain`: for an odd free H entry `e = z − U` (`z = hpath m`) with east step free and black `z + (1,1)`, `e` is refuted
by the white/black rules from `E` (the earlier entries) and the core `C = {e + (1,2)}` (the rank-4 start `z + (1,2) − U`):
`e → e + (0,1)` (free white, prescribed north) `→ e + (1,1)` (nonfree white, east input) `→` (black) `{e + (1,0), e + (1,2)}`,
where `e + (1,0) = H_{m+1−d}` is earlier and `e + (1,2)` is the core. -/

namespace FLatticePaper.MinusRowRemoval

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.MinusRowWiring FLatticePaper.EasyHRank FLatticePaper.OddAxialRank

/-- **Row removal with a position-dependent core.** -/
theorem row_removed_pos (frame : ChildFrame) (F : Field) {η : ℤ} (hη : η = 1 ∨ η = -1) {S : Set Site}
    (hres : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z)
    {C : ℕ → Site → Prop} (row : List Site)
    (href : ∀ (k : ℕ) (e : Site), row[k]? = some e →
      Refuted frame F η (fun x => ∃ j : ℕ, j < k ∧ row[j]? = some x) (C k) e)
    (hC : ∀ (k : ℕ) (x : Site), C k x →
      (∀ (j : ℕ) (e' : Site), j < k → row[j]? = some e' → e' ∉ S) → x ∉ S) :
    ∀ (k : ℕ) (e : Site), row[k]? = some e → e ∉ S := by
  refine FreeRows.ordered_removal_list S row ?_
  intro k e he hmem hIH
  have hE : ∀ x, (∃ j : ℕ, j < k ∧ row[j]? = some x) → x ∉ S := by
    rintro x ⟨j, hj, hjx⟩
    exact hIH j x hj hjx
  exact (RefuteTree.refuted_not_mem frame F hη hres hK hE (fun x hx => hC k x hx hIH) e (href k e he)) hmem

/-- **The rank-4 chain.** The odd free H entry `e = hAt(m−d) = z − U` with an east-free step and a black `z + (1,1)` is refuted from
the earlier entries (`H_{m+1−d}`) and the core `C = {e + (1,2)}`. -/
theorem refuted_rank4_chain (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (r : ℤ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH)
    (hblack : laplacian F ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) = -1) :
    RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m))
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
  have hprescN : frame.prescribedH (-1) z = ((0 : ℤ), (1 : ℤ)) := by
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
  have hpermW : permitsQ1 frame F (-1) (e + ((0 : ℤ), (1 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
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
  have hRneg : RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingNeg (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinNeg, ← hnext]
    exact RefuteTree.Refuted.earlier (hAt_mem_earlier frame r m hm2)
  have hRpos : RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingPos (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinPos]
    exact RefuteTree.Refuted.core rfl
  have hRy : RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.black hy_lap hRneg hRpos
  have hRw : RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m))
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((0 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.white hw_lap hpermW hRy
  have hfreeE : FreeClosure.freeClosure frame e :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl (by rw [heU]; exact hzfree)⟩
  have hpresE : FreePolicy.FreePresc frame (-1) e (e + ((0 : ℤ), (1 : ℤ))) :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl ⟨by rw [heU]; exact hzfree, by rw [heU, hprescN]⟩⟩
  have hpermE : permitsQ1 frame F (-1) e (e + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hlape, Or.inl ⟨hfreeE, hpresE⟩⟩
  exact RefuteTree.Refuted.white hlape hpermE hRw

/-- **The north chain.** If the east-north input `e + (1,1)` of the odd free H entry `e = hAt(m−d)` is refuted, so is `e`: `e`
is free white with prescribed north input `e + (0,1)`, which is nonfree white with the east input `e + (1,1)`. -/
theorem refuted_north_chain (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    {E C : Site → Prop}
    (hy : RefuteTree.Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (1 : ℤ)))) :
    RefuteTree.Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
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
  have hprescN : frame.prescribedH (-1) z = ((0 : ℤ), (1 : ℤ)) := by
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
  have hpermW : permitsQ1 frame F (-1) (e + ((0 : ℤ), (1 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hw_lap, Or.inr ⟨hncf, Or.inr hincPos_w.symm⟩⟩
  have hRw : RefuteTree.Refuted frame F (-1) E C (e + ((0 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.white hw_lap hpermW hy
  have hfreeE : FreeClosure.freeClosure frame e :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl (by rw [heU]; exact hzfree)⟩
  have hpresE : FreePolicy.FreePresc frame (-1) e (e + ((0 : ℤ), (1 : ℤ))) :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl ⟨by rw [heU]; exact hzfree, by rw [heU, hprescN]⟩⟩
  have hpermE : permitsQ1 frame F (-1) e (e + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hlape, Or.inl ⟨hfreeE, hpresE⟩⟩
  exact RefuteTree.Refuted.white hlape hpermE hRw

/-- **The odd H entry with a diagonal step.** `H_{m+1−d}` is `z + (1,1) − U`, the east-north input itself, so the north chain
refutes `e` from the earlier entry `H_{m+1−d}`. -/
theorem refuted_odd_diag (frame : ChildFrame) (F : Field) (hP : frame.Packet F) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH)
    {E C : Site → Prop} (hE : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    RefuteTree.Refuted frame F (-1) E C (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  apply refuted_north_chain frame F hP hm1 hm2 hzfree hodd
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

end FLatticePaper.MinusRowRemoval
