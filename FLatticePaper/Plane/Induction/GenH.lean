import FLatticePaper.Plane.Induction.GenStart
import FLatticePaper.Plane.Induction.HChainEta
import FLatticePaper.Plane.Induction.RankFourStart

/-! # The H entries for an arbitrary sign η and an arbitrary earlier predicate

`rank4_chain_gen`: the rank-4 chain with the earlier set `E` and its east-label membership `hE_next` as inputs.
`H_entry_gen`: each H entry `hAt(m−d)`, `1 ≤ m ≤ d−2`, is outside a restricted fort for `permitsQ1 frame F η`, under the induction
hypothesis on `E` and the row inputs `hEH`, `hEV`, `hVidx`. The cases are the η-generic chains of `HChainEta` and the start
exclusion of `GenStart`; the colour is binary (`Packet.binary`). -/

namespace FLatticePaper.GenH

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.EasyHRank FLatticePaper.EasyHRankDiag FLatticePaper.MinusRowWiring FLatticePaper.MinusRowRemoval
open FLatticePaper.MinusRowEndpoint FLatticePaper.OddAxialRank FLatticePaper.HChainEta FLatticePaper.GenStart
open FLatticePaper.RankFourStart

theorem rank4_chain_gen (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hzfree : HChain.hpath frame m ∈ frame.freeH) (hodd : ¬ EvenSite (HChain.hpath frame m))
    (hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH)
    (hblack : laplacian F ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2 + 1) = -1)
    {E : Site → Prop} (hE_next : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    RefuteTree.Refuted frame F η E
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
  have hRneg : RefuteTree.Refuted frame F η E
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingNeg (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinNeg, ← hnext]
    exact RefuteTree.Refuted.earlier hE_next
  have hRpos : RefuteTree.Refuted frame F η E
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (incomingPos (e + ((1 : ℤ), (1 : ℤ)))) := by
    rw [hinPos]
    exact RefuteTree.Refuted.core rfl
  have hRy : RefuteTree.Refuted frame F η E
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((1 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.black hy_lap hRneg hRpos
  have hRw : RefuteTree.Refuted frame F η E
      (fun x => x = e + ((1 : ℤ), (2 : ℤ))) (e + ((0 : ℤ), (1 : ℤ))) :=
    RefuteTree.Refuted.white hw_lap hpermW hRy
  have hfreeE : FreeClosure.freeClosure frame e :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl (by rw [heU]; exact hzfree)⟩
  have hpresE : FreePolicy.FreePresc frame η e (e + ((0 : ℤ), (1 : ℤ))) :=
    ⟨RowAt.Uvec frame, hUmem, Or.inl ⟨by rw [heU]; exact hzfree, by rw [heU, hprescN]⟩⟩
  have hpermE : permitsQ1 frame F η e (e + ((0 : ℤ), (1 : ℤ))) :=
    Or.inr ⟨hlape, Or.inl ⟨hfreeE, hpresE⟩⟩
  exact RefuteTree.Refuted.white hlape hpermE hRw


/-- **An H entry is outside the fort for an arbitrary sign η and an arbitrary earlier predicate.** The earlier predicate `E`
contains the east H label, the later H labels `hpath k − U` and the V labels `vpath k` (`k ≤ B`), and the induction hypothesis
`hIH` says that `E`-sites are outside the fort. The colour of `z + (1,1)` is binary, so no colour input is needed. -/
theorem H_entry_gen (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    {K : ℕ} (hK3 : 3 ≤ K)
    (hKs : frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ))
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    (B : ℤ)
    (hcap : ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
      ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (E : Site → Prop) (hE_next : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)))
    (hEH : ∀ k : ℕ, ((m : ℤ) + 1 ≤ (k : ℤ)) → (k : ℤ) < frame.child.den →
      E (HChain.hpath frame k - RowAt.Uvec frame))
    (hEV : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → 1 ≤ (k : ℤ) → (k : ℤ) ≤ B →
      E (VChain.vpath frame k))
    (hVidx : ¬ EvenSite (HChain.hpath frame m) → ∀ x i : Site, frame.openRect x →
      CapRay.ConeRoot (HChain.hpath frame m) K x → EvenSite x →
      i = incomingPos x → i ∈ frame.closedPolygon → ¬ frame.openRect i →
      1 ≤ x.2 - frame.child.num ∧ x.2 - frame.child.num ≤ B)
    (hIH : ∀ x, E x → x ∉ S) :
    RowAt.hAt frame ((m : ℤ) - frame.child.den) ∉ S := by
  have hzfree : HChain.hpath frame m ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hz1 : (HChain.hpath frame m).1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : (HChain.hpath frame m).1 < frame.child.den := by omega
  have hx2 : 2 ≤ (HChain.hpath frame m).1 := by omega
  have hper := hP.periods
  by_cases hev : EvenSite (HChain.hpath frame m)
  · by_cases hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH
    · exact RefuteTree.refuted_not_mem frame F hη hS hK (C := fun _ => False) hIH (fun x hx => False.elim hx) _
        (refuted_even_H_east_free_eta frame F η hP hper hm1 hm2 hev hfree hE_next)
    · exact RefuteTree.refuted_not_mem frame F hη hS hK (C := fun _ => False) hIH (fun x hx => False.elim hx) _
        (refuted_even_H_diag_eta frame F η hP hper hnd hZ2 hm1 hm2 hev hfree hE_next)
  · have hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH :=
      EasyHRankDiag.east_freeH_of_odd frame hzfree hev (by omega) hzd
    rcases hP.binary (HChain.hpath frame m + ((1 : ℤ), (1 : ℤ))) with hb | hw
    · obtain ⟨p, q, hs, hcq⟩ := hcap
      have hrank4 := rank4_chain_gen frame F η hP hm1 hm2 hzfree hev hfree hb hE_next
      have hstart : ∀ x : Site, x = RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) → x ∉ S := by
        rintro x rfl
        exact rank4_start_gen frame F η hP hsig hZ3 hn1 hnd hm1 hm2 hzfree hev hb hK3 hKs hKu hs
          hcq hS {x | E x} (fun e he => hIH e he) B
          (fun k h1 h2 => hEH k h1 h2) hEV (hVidx hev)
      exact RefuteTree.refuted_not_mem frame F hη hS hK hIH hstart _ hrank4
    · exact RefuteTree.refuted_not_mem frame F hη hS hK (C := fun _ => False) hIH (fun x hx => False.elim hx) _
        (refuted_odd_H_white_q_eta frame F η hP hper hnd hm1 hm2 hev hw hE_next)

end FLatticePaper.GenH
