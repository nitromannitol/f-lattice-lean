import FLatticePaper.Plane.Induction.PlusRowWiring
import FLatticePaper.Plane.Induction.GenH
import FLatticePaper.Plane.Induction.PlusVIndex
import FLatticePaper.Plane.Induction.RankFourStart
import FLatticePaper.Plane.Induction.HChainEta
import FLatticePaper.Plane.Induction.OddAxialRank

/-! # The H block of the plus row is outside the restricted fort (eta = 1, easy regime)

The plus row has the H entries `H_{-1}, …, H_{1-d}` at positions `P0 + t` (`t = 0, …, d-2`), where `P0 = (r+1) + 2 + (L-r-2)` is the
position after the V tail. `H_{-1-t}` is refuted by strong induction on the position: the endpoint `H_{-1}` by the white rule from
`V_0`, and the other entries by `H_entry_gen` (with `eta = 1`, the earlier set being the row prefix, the V bound `V_index_plus`). -/

namespace FLatticePaper.PlusRowH

open FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows FLatticePaper.PlusRowWiring

/-- **The plus H block.** Every site of the plus H block is outside the restricted fort `S` for `permitsQ1 frame F 1`, given that
the earlier sites (all positions before the H block) are outside `S`. -/
theorem plus_H_block_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hnb2 : 2 ≤ frame.child.num) (hpa : 0 ≤ frame.parents.odd.num)
    (hpb : frame.parents.odd.num + 1 ≤ frame.parents.odd.den)
    (hpc : 1 ≤ frame.parents.even.num) (hpe : frame.parents.even.num ≤ frame.parents.even.den)
    (hL : 0 < frame.child.den + frame.child.num)
    (hcap : ∀ (K : ℕ), 3 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    (r : ℤ) (hr : r = frame.parents.odd.den + frame.parents.odd.num)
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z)
    (hEarly : ∀ (j : ℕ) (e' : Site), j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat →
      (plusSites frame r)[j]? = some e' → e' ∉ S) :
    ∀ (k : ℕ) (e : Site), (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat ≤ k →
      k < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + (frame.child.den - 1).toNat →
      (plusSites frame r)[k]? = some e → e ∉ S := by
  obtain ⟨K, hK3, hKs, hKu⟩ := RankFourStart.exists_minimal_K frame.child.num frame.child.den hn1 hnd
  set P0 : ℕ := (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat with hP0
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro e hk1 hk2 he
    have hIHk : ∀ (j : ℕ) (e' : Site), j < k → (plusSites frame r)[j]? = some e' → e' ∉ S := by
      intro j e' hj hje
      by_cases hjr : j < P0
      · exact hEarly j e' hjr hje
      · exact ih j hj e' (by omega) (by omega) hje
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = P0 + t := ⟨k - P0, by omega⟩
    have hrow : (plusSites frame r)[P0 + t]? = some (RowAt.hAt frame (-1 - (t : ℤ))) := by
      have h := plusRow_get_H r (frame.child.den + frame.child.num) frame.child.den (-1 - (t : ℤ)) (by omega) (by omega)
      have hidx : (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat
          + (-1 - (-1 - (t : ℤ))).toNat = P0 + t := by
        rw [hP0]
        omega
      rw [hidx] at h
      unfold plusSites rowSites
      rw [List.getElem?_map, h]
      simp [labelSite]
    rw [hrow] at he
    have he' : e = RowAt.hAt frame (-1 - (t : ℤ)) := (Option.some.inj he).symm
    rw [he']
    by_cases h0 : t = 0
    · subst h0
      have hA : (-1 : ℤ) - ((0 : ℕ) : ℤ) = -1 := by norm_num
      rw [hA]
      have hVF : FLatticePaper.Induction.vFirst ∈ earlierPlus frame r P0 :=
        vFirst_mem_earlierPlus_of_lt frame r hL P0 (by rw [hP0]; omega)
      exact RefuteTree.refuted_not_mem frame F (Or.inl rfl) hS hK
        (E := fun x => x ∈ earlierPlus frame r P0) (C := fun _ => False)
        (fun x hx => by
          obtain ⟨j, hj, hjx⟩ := hx
          exact hIHk j x (by omega) hjx)
        (fun x hx => hx.elim) _
        (HChainEta.refuted_hAt_neg_one_eta frame F 1 hP (E := fun x => x ∈ earlierPlus frame r P0)
          (C := fun _ => False) hVF)
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = frame.child.den - 1 - (t : ℤ) :=
        ⟨(frame.child.den - 1 - (t : ℤ)).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hm2 : (m : ℤ) + 1 < frame.child.den := by omega
      have hentry : entryPosPlus frame r m = P0 + t := by
        unfold entryPosPlus
        rw [hP0]
        have h2 : (-1 - ((m : ℤ) - frame.child.den)).toNat = t := by omega
        rw [h2]
      have hIH' : ∀ x, x ∈ earlierPlus frame r (entryPosPlus frame r m) → x ∉ S := by
        rw [hentry]
        intro x hx
        obtain ⟨j, hj, hjx⟩ := hx
        exact hIHk j x (by omega) hjx
      have hzfree : HChain.hpath frame m ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
      have hz1 : (HChain.hpath frame m).1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
      have hzd : (HChain.hpath frame m).1 < frame.child.den := by omega
      have hx2 : 2 ≤ (HChain.hpath frame m).1 := by omega
      have hVidx : ¬ EvenSite (HChain.hpath frame m) → ∀ x i : Site, frame.openRect x →
          CapRay.ConeRoot (HChain.hpath frame m) K x → EvenSite x → i = incomingPos x →
          i ∈ frame.closedPolygon → ¬ frame.openRect i →
          1 ≤ x.2 - frame.child.num ∧ x.2 - frame.child.num ≤ frame.child.den + frame.child.num - r - 2 := by
        intro hodd x i hx hcone hxe hi _ hiopen
        subst hi
        have hzt := OddAxialRank.odd_t_range frame hzfree hodd hx2 hzd
        rw [hr]
        exact PlusVIndex.V_index_plus frame hx2 hzd hzt hn1 hnd hnb2 hpa hpb hpc hpe hKu hx hcone hxe hiopen
      have hres := GenH.H_entry_gen frame F 1 (Or.inl rfl) hP hsig hZ2 hZ3 hn1 hnd hK3 hKs hKu
        (frame.child.den + frame.child.num - r - 2) (hcap K hK3 hKs hKu) hS hK hm1 hm2
        (fun x => x ∈ earlierPlus frame r (entryPosPlus frame r m))
        (hAt_mem_earlierPlus frame r m hm2)
        (fun k h1 h2 => hEH_plus frame r m k h1 h2)
        (fun k h1 h1' h2 => hEV_plus frame r m k h1 h1' h2)
        hVidx hIH'
      rw [show (m : ℤ) - frame.child.den = -1 - (t : ℤ) by omega] at hres
      exact hres

end FLatticePaper.PlusRowH
