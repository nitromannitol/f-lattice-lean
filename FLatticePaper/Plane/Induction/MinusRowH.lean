import FLatticePaper.Plane.Induction.RankFourStart
import FLatticePaper.Plane.Induction.MinusRowOdd
import FLatticePaper.Plane.Induction.MinusRowEndpoint

/-! # The minus-row H entries are outside the fort, under the row induction

For `e = hAt(m−d) = hpath m − U` with `1 ≤ m ≤ d − 2`, the refutation is chosen by the chain data.
* Even `z`, free east step: rank 1. Even `z`, diagonal step: rank 2.
* Odd `z` (its east step is always free, `EasyHRankDiag.east_freeH_of_odd`): the colour of `q = z + (1,1)` is binary.
  If `lap q = 0`, the rank-3 chain refutes `e` (`MinusRowOdd.refuted_odd_H_white_q`), with no lateness.
  If `lap q = −1`, the rank-4 chain refutes `e` with the start `e + (1,2)` as its core, and the start is excluded by
  `RankFourStart.rank4_start_not_mem` under the row induction.
No colour input is assumed. The earlier set is the row prefix `earlierAt`. -/

namespace FLatticePaper.MinusRowH

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.MinusRowWiring FLatticePaper.MinusRowRemoval FLatticePaper.RankFourStart FLatticePaper.EasyHRank
open FLatticePaper.EasyHRankDiag FLatticePaper.MinusRowEndpoint

/-- **An H entry `e = hAt(m−d)`, `1 ≤ m ≤ d−2`, is outside the fort** under the row induction (`hIH` on its earlier set). -/
theorem H_entry_not_mem (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num) (hr0 : 0 ≤ frame.parents.odd.den + frame.parents.odd.num)
    (hcap : ∀ (K : ℕ), 3 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    (hIH : ∀ x ∈ earlierAt frame (frame.parents.odd.den + frame.parents.odd.num)
      (entryPos frame (frame.parents.odd.den + frame.parents.odd.num) m), x ∉ S) :
    RowAt.hAt frame ((m : ℤ) - frame.child.den) ∉ S := by
  set r := frame.parents.odd.den + frame.parents.odd.num with hr
  have hper := hP.periods
  have hzfree : HChain.hpath frame m ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hz1 : (HChain.hpath frame m).1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : (HChain.hpath frame m).1 < frame.child.den := by omega
  have hx2 : 2 ≤ (HChain.hpath frame m).1 := by omega
  have hE : ∀ x, (fun x => x ∈ earlierAt frame r (entryPos frame r m)) x → x ∉ S := fun x hx => hIH x hx
  have hnot : ∀ (C : Site → Prop), (∀ x, C x → x ∉ S) →
      RefuteTree.Refuted frame F (-1) (fun x => x ∈ earlierAt frame r (entryPos frame r m)) C
        (RowAt.hAt frame ((m : ℤ) - frame.child.den)) → RowAt.hAt frame ((m : ℤ) - frame.child.den) ∉ S :=
    fun C hC href => RefuteTree.refuted_not_mem frame F (Or.inr rfl) hS hK hE hC _ href
  by_cases hev : EvenSite (HChain.hpath frame m)
  · by_cases hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH
    · exact hnot (fun _ => False) (fun x hx => hx.elim)
        (minus_refuted_even_east frame F hP hper r hm1 hm2 hev hfree)
    · have hdiag : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∉ frame.freeH := hfree
      exact hnot (fun _ => False) (fun x hx => hx.elim)
        (minus_refuted_even_diag frame F hP hper r hnd hZ2 hm1 hm2 hev hdiag)
  · have hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH :=
      EasyHRankDiag.east_freeH_of_odd frame hzfree hev (by omega) hzd
    rcases hP.binary (HChain.hpath frame m + ((1 : ℤ), (1 : ℤ))) with hb | hw
    · obtain ⟨K, hK3, hKs, hKu⟩ := exists_minimal_K frame.child.num frame.child.den hn1 hnd
      obtain ⟨p, q, hs, hcq⟩ := hcap K hK3 hKs hKu
      have hrank4 := refuted_rank4_chain frame F hP r hm1 hm2 hzfree hev hfree hb
      have hstart : ∀ x : Site, x = RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ)) → x ∉ S := by
        rintro x rfl
        exact rank4_start_not_mem frame F hP hsig hZ3 hn1 hnd hNo hr0 hm1 hm2 hzfree hev hb hK3 hKs hKu hs
          hcq hS hIH
      exact hnot (fun x => x = RowAt.hAt frame ((m : ℤ) - frame.child.den) + ((1 : ℤ), (2 : ℤ))) hstart hrank4
    · exact hnot (fun _ => False) (fun x hx => hx.elim)
        (MinusRowOdd.refuted_odd_H_white_q frame F hP hper hnd hm1 hm2 hev hw (hAt_mem_earlier frame r m hm2))

/-- The row site at position `r + 2 + (−1 − j)` of the minus row is the H entry `hAt j`, for `1 − d ≤ j ≤ −1`. -/
theorem minusSites_H (frame : ChildFrame) (r : ℤ) (j : ℤ) (hj1 : 1 - frame.child.den ≤ j) (hj2 : j ≤ -1) :
    (minusSites frame r)[r.toNat + 2 + (-1 - j).toNat]? = some (RowAt.hAt frame j) := by
  unfold minusSites rowSites
  rw [List.getElem?_map, minusRow_get_H _ _ _ _ hj1 hj2]
  simp [labelSite]

/-- **The H block of the minus row is outside the fort.** Positions `r + 2 ≤ k < r + 2 + (d − 1)` are the H entries
`H_{-1}, …, H_{1−d}`; the positions below `r + 2` (the V entries `V_r, …, V_1`, `H_0`, `V_0`) are outside the fort by `hEarly`. -/
theorem minus_H_block_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hsig : ∀ w ∈ frame.closedPolygon, F w - F (w - frame.shortShift) ≤ 0)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hNo : 1 ≤ frame.parents.odd.num) (hr0 : 0 ≤ frame.parents.odd.den + frame.parents.odd.num)
    (hcap : ∀ (K : ℕ), 3 ≤ K → frame.child.den + 2 * frame.child.num - 1 ≤ frame.child.num * (K : ℤ) →
      frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2 →
      ∃ p q : ℤ, frame.child.num * p - frame.child.den * q = 2 - frame.child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)))
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z)
    (hEarly : ∀ (j : ℕ) (e' : Site), j < (frame.parents.odd.den + frame.parents.odd.num).toNat + 2 →
      (minusSites frame (frame.parents.odd.den + frame.parents.odd.num))[j]? = some e' → e' ∉ S) :
    ∀ (k : ℕ) (e : Site), (frame.parents.odd.den + frame.parents.odd.num).toNat + 2 ≤ k →
      (k : ℤ) < (frame.parents.odd.den + frame.parents.odd.num) + 2 + (frame.child.den - 1) →
      (minusSites frame (frame.parents.odd.den + frame.parents.odd.num))[k]? = some e → e ∉ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro e hk1 hk2 he
    set r := frame.parents.odd.den + frame.parents.odd.num with hr
    have hIHk : ∀ (j : ℕ) (e' : Site), j < k → (minusSites frame r)[j]? = some e' → e' ∉ S := by
      intro j e' hj hje
      by_cases hjr : j < r.toNat + 2
      · exact hEarly j e' hjr hje
      · exact ih j hj e' (by omega) (by omega) hje
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = r.toNat + 2 + t := ⟨k - (r.toNat + 2), by omega⟩
    have hrow := minusSites_H frame r (-1 - (t : ℤ)) (by omega) (by omega)
    have hidx : r.toNat + 2 + (-1 - (-1 - (t : ℤ))).toNat = r.toNat + 2 + t := by omega
    rw [hidx] at hrow
    rw [hrow] at he
    have he' : e = RowAt.hAt frame (-1 - (t : ℤ)) := (Option.some.inj he).symm
    rw [he']
    by_cases h0 : t = 0
    · subst h0
      have hv0 : RowAt.vAt frame 0 = FLatticePaper.Induction.vFirst := by
        have h := RowAt.vAt_nat frame 0 (by omega)
        simp only [Nat.cast_zero] at h
        rw [h, VChain.vpath_zero]
      have hVr : (minusSites frame r)[r.toNat + 1]? = some FLatticePaper.Induction.vFirst := by
        unfold minusSites rowSites
        rw [List.getElem?_map, minusRow_get_V0]
        simp only [Option.map_some, labelSite]
        rw [hv0]
      have hA : (-1 : ℤ) - ((0 : ℕ) : ℤ) = -1 := by norm_num
      rw [hA]
      exact RefuteTree.refuted_not_mem frame F (Or.inr rfl) hS hK
        (E := fun x => ∃ j : ℕ, j < r.toNat + 2 + 0 ∧ (minusSites frame r)[j]? = some x)
        (fun x hx => by
          obtain ⟨j, hj, hjx⟩ := hx
          exact hIHk j x (by omega) hjx)
        (fun x hx => hx.elim) _
        (refuted_hAt_neg_one frame F hP (E := fun x => ∃ j : ℕ, j < r.toNat + 2 + 0 ∧ (minusSites frame r)[j]? = some x)
          (C := fun _ => False) ⟨r.toNat + 1, by omega, hVr⟩)
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = frame.child.den - 1 - (t : ℤ) :=
        ⟨(frame.child.den - 1 - (t : ℤ)).toNat, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hm2 : (m : ℤ) + 1 < frame.child.den := by omega
      have hentry : entryPos frame r m = r.toNat + 2 + t := by
        unfold entryPos
        omega
      have hIH' : ∀ x ∈ earlierAt frame r (entryPos frame r m), x ∉ S := by
        rw [hentry]
        intro x hx
        obtain ⟨j, hj, hjx⟩ := hx
        exact hIHk j x (by omega) hjx
      have hres := H_entry_not_mem frame F hP hsig hZ2 hZ3 hn1 hnd hNo hr0 hcap hS hK hm1 hm2 hIH'
      rw [show (m : ℤ) - frame.child.den = -1 - (t : ℤ) by omega] at hres
      exact hres

end FLatticePaper.MinusRowH
