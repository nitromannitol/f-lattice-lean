import FLatticePaper.Plane.Induction.HardHChainEta
import FLatticePaper.Plane.Induction.HardRank4
import FLatticePaper.Plane.Induction.MinusRowH
import FLatticePaper.Plane.Induction.PlusRowH
import FLatticePaper.Plane.Induction.PlusRowPrefix

/-! # The H block of the minus and plus rows in the hard frames (d < 2n), without `2n ≤ d`

For an H entry `hAt(−1−t)` with `t + 2 ≤ d`, the refutation in a hard frame uses only the η-chains:
rank 1 (even, free east), rank 2 (even, diagonal, `HardHChainEta`), rank 3 (odd, white `q`, `HardHChainEta`). The black branch
`lap(z+(1,1)) = −1` is impossible (`HardRank4.no_black_NE`), so the rank-4 input `hEH`/`hEV`/`hVidx` is not needed.

* `H_block_refuted_hard`: the Refuted form (earlier positions `E`, core `False`), with no induction hypothesis. This is the `href`
  for `RefuteTree`-row removal (`row_removed_pos`) at the H positions.
* `H_block_removed_hard`: the not-in-S form, with the prefix `hEarlyHard` (the V prefix and `H_0`, `V_0`) explicit.
* `minus_href_hard`, `plus_href_hard`, `minus_H_block_removed_hard`, `plus_H_block_removed_hard`: the instances for the minus
  row (`η = −1`, `minusSites`) and the plus row (`η = 1`, `PlusRowWiring.plusSites`). -/

namespace FLatticePaper.HardRowH

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RefuteTree FLatticePaper.FreeRows
open FLatticePaper.EasyHRank FLatticePaper.EasyHRankDiag FLatticePaper.MinusRowWiring FLatticePaper.MinusRowRemoval
open FLatticePaper.MinusRowEndpoint FLatticePaper.OddAxialRank FLatticePaper.HChainEta FLatticePaper.MinusRowH

/-- **An H entry of a hard frame, in Refuted form.** For `1 ≤ m`, `m + 1 < d`, the entry `hAt(m−d)` is refuted from any `E` that
contains its east neighbour `hAt(m+1−d)`, with core `False`. -/
theorem H_entry_refuted_hard (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : (m : ℤ) + 1 < frame.child.den)
    {E : Site → Prop} (hE_next : E (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den))) :
    Refuted frame F η E (fun _ => False) (RowAt.hAt frame ((m : ℤ) - frame.child.den)) := by
  obtain ⟨hn0, -, -, -, -⟩ := frame.child_facts
  have hd3 : frame.child.den ≤ 3 * frame.child.num := by omega
  have hzfree : HChain.hpath frame m ∈ frame.freeH := RowPairWord.hpath_mem_all frame m (by omega)
  have hz1 : (HChain.hpath frame m).1 = (m : ℤ) + 1 := RowPair.hpath_fst frame m
  have hzd : (HChain.hpath frame m).1 < frame.child.den := by omega
  have hx2 : 2 ≤ (HChain.hpath frame m).1 := by omega
  have hper := hP.periods
  by_cases hev : EvenSite (HChain.hpath frame m)
  · by_cases hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH
    · exact refuted_even_H_east_free_eta frame F η hP hper hm1 hm2 hev hfree hE_next
    · exact HardHChainEta.refuted_even_H_diag_eta_hard frame F η hP hper hZ2 hm1 hm2 hev hfree hE_next
  · have hfree : ((HChain.hpath frame m).1 + 1, (HChain.hpath frame m).2) ∈ frame.freeH :=
      EasyHRankDiag.east_freeH_of_odd frame hzfree hev (by omega) hzd
    rcases hP.binary (HChain.hpath frame m + ((1 : ℤ), (1 : ℤ))) with hb | hw
    · exact absurd hb (HardRank4.no_black_NE frame F hZ3 hd3 hzfree hev hx2 hzd)
    · exact HardHChainEta.refuted_odd_H_white_q_eta_hard frame F η hP hper hm1 hm2 hev hw hE_next

/-- **The hard H block in Refuted form, for an arbitrary row.** Given that the row carries `hAt(−1−t)` at position `P0 + t`
(`t + 2 ≤ d`) and `vFirst` at some position before `P0`, the H entry at `P0 + t` is refuted from the positions before it,
with core `False`. This is the `href` of `row_removed_pos` at the H positions. -/
theorem H_block_refuted_hard (frame : ChildFrame) (F : Field) (η : ℤ) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num)
    (row : List Site) (P0 : ℕ)
    (hrow : ∀ t : ℕ, t + 2 ≤ frame.child.den → row[P0 + t]? = some (RowAt.hAt frame (-1 - (t : ℤ))))
    (hV0 : ∃ j : ℕ, j < P0 ∧ row[j]? = some FLatticePaper.Induction.vFirst)
    (t : ℕ) (ht : t + 2 ≤ frame.child.den) :
    Refuted frame F η (fun x => ∃ j : ℕ, j < P0 + t ∧ row[j]? = some x) (fun _ => False)
      (RowAt.hAt frame (-1 - (t : ℤ))) := by
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    obtain ⟨j, hj, hjv⟩ := hV0
    have hA : (-1 : ℤ) - ((0 : ℕ) : ℤ) = -1 := by norm_num
    rw [hA]
    exact refuted_hAt_neg_one_eta frame F η hP (E := fun x => ∃ i : ℕ, i < P0 + 0 ∧ row[i]? = some x)
      (C := fun _ => False) ⟨j, by omega, hjv⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = frame.child.den - 1 - ((s + 1 : ℕ) : ℤ) :=
      ⟨(frame.child.den - 1 - ((s + 1 : ℕ) : ℤ)).toNat, by omega⟩
    have hm1 : 1 ≤ m := by push_cast at hm; omega
    have hm2 : (m : ℤ) + 1 < frame.child.den := by push_cast at hm; omega
    have hsame : (m : ℤ) + 1 - frame.child.den = -1 - (s : ℤ) := by push_cast at hm; omega
    have hEnext : ∃ j : ℕ, j < P0 + (s + 1) ∧ row[j]? = some (RowAt.hAt frame ((m : ℤ) + 1 - frame.child.den)) := by
      refine ⟨P0 + s, by omega, ?_⟩
      rw [hsame]
      exact hrow s (by omega)
    have hres := H_entry_refuted_hard frame F η hP hZ2 hZ3 hhard hm1 hm2
      (E := fun x => ∃ j : ℕ, j < P0 + (s + 1) ∧ row[j]? = some x) hEnext
    rw [show (m : ℤ) - frame.child.den = -1 - ((s + 1 : ℕ) : ℤ) by push_cast at hm ⊢; omega] at hres
    exact hres

/-- **The hard H block, not-in-S form.** Given the prefix `hEarlyHard` (every position before `P0`, namely the V prefix and
`H_0`, `V_0`, is outside `S`), every H position `P0 + t`, `t + 2 ≤ d`, is outside `S`. -/
theorem H_block_removed_hard (frame : ChildFrame) (F : Field) (η : ℤ) (hη : η = 1 ∨ η = -1) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num)
    (row : List Site) (P0 : ℕ)
    (hrow : ∀ t : ℕ, t + 2 ≤ frame.child.den → row[P0 + t]? = some (RowAt.hAt frame (-1 - (t : ℤ))))
    (hV0 : ∃ j : ℕ, j < P0 ∧ row[j]? = some FLatticePaper.Induction.vFirst)
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F η) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F η z)
    (hEarlyHard : ∀ (j : ℕ) (e' : Site), j < P0 → row[j]? = some e' → e' ∉ S) :
    ∀ t : ℕ, t + 2 ≤ frame.child.den → ∀ e : Site, row[P0 + t]? = some e → e ∉ S := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht e he
  have hE : ∀ x, (∃ j : ℕ, j < P0 + t ∧ row[j]? = some x) → x ∉ S := by
    rintro x ⟨j, hj, hjx⟩
    by_cases hjP : j < P0
    · exact hEarlyHard j x hjP hjx
    · obtain ⟨t', rfl⟩ : ∃ t', j = P0 + t' := ⟨j - P0, by omega⟩
      have hrow' := hrow t' (by omega)
      rw [hrow'] at hjx
      have hx : x = RowAt.hAt frame (-1 - (t' : ℤ)) := (Option.some.inj hjx).symm
      rw [hx]
      exact ih t' (by omega) (by omega) _ hrow'
  have href := H_block_refuted_hard frame F η hP hZ2 hZ3 hhard row P0 hrow hV0 t ht
  have he' : e = RowAt.hAt frame (-1 - (t : ℤ)) := by
    rw [hrow t ht] at he
    exact (Option.some.inj he).symm
  rw [he']
  exact RefuteTree.refuted_not_mem frame F hη hS hK hE (fun x hx => hx.elim) _ href

/-- The minus-row V_0 entry: `minusSites` has `vFirst` at position `r.toNat + 1`. -/
theorem minus_hV0 (frame : ChildFrame) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num) :
    ∃ j : ℕ, j < r.toNat + 2 ∧ (minusSites frame r)[j]? = some FLatticePaper.Induction.vFirst := by
  have hv0 : RowAt.vAt frame 0 = FLatticePaper.Induction.vFirst := by
    have h := RowAt.vAt_nat frame 0 (by omega)
    simp only [Nat.cast_zero] at h
    rw [h, VChain.vpath_zero]
  have hVr : (minusSites frame r)[r.toNat + 1]? = some FLatticePaper.Induction.vFirst := by
    unfold minusSites rowSites
    rw [List.getElem?_map, minusRow_get_V0]
    simp only [Option.map_some, labelSite]
    rw [hv0]
  exact ⟨r.toNat + 1, by omega, hVr⟩

/-- The minus-row H positions: `minusSites` has `hAt(−1−t)` at position `r.toNat + 2 + t`. -/
theorem minus_hrow (frame : ChildFrame) (r : ℤ) (t : ℕ) (ht : t + 2 ≤ frame.child.den) :
    (minusSites frame r)[r.toNat + 2 + t]? = some (RowAt.hAt frame (-1 - (t : ℤ))) := by
  have h := MinusRowH.minusSites_H frame r (-1 - (t : ℤ)) (by omega) (by omega)
  have hidx : r.toNat + 2 + (-1 - (-1 - (t : ℤ))).toNat = r.toNat + 2 + t := by omega
  rw [hidx] at h
  exact h

/-- **The minus row H block, Refuted form** (`η = −1`, positions `r.toNat + 2 + t`), as the `href` of `row_removed_pos`. -/
theorem minus_href_hard (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    (t : ℕ) (ht : t + 2 ≤ frame.child.den) :
    Refuted frame F (-1) (fun x => ∃ j : ℕ, j < r.toNat + 2 + t ∧ (minusSites frame r)[j]? = some x) (fun _ => False)
      (RowAt.hAt frame (-1 - (t : ℤ))) :=
  H_block_refuted_hard frame F (-1) hP hZ2 hZ3 hhard (minusSites frame r) (r.toNat + 2) (minus_hrow frame r)
    (minus_hV0 frame r hL) t ht

/-- **The minus row H block, not-in-S form** (`η = −1`), with the prefix `hEarlyHard` explicit. -/
theorem minus_H_block_removed_hard (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z)
    (hEarlyHard : ∀ (j : ℕ) (e' : Site), j < r.toNat + 2 → (minusSites frame r)[j]? = some e' → e' ∉ S) :
    ∀ t : ℕ, t + 2 ≤ frame.child.den → ∀ e : Site, (minusSites frame r)[r.toNat + 2 + t]? = some e → e ∉ S :=
  H_block_removed_hard frame F (-1) (Or.inr rfl) hP hZ2 hZ3 hhard (minusSites frame r) (r.toNat + 2)
    (minus_hrow frame r) (minus_hV0 frame r hL) hS hK hEarlyHard

/-- The plus-row H positions: `PlusRowWiring.plusSites` has `hAt(−1−t)` at `P0 + t`, `P0 = (r+1).toNat + 2 + (d+n−r−2).toNat`. -/
theorem plus_hrow (frame : ChildFrame) (r : ℤ) (t : ℕ) (ht : t + 2 ≤ frame.child.den) :
    (PlusRowWiring.plusSites frame r)[(r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + t]? =
      some (RowAt.hAt frame (-1 - (t : ℤ))) := by
  have h := PlusRowWiring.plusRow_get_H r (frame.child.den + frame.child.num) frame.child.den (-1 - (t : ℤ))
    (by omega) (by omega)
  have hidx : (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat
      + (-1 - (-1 - (t : ℤ))).toNat
      = (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + t := by omega
  rw [hidx] at h
  unfold PlusRowWiring.plusSites rowSites
  rw [List.getElem?_map, h]
  simp [labelSite]

/-- The plus-row V_0 entry at position `(r+1).toNat + 1` (value `(0,0) = vFirst`). -/
theorem plus_hV0 (frame : ChildFrame) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num) :
    ∃ j : ℕ, j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat ∧
      (PlusRowWiring.plusSites frame r)[j]? = some FLatticePaper.Induction.vFirst :=
  ⟨(r + 1).toNat + 1, by omega, PlusRowPrefix.plusSites_V0 frame r hL⟩

/-- **The plus row H block, Refuted form** (`η = 1`), as the `href` of `row_removed_pos`. -/
theorem plus_href_hard (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    (t : ℕ) (ht : t + 2 ≤ frame.child.den) :
    Refuted frame F 1 (fun x => ∃ j : ℕ,
        j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + t ∧ (PlusRowWiring.plusSites frame r)[j]? = some x)
      (fun _ => False) (RowAt.hAt frame (-1 - (t : ℤ))) :=
  H_block_refuted_hard frame F 1 hP hZ2 hZ3 hhard (PlusRowWiring.plusSites frame r)
    ((r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat) (plus_hrow frame r)
    (plus_hV0 frame r hL) t ht

/-- **The plus row H block, not-in-S form** (`η = 1`), with the prefix `hEarlyHard` explicit. -/
theorem plus_H_block_removed_hard (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hZ2 : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hZ3 : ∀ w : Site, EvenSite w → 2 - (frame.child.den + frame.child.num) ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → F w = 0)
    (hhard : frame.child.den < 2 * frame.child.num) (r : ℤ) (hL : 0 < frame.child.den + frame.child.num)
    {S : Set Site} (hS : IsRestrictedFort F (permitsQ1 frame F 1) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F 1 z)
    (hEarlyHard : ∀ (j : ℕ) (e' : Site),
      j < (r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat →
      (PlusRowWiring.plusSites frame r)[j]? = some e' → e' ∉ S) :
    ∀ t : ℕ, t + 2 ≤ frame.child.den → ∀ e : Site,
      (PlusRowWiring.plusSites frame r)[(r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat + t]? = some e → e ∉ S :=
  H_block_removed_hard frame F 1 (Or.inl rfl) hP hZ2 hZ3 hhard (PlusRowWiring.plusSites frame r)
    ((r + 1).toNat + 2 + (frame.child.den + frame.child.num - r - 2).toNat) (plus_hrow frame r)
    (plus_hV0 frame r hL) hS hK hEarlyHard

end FLatticePaper.HardRowH
