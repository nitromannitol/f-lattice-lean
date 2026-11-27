import FLatticePaper.Plane.Induction.WordMinusEasy
import FLatticePaper.Plane.Induction.RowVTailRow
import FLatticePaper.Plane.Induction.WordPlusEasy

/-! # The whole minus row of an easy word is outside the restricted fort (eta = -1)

The minus row is the prefix `V_r..V_1, H_0, V_0`, the H block, and the V tail `V_{-1}..V_{r+1-L}`. The prefix and the H block are
`WordMinusEasy.minus_row_up_to_H_word`; the tail is taken by strong induction from `RowVTailRow.tail_href_row`. -/

namespace FLatticePaper.WordMinusRow

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
  FLatticePaper.WordMinusEasy FLatticePaper.WordWebHyp FLatticePaper.WordVPattern FLatticePaper.WordDischarge
  FLatticePaper.W1Seeds FLatticePaper.RowVTailRow

/-- **The minus V tail is outside the restricted fort** (strong induction over the positions, from the earlier positions and
`tail_href_row`). -/
theorem minus_tail_removed (frame : ChildFrame) (F : Field) (hP : frame.Packet F)
    (hS : ∀ z : Site, 2 - 2 * frame.child.den ≤ frame.sGrade z →
      frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 2 → F z = harmonicGrid z)
    (hO : ∀ z : Site, ¬ EvenSite z → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade z →
      frame.sGrade z ≤ 3 * frame.child.den + frame.child.num - 2 → F z = harmonicGrid z)
    (hd2 : 2 * frame.child.num ≤ frame.child.den) (hd : 2 ≤ frame.child.den) {r : ℤ} (hr0 : 0 ≤ r)
    {S : Set Site} (hres : IsRestrictedFort F (permitsQ1 frame F (-1)) S)
    (hK : ∀ z ∈ S, frame.cutPrice ≤ frame.price F z + frame.roundedSlip F (-1) z)
    (hPre : ∀ (j : ℕ) (e : Site), j < r.toNat + 2 + (frame.child.den - 1).toNat →
      (tailRow frame r)[j]? = some e → e ∉ S) :
    ∀ (j : ℕ) (e : Site), r.toNat + 2 + (frame.child.den - 1).toNat ≤ j →
      j < r.toNat + 2 + (frame.child.den - 1).toNat + (frame.child.den + frame.child.num - r - 1).toNat →
      (tailRow frame r)[j]? = some e → e ∉ S := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro e hlo hhi he
    have hE : ∀ x, (∃ k' : ℕ, k' < j ∧ (tailRow frame r)[k']? = some x) → x ∉ S := by
      rintro x ⟨k', hk', hkx⟩
      by_cases hk3 : k' < r.toNat + 2 + (frame.child.den - 1).toNat
      · exact hPre k' x hk3 hkx
      · exact ih k' hk' x (by omega) (by omega) hkx
    have href := RowVTailRow.tail_href_row hP hS hO hd2 hr0 hd j e he hlo hhi
    exact RefuteTree.refuted_not_mem frame F (Or.inr rfl) hres hK
      (E := fun x => ∃ k' : ℕ, k' < j ∧ (tailRow frame r)[k']? = some x) (C := fun _ => False) hE
      (fun x hx => hx.elim) _ href

/-- **The whole minus row at an easy word.** -/
theorem minus_row_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site}
    (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) (-1)) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z) :
    ∀ (k : ℕ) (e : Site),
      k < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num).toNat + 2 +
        ((frameAt word).child.den - 1).toNat + ((frameAt word).child.den + (frameAt word).child.num -
          ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1).toNat →
      (MinusRowWiring.minusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))[k]? =
        some e → e ∉ S := by
  have hup := minus_row_up_to_H_word hw hS hpar hSE hTrW hTrC hnd hres hK
  have hd : 2 ≤ (frameAt word).child.den := by
    obtain ⟨hn0, hnd', -, hd3, -⟩ := (frameAt word).child_facts
    omega
  have hTail := minus_tail_removed (frameAt word) (standardField word) hS.packet
    (fun z h1 h2 => OppWordCover.word_strip hS z (by omega) (by omega)) (hO_word hS hpar) hnd hd
    (r := (frameAt word).parents.odd.den + (frameAt word).parents.odd.num)
    (by
      have := brk_pos word
      unfold brk at this
      omega)
    hres hK (fun j e hj he => hup j e hj he)
  intro k e hk he
  by_cases hkH : k < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num).toNat + 2 +
      ((frameAt word).child.den - 1).toNat
  · exact hup k e hkH he
  · exact hTail k e (by omega) hk he

end FLatticePaper.WordMinusRow
