import FLatticePaper.Plane.Induction.RowPair
import FLatticePaper.Plane.Induction.WordVPattern
import FLatticePaper.Plane.Induction.WordBoundary
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.PriceDeck
import FLatticePaper.Plane.Induction.FreeVOrdinate
import FLatticePaper.Plane.Induction.HChain
import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.EndpointDeck

/-! # The minus row at the game's word has the pair `(cutPrice, 0)` on every label (item (b) of task w3)

At `frameAt word` with the field `standardField word`:
* `P` drifts by `−1` along `U = (d, n)` (kernel) and is unchanged along `V` (transverse); `J` is unchanged along `U` and drifts by `−1`
  along `V` (`ChildFrame.price_kernel`, `price_transverse`, `slip_kernel`, `slip_transverse` from `StripsM.hper_word`);
* `P = cutPrice` on the free V cut (`PriceDeck.price_on_freeV`), `J(vpath k) = 0` for `k ≤ r`, `−1` after (`WordVPattern`);
* on the free H trace `P = cutPrice − 1` off `H₀` and `J = 0` (`TraceAt word`, `WordBoundary.roundedSlip_freeH_word`).

The inputs are the word's packet (`TieReduce.packet_of_strong`, conjugate SE), the trace of the word and of its conjugate. -/

namespace FLatticePaper.RowPairWord

open Farey FLatticePaper FLatticePaper.Induction

/-- Every H index `m < d` is a free H point (the top one by the successor of the one below). -/
theorem hpath_mem_all (frame : ChildFrame) (m : ℕ) (hm : (m : ℤ) < frame.child.den) :
    HChain.hpath frame m ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  by_cases h : (m : ℤ) + 1 < frame.child.den
  · exact (HChain.hpath_free frame m h).1
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
    rw [HChain.hpath_succ]
    have hkf := (HChain.hpath_free frame k (by omega)).1
    have hne : HChain.hpath frame k ≠ frame.hLast := by
      intro heq
      have h1 := RowPair.hpath_fst frame k
      have h2 : frame.hLast.1 = frame.child.den := rfl
      rw [heq, h2] at h1
      omega
    exact HChain.hsucc_mem frame hkf hne

/-- The price drift along `U`, in the form of `RowAt.Uvec`. -/
theorem price_U (frame : ChildFrame) (F : Field) {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.price F (z + RowAt.Uvec frame) = frame.price F z + (-1) := by
  have e : RowAt.Uvec frame = frame.child.modifiedDeck.kernel := (frame.child_modifiedDeck_kernel).symm
  rw [e, frame.price_kernel F h z]
  ring

/-- The rounded slip is unchanged along `U`. -/
theorem roundedSlip_U (frame : ChildFrame) (F : Field) {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.roundedSlip F (-1) (z + RowAt.Uvec frame) = frame.roundedSlip F (-1) z := by
  have e : RowAt.Uvec frame = frame.child.modifiedDeck.kernel := (frame.child_modifiedDeck_kernel).symm
  rw [e]
  unfold ChildFrame.roundedSlip
  rw [frame.slip_kernel F h (-1) z]

/-- The rounded slip drifts by `−1` along `V` (the period `η = −1`). -/
theorem roundedSlip_V (frame : ChildFrame) (F : Field) {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.roundedSlip F (-1) (z + RowAt.Vvec frame) = frame.roundedSlip F (-1) z + (-1) := by
  have e : RowAt.Vvec frame = frame.child.modifiedDeck.transverse := (EndpointDeck.transverse_eq_Vdeck frame).symm
  rw [e]
  unfold ChildFrame.roundedSlip
  rw [frame.slip_transverse F h (-1) z]
  omega

theorem price_V (frame : ChildFrame) (F : Field) {cU cV : ℤ} (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.price F (z + RowAt.Vvec frame) = frame.price F z := by
  have e : RowAt.Vvec frame = frame.child.modifiedDeck.transverse := (EndpointDeck.transverse_eq_Vdeck frame).symm
  rw [e, frame.price_transverse F h z]

/-- **The minus row at the word: every label has the pair `(cutPrice, 0)`.** `r = brk word`, `L = den + num`, `d = den`. -/
theorem minusRow_pairs_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hTrW : TraceFromPsi.TraceAt word)
    (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (ℓ : FreeRows.FreeLabel)
    (hℓ : ℓ ∈ FreeRows.minusRow (WordVPattern.brk word)
      ((frameAt word).child.den + (frameAt word).child.num) (frameAt word).child.den) :
    (frameAt word).price (standardField word)
        (FreeRows.labelSite (RowAt.vAt (frameAt word)) (RowAt.hAt (frameAt word)) ℓ) = (frameAt word).cutPrice ∧
    (frameAt word).roundedSlip (standardField word) (-1)
        (FreeRows.labelSite (RowAt.vAt (frameAt word)) (RowAt.hAt (frameAt word)) ℓ) = 0 := by
  have hP : (frameAt word).Packet (standardField word) := packet_of_strong hw hSE
  have hS := hP.strips
  have hper := StripsM.hper_word hw hSE
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  have hbr := WordVPattern.brk_add_two_le word
  have hr0 : (0 : ℤ) ≤ WordVPattern.brk word := le_of_lt (WordVPattern.brk_pos word)
  -- the price on the free V cut
  have hPc : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).price (standardField word) (VChain.vpath (frameAt word) k) = (frameAt word).cutPrice := by
    intro k hk
    have hz : VChain.vpath (frameAt word) k ∈ (frameAt word).freeV := by
      by_cases hk1 : (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num - 1
      · exact VChain.vpath_free (frameAt word) k hk1
      · have e : VChain.vpath (frameAt word) k = (frameAt word).vLast := by
          rw [VChain.vLast_eq_vpath]
          congr 1
          omega
        rw [e]
        exact FreeVOrdinate.vLast_mem_freeV (frameAt word)
    exact PriceDeck.price_on_freeV (frameAt word) (standardField word) hS hz
  -- the V pattern (minus)
  have hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ WordVPattern.brk word then 0 else -1 :=
    fun k hk => WordVPattern.roundedSlip_minus_vpath hw hSE hTrC k hk
  -- the free H trace
  have hFmem : FLatticePaper.Induction.hFirst ∈ (frameAt word).freeH := by
    have h0 := hpath_mem_all (frameAt word) 0 (by omega)
    rwa [HChain.hpath_zero] at h0
  have hPF : (frameAt word).price (standardField word) FLatticePaper.Induction.hFirst = (frameAt word).cutPrice := by
    have hc : FLatticePaper.Induction.hFirst = ((1 : ℤ), (0 : ℤ)) := rfl
    rw [hTrW _ hFmem, if_pos hc, sub_zero]
  have hPH : ∀ m : ℕ, (m : ℤ) < (frameAt word).child.den → m ≠ 0 →
      (frameAt word).price (standardField word) (HChain.hpath (frameAt word) m) = (frameAt word).cutPrice - 1 := by
    intro m hm hm0
    have hne : HChain.hpath (frameAt word) m ≠ ((1 : ℤ), (0 : ℤ)) := by
      intro heq
      have h1 := RowPair.hpath_fst (frameAt word) m
      rw [heq] at h1
      norm_num at h1
      omega
    rw [hTrW _ (hpath_mem_all (frameAt word) m hm), if_neg hne]
  have hJH : ∀ m : ℕ, (m : ℤ) < (frameAt word).child.den →
      (frameAt word).roundedSlip (standardField word) (-1) (HChain.hpath (frameAt word) m) = 0 :=
    fun m hm => WordBoundary.roundedSlip_freeH_word hw hSE (Or.inr rfl) (hpath_mem_all (frameAt word) m hm)
  -- the drifts
  have hPU := price_U (frameAt word) (standardField word) hper
  have hJU := roundedSlip_U (frameAt word) (standardField word) hper
  have hPV := price_V (frameAt word) (standardField word) hper
  have hJV := roundedSlip_V (frameAt word) (standardField word) hper
  have hrL : WordVPattern.brk word ≤ (frameAt word).child.den + (frameAt word).child.num - 2 := by omega
  -- the label cases
  simp only [FreeRows.minusRow, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with (((⟨i, hi, rfl⟩ | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · -- `V (r − i)` with `1 ≤ r − i ≤ r`
    exact RowPair.V_label_pair (frameAt word) ((frameAt word).roundedSlip (standardField word) (-1))
      ((frameAt word).price (standardField word)) (WordVPattern.brk word) (frameAt word).cutPrice
      hJV hPV hr0 hrL hpat hPc _ (by omega) (by omega)
  · -- `H 0`
    exact RowPair.H_label_pair (frameAt word) ((frameAt word).price (standardField word))
      ((frameAt word).roundedSlip (standardField word) (-1)) (frameAt word).cutPrice hPU hJU hPH hPF hJH 0 (by omega) (by omega)
  · -- `V 0`
    exact RowPair.V_label_pair (frameAt word) ((frameAt word).roundedSlip (standardField word) (-1))
      ((frameAt word).price (standardField word)) (WordVPattern.brk word) (frameAt word).cutPrice
      hJV hPV hr0 hrL hpat hPc 0 (by omega) (by omega)
  · -- `H (−1 − i)` with `i < d − 1`
    exact RowPair.H_label_pair (frameAt word) ((frameAt word).price (standardField word))
      ((frameAt word).roundedSlip (standardField word) (-1)) (frameAt word).cutPrice hPU hJU hPH hPF hJH _ (by omega) (by omega)
  · -- `V (−1 − i)` with `i < L − r − 1`
    exact RowPair.V_label_pair (frameAt word) ((frameAt word).roundedSlip (standardField word) (-1))
      ((frameAt word).price (standardField word)) (WordVPattern.brk word) (frameAt word).cutPrice
      hJV hPV hr0 hrL hpat hPc _ (by omega) (by omega)

end FLatticePaper.RowPairWord
