import FLatticePaper.Plane.Induction.RowPairWord
import FLatticePaper.Plane.Induction.PairTranslate

/-! # The pair `(cutPrice, 0)` on the plus row, and the lift uniqueness for the sign `+1`

For `eta = +1` the rounded slip `J = roundedSlip F 1` drifts by `+1` along the transverse `V` (`slip` drifts by `2η = 2`), so the
V label lemma and the lift lemma are stated for a general drift sign `s` (`s = -1` is the minus case, `s = +1` the plus case). -/

namespace FLatticePaper.PlusRowPair

open Farey FLatticePaper FLatticePaper.Induction

/-- **The V labels have the pair `(c₀, 0)` for a drift sign `s`.** The label `vAt j`, `R + 1 − L ≤ j ≤ R`, has `P = c₀` and `J = 0`
when `J` drifts by `s` along `V` and `J(vpath k) = 0` for `k ≤ R`, `= s` for `k > R`. -/
theorem V_label_pair_gen (frame : ChildFrame) (s : ℤ) (J P : Site → ℤ) (r c0 : ℤ)
    (hJV : ∀ z, J (z + RowAt.Vvec frame) = J z + s)
    (hPV : ∀ z, P (z + RowAt.Vvec frame) = P z)
    (hr0 : 0 ≤ r) (hrL : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      J (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else s)
    (hPc : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → P (VChain.vpath frame k) = c0)
    (j : ℤ) (hj1 : r + 1 - (frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ r) :
    P (RowAt.vAt frame j) = c0 ∧ J (RowAt.vAt frame j) = 0 := by
  have hL : (0 : ℤ) < frame.child.den + frame.child.num := RowAt.len_pos frame
  by_cases hj0 : 0 ≤ j
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, by omega⟩
    have hkL : (k : ℤ) < frame.child.den + frame.child.num := by omega
    rw [← hk, RowAt.vAt_nat frame k hkL]
    refine ⟨hPc k hkL, ?_⟩
    rw [hpat k hkL, if_pos (show (k : ℤ) ≤ r by omega)]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j + (frame.child.den + frame.child.num) :=
      ⟨(j + (frame.child.den + frame.child.num)).toNat, by omega⟩
    have hkL : (k : ℤ) < frame.child.den + frame.child.num := by omega
    have e := RowAt.vAt_add_len frame j
    rw [← hk, RowAt.vAt_nat frame k hkL] at e
    have hP1 : P (RowAt.vAt frame j) = P (VChain.vpath frame k) := by
      rw [e, hPV]
    have hJ1 : J (VChain.vpath frame k) = J (RowAt.vAt frame j) + s := by
      rw [e, hJV]
    refine ⟨hP1.trans (hPc k hkL), ?_⟩
    rw [hpat k hkL, if_neg (show ¬ ((k : ℤ) ≤ r) by omega)] at hJ1
    linarith

/-- **Lift uniqueness for a drift sign `s = ±1` along `V`.** -/
theorem lift_pair_unique_gen (frame : ChildFrame) (s : ℤ) (hs : s = 1 ∨ s = -1) (P J : Site → ℤ) (c0 : ℤ)
    (hPU : ∀ z, P (z + RowAt.Uvec frame) = P z + (-1))
    (hJU : ∀ z, J (z + RowAt.Uvec frame) = J z)
    (hPV : ∀ z, P (z + RowAt.Vvec frame) = P z)
    (hJV : ∀ z, J (z + RowAt.Vvec frame) = J z + s)
    (x : Site) (hx : P x = c0 ∧ J x = 0) (m n : ℤ)
    (hg : P (x + m • RowAt.Uvec frame + n • RowAt.Vvec frame) = c0 ∧
      J (x + m • RowAt.Uvec frame + n • RowAt.Vvec frame) = 0) :
    m = 0 ∧ n = 0 := by
  have h1 := PairTranslate.drift_zsmul P (RowAt.Uvec frame) (-1) hPU m x
  have hPV0 : ∀ z, P (z + RowAt.Vvec frame) = P z + 0 := fun z => by rw [hPV z, add_zero]
  have hJU0 : ∀ z, J (z + RowAt.Uvec frame) = J z + 0 := fun z => by rw [hJU z, add_zero]
  have h2 := PairTranslate.drift_zsmul P (RowAt.Vvec frame) 0 hPV0 n (x + m • RowAt.Uvec frame)
  have h3 := PairTranslate.drift_zsmul J (RowAt.Uvec frame) 0 hJU0 m x
  have h4 := PairTranslate.drift_zsmul J (RowAt.Vvec frame) s hJV n (x + m • RowAt.Uvec frame)
  have hP := hg.1
  have hJ := hg.2
  rw [h2, h1, hx.1] at hP
  rw [h4, h3, hx.2] at hJ
  constructor
  · linarith
  · rcases hs with rfl | rfl <;> linarith

/-- The rounded slip of the sign `+1` is unchanged along `U`. -/
theorem roundedSlip_U_plus (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.roundedSlip F 1 (z + RowAt.Uvec frame) = frame.roundedSlip F 1 z := by
  have e : RowAt.Uvec frame = frame.child.modifiedDeck.kernel := (frame.child_modifiedDeck_kernel).symm
  rw [e]
  unfold ChildFrame.roundedSlip
  rw [frame.slip_kernel F h 1 z]

/-- The rounded slip of the sign `+1` drifts by `+1` along `V` (the slip drifts by `2`). -/
theorem roundedSlip_V_plus (frame : ChildFrame) (F : Field) {cU cV : ℤ}
    (h : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    frame.roundedSlip F 1 (z + RowAt.Vvec frame) = frame.roundedSlip F 1 z + 1 := by
  have e : RowAt.Vvec frame = frame.child.modifiedDeck.transverse := (EndpointDeck.transverse_eq_Vdeck frame).symm
  rw [e]
  unfold ChildFrame.roundedSlip
  rw [frame.slip_transverse F h 1 z]
  omega

/-- **The plus row labels have the pair `(cutPrice, 0)`** (with `J = roundedSlip F 1`), at the word. -/
theorem plusRow_pairs_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hTrW : TraceFromPsi.TraceAt word)
    (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (ℓ : FreeRows.FreeLabel)
    (hℓ : ℓ ∈ FreeRows.plusRow (WordVPattern.brk word)
      ((frameAt word).child.den + (frameAt word).child.num) (frameAt word).child.den) :
    (frameAt word).price (standardField word)
        (FreeRows.labelSite (RowAt.vAt (frameAt word)) (RowAt.hAt (frameAt word)) ℓ) = (frameAt word).cutPrice ∧
    (frameAt word).roundedSlip (standardField word) 1
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
  -- the V pattern (plus)
  have hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) 1 (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2 then 0 else 1 :=
    fun k hk => WordVPattern.roundedSlip_plus_vpath hw hSE hTrC k hk
  -- the free H trace
  have hFmem : FLatticePaper.Induction.hFirst ∈ (frameAt word).freeH := by
    have h0 := RowPairWord.hpath_mem_all (frameAt word) 0 (by omega)
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
    rw [hTrW _ (RowPairWord.hpath_mem_all (frameAt word) m hm), if_neg hne]
  have hJH : ∀ m : ℕ, (m : ℤ) < (frameAt word).child.den →
      (frameAt word).roundedSlip (standardField word) 1 (HChain.hpath (frameAt word) m) = 0 :=
    fun m hm => WordBoundary.roundedSlip_freeH_word hw hSE (Or.inl rfl) (RowPairWord.hpath_mem_all (frameAt word) m hm)
  have hPU := RowPairWord.price_U (frameAt word) (standardField word) hper
  have hJU := PlusRowPair.roundedSlip_U_plus (frameAt word) (standardField word) hper
  have hPV := RowPairWord.price_V (frameAt word) (standardField word) hper
  have hJV := PlusRowPair.roundedSlip_V_plus (frameAt word) (standardField word) hper
  have hR0 : (0 : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2 := by
    omega
  have hRL : (frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2 ≤
      (frameAt word).child.den + (frameAt word).child.num - 2 := by
    have := WordVPattern.brk_pos word
    omega
  simp only [FreeRows.plusRow, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with (((⟨i, hi, rfl⟩ | rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · -- `V (-r - 1 + i)`, the negative block
    exact PlusRowPair.V_label_pair_gen (frameAt word) 1
      ((frameAt word).roundedSlip (standardField word) 1) ((frameAt word).price (standardField word))
      ((frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2) (frameAt word).cutPrice
      hJV hPV hR0 hRL hpat hPc _ (by omega) (by omega)
  · -- `H 0`
    exact RowPair.H_label_pair (frameAt word) ((frameAt word).price (standardField word))
      ((frameAt word).roundedSlip (standardField word) 1) (frameAt word).cutPrice hPU hJU hPH hPF hJH 0
      (by omega) (by omega)
  · -- `V 0`
    exact PlusRowPair.V_label_pair_gen (frameAt word) 1
      ((frameAt word).roundedSlip (standardField word) 1) ((frameAt word).price (standardField word))
      ((frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2) (frameAt word).cutPrice
      hJV hPV hR0 hRL hpat hPc 0 (by omega) (by omega)
  · -- `V (1 + i)`, the positive block
    exact PlusRowPair.V_label_pair_gen (frameAt word) 1
      ((frameAt word).roundedSlip (standardField word) 1) ((frameAt word).price (standardField word))
      ((frameAt word).child.den + (frameAt word).child.num - WordVPattern.brk word - 2) (frameAt word).cutPrice
      hJV hPV hR0 hRL hpat hPc _ (by omega) (by omega)
  · -- `H (-1 - i)`
    exact RowPair.H_label_pair (frameAt word) ((frameAt word).price (standardField word))
      ((frameAt word).roundedSlip (standardField word) 1) (frameAt word).cutPrice hPU hJU hPH hPF hJH _
      (by omega) (by omega)

end FLatticePaper.PlusRowPair
