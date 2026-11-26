import FLatticePaper.Plane.Induction.ClippedFreeV
import FLatticePaper.Plane.Induction.LiftPsi
import FLatticePaper.Plane.Induction.RowMinus
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.TraceFromPsi
import FLatticePaper.Plane.Induction.VChain
import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.FinalRootSlip
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.RawB
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.RoutePlus
import FLatticePaper.Plane.Induction.CutReflect
import FLatticePaper.Plane.Induction.Q3Field

/-! # The V pattern of the word's own rounded slip (`hpat` of `EasyNoFort`), both signs

With `r = D + N` the odd parent's sum (`brk word`) and `L = den + num` of the word's child frame:
* raw minus slip `D₋(vpath k) = slip (−1) (vpath k)`: `0` at `k = 0`, `−1` for `1 ≤ k ≤ r`, `−2` for `r < k < L`
  (`slip_minus_vpath_raw`), from the clipped identity and the lift at the word;
* rounded minus pattern: `J₋ = 0` for `k ≤ r`, `−1` for `r < k < L` (`roundedSlip_minus_vpath`);
* rounded plus pattern: `J₊ = 0` for `k ≤ L − r − 2`, `1` otherwise (`roundedSlip_plus_vpath`), by the field symmetry through
  `(1,−1)` (`Q3Field.packet_reflection_I`, `CutReflect.Dq_reflect`), the reversal `vLast − vpath k = vpath (L−1−k)` and the period rule:
  `D₊(vpath k) = D₋(vpath (L−1−k)) + 2`.

The inputs are the conjugate's strong estimates and trace, and the word's own packet (`packet_of_strong`). -/

namespace FLatticePaper.WordVPattern

open Farey FLatticePaper FLatticePaper.Induction

/-- The break `r = D + N` of the word: the odd parent's denominator plus numerator. -/
def brk (word : Word) : ℤ := (frameAt word).parents.odd.den + (frameAt word).parents.odd.num

/-- `r + 2 ≤ L` (so `r ≤ L − 2`), from the parent bounds and the child identities. -/
theorem brk_add_two_le (word : Word) :
    brk word + 2 ≤ (frameAt word).child.den + (frameAt word).child.num := by
  obtain ⟨hdo, hno, -, -⟩ := NativeGrade.odd_parent_facts (frameAt word)
  obtain ⟨hde, hne, -⟩ := (frameAt word).valid.even_bounds
  have hd := ZoneI1.child_den_eq (frameAt word)
  have hn := ZoneI1.child_num_eq (frameAt word)
  unfold brk
  omega

theorem brk_pos (word : Word) : 0 < brk word := by
  obtain ⟨hdo, hno, -, -⟩ := NativeGrade.odd_parent_facts (frameAt word)
  unfold brk
  omega

/-- **The raw minus slip along the V chain.** For `k < L`: `D₋(vpath k) = 0` at `k = 0`, `−1` for `1 ≤ k ≤ r`, `−2` for `r < k < L`. -/
theorem slip_minus_vpath_raw {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (k : ℕ)
    (hk : (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num) :
    (frameAt word).slip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
      if k = 0 then 0 else if (k : ℤ) ≤ brk word then -1 else -2 := by
  have hP : (frameAt word).Packet (standardField word) := packet_of_strong h hSE
  have hS := hP.strips
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := (frameAt word).child_facts
  have hbr := brk_add_two_le word
  have hr0 := brk_pos word
  by_cases hk0 : k = 0
  · -- `k = 0`: the zero strip at `vFirst = (0, 0)`
    subst hk0
    rw [VChain.vpath_zero, if_pos rfl]
    have hvF : FLatticePaper.Induction.vFirst = ((0 : ℤ), (0 : ℤ)) := rfl
    rw [hvF]
    have ht : (frameAt word).tGrade ((0 : ℤ), (0 : ℤ)) = 0 := by
      unfold ChildFrame.tGrade
      ring
    have := EndpointDeck.Dq_zero (frameAt word) hS (-1) ((0 : ℤ), (0 : ℤ))
      (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega) (by rw [ht]; omega)
    unfold EndpointDeck.Dq at this
    unfold ChildFrame.slip
    exact this
  · by_cases hkL : (k : ℤ) = (frameAt word).child.den + (frameAt word).child.num - 1
    · -- `k = L − 1`: the last V point is `(1, −1) + V`, the period rule and the zero strip at `(1, −1)`
      have hz : VChain.vpath (frameAt word) k = (frameAt word).vLast := by
        rw [FLatticePaper.VChain.vLast_eq_vpath]
        congr 1
        omega
      rw [hz, FinalRootSlip.vLast_eq_I_add_transverse, EndpointDeck.transverse_eq_Vdeck]
      rw [if_neg hk0, if_neg (show ¬ ((k : ℤ) ≤ brk word) by omega)]
      have hdq := EndpointDeck.Dq_smul_transverse (frameAt word) hP (-1) 1 ((1 : ℤ), (-1 : ℤ))
      have hdi := EndpointDeck.Dq_diag (frameAt word) hS (-1) (Or.inr rfl)
      rw [one_zsmul] at hdq
      unfold EndpointDeck.Dq at hdq hdi
      unfold ChildFrame.slip
      linarith
    · -- `1 ≤ k < L − 1`: the clipped identity and the lift at the free V point `vpath k`
      have hk1 : (1 : ℤ) ≤ k := by omega
      have hz : VChain.vpath (frameAt word) k ∈ (frameAt word).freeV :=
        VChain.vpath_free (frameAt word) k (by omega)
      have hzord : (VChain.vpath (frameAt word) k).2 = (k : ℤ) := VChain.vpath_ord (frameAt word) k
      have hne : VChain.vpath (frameAt word) k ≠ (frameAt word).vLast := by
        intro heq
        have h2 := congrArg Prod.snd heq
        have h3 : (frameAt word).vLast.2 = (frameAt word).child.num + (frameAt word).child.den - 1 := rfl
        rw [h3, hzord] at h2
        omega
      have hTraceConj : ∀ w ∈ (frameAt (conjWord word)).freeH,
          (frameAt (conjWord word)).price (standardField (conjWord word)) w =
            (frameAt (conjWord word)).cutPrice - (if w = ((1 : ℤ), (0 : ℤ)) then 0 else 1) :=
        fun w hw => hTr w hw
      have clip := ClippedFreeV.clipped_identity_freeV h hSE hP hz
      have lift := LiftPsi.psi_lift h hSE hTraceConj hz hne
      have hu : (frameAt word).uq = ((frameAt word).eps * (frameAt word).parents.even.den,
          (frameAt word).eps * (frameAt word).parents.even.num) := rfl
      rw [hu, hzord] at lift
      have hsh : (VChain.vpath (frameAt word) k) + (-1 : ℤ) • (frameAt word).shortShift =
          (VChain.vpath (frameAt word) k) - (frameAt word).shortShift := by
        ext <;> simp <;> ring
      unfold ChildFrame.slip
      rw [hsh, clip, lift, if_neg hk0]
      by_cases hkr : (k : ℤ) ≤ brk word
      · have hc1 : ArcCut.ceilDiv (k : ℤ) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) = 1 :=
          RowMinus.ceil_one _ _ hr0 hk1 hkr
        rw [hc1, if_pos hkr]
        all_goals norm_num
      · have hc2 : 2 ≤ ArcCut.ceilDiv (k : ℤ) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) :=
          RowMinus.ceil_two _ _ hr0 (by unfold brk at hkr; omega)
        rw [min_eq_right hc2, if_neg hkr]

/-- **The minus V pattern (rounded).** `J₋(vpath k) = 0` for `k ≤ r` and `−1` for `r < k < L`. -/
theorem roundedSlip_minus_vpath {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (k : ℕ)
    (hk : (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num) :
    (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
      if (k : ℤ) ≤ brk word then 0 else -1 := by
  have hraw := slip_minus_vpath_raw h hSE hTr k hk
  have hr0 := brk_pos word
  unfold ChildFrame.roundedSlip
  rw [hraw]
  by_cases hk0 : k = 0
  · rw [if_pos hk0, if_pos (show (k : ℤ) ≤ brk word by rw [hk0]; norm_num; omega)]
    norm_num
  · rw [if_neg hk0]
    by_cases hkr : (k : ℤ) ≤ brk word
    · rw [if_pos hkr, if_pos hkr]
      norm_num
    · rw [if_neg hkr, if_neg hkr]
      norm_num

/-- **The plus V pattern (rounded).** `J₊(vpath k) = 0` for `k ≤ L − r − 2` and `1` otherwise. -/
theorem roundedSlip_plus_vpath {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hTr : TraceFromPsi.TraceAt (conjWord word)) (k : ℕ)
    (hk : (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num) :
    (frameAt word).roundedSlip (standardField word) 1 (VChain.vpath (frameAt word) k) =
      if (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - brk word - 2 then 0 else 1 := by
  have hP : (frameAt word).Packet (standardField word) := packet_of_strong h hSE
  have hbr := brk_add_two_le word
  have hr0 := brk_pos word
  -- the reversed index `m = L − 1 − k`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = (frameAt word).child.num + (frameAt word).child.den - 1 - (k : ℤ) :=
    ⟨((frameAt word).child.num + (frameAt word).child.den - 1 - (k : ℤ)).toNat, by omega⟩
  have hmL : (m : ℤ) < (frameAt word).child.den + (frameAt word).child.num := by omega
  have hvsub : (frameAt word).vLast - VChain.vpath (frameAt word) k = VChain.vpath (frameAt word) m :=
    RoutePlus.vLast_sub_vpath (frameAt word) k hk m hm
  have hvL : (frameAt word).vLast = ((1 : ℤ), (-1 : ℤ)) + Vdeck (frameAt word) := by
    rw [FinalRootSlip.vLast_eq_I_add_transverse, EndpointDeck.transverse_eq_Vdeck]
  have hI : ∀ z, standardField word (FLatticePaper.Induction.reflectionI - z) = standardField word z :=
    fun z => packet_reflection_I (frameAt word) hP z
  have hrefl : FLatticePaper.Induction.reflectionI - VChain.vpath (frameAt word) k =
      VChain.vpath (frameAt word) m - Vdeck (frameAt word) := by
    rw [← hvsub, hvL]
    unfold FLatticePaper.Induction.reflectionI
    abel
  have key : EndpointDeck.Dq (frameAt word) (standardField word) 1 (VChain.vpath (frameAt word) k) =
      EndpointDeck.Dq (frameAt word) (standardField word) (-1) (VChain.vpath (frameAt word) m) + 2 := by
    rw [CutReflect.Dq_reflect (frameAt word) hI (VChain.vpath (frameAt word) k), hrefl]
    have hsh : VChain.vpath (frameAt word) m - Vdeck (frameAt word) =
        VChain.vpath (frameAt word) m + (-1 : ℤ) • Vdeck (frameAt word) := by
      simp [sub_eq_add_neg]
    rw [hsh, EndpointDeck.Dq_smul_transverse (frameAt word) hP (-1) (-1) (VChain.vpath (frameAt word) m)]
    ring
  have hraw := slip_minus_vpath_raw h hSE hTr m hmL
  have hraw' : EndpointDeck.Dq (frameAt word) (standardField word) (-1) (VChain.vpath (frameAt word) m) =
      if m = 0 then 0 else if (m : ℤ) ≤ brk word then -1 else -2 := hraw
  show (EndpointDeck.Dq (frameAt word) (standardField word) 1 (VChain.vpath (frameAt word) k) + 1) / 2 = _
  rw [key, hraw']
  by_cases hm0 : m = 0
  · rw [if_pos hm0, if_neg (show ¬ ((k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - brk word - 2) by
      subst hm0; omega)]
    norm_num
  · rw [if_neg hm0]
    by_cases hmr : (m : ℤ) ≤ brk word
    · rw [if_pos hmr, if_neg (show ¬ ((k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - brk word - 2) by
        omega)]
      norm_num
    · rw [if_neg hmr, if_pos (show (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - brk word - 2 by
        omega)]
      norm_num

end FLatticePaper.WordVPattern
