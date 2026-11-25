import FLatticePaper.Plane.Induction.QueryClass
import FLatticePaper.Plane.Induction.QueryCPFrame
import FLatticePaper.Plane.Induction.TpFrame
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.CutOnePerProper
import FLatticePaper.Plane.Induction.OddFreeH
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.QueryCP

/-! Task w3, step 1(b)(i)–(ii): helpers for the transport classification at the frame level. -/

namespace FLatticePaper.QueryClassFrame

open Farey FLatticePaper FLatticePaper.Induction

/-- The sheet shift has coordinates `(1 − W)(d_q, n_q)` (the unmodified kernel of the even parent is `(den, num)`). -/
theorem sheetShift_coords (frame : ChildFrame) :
    frame.sheetShift = ((1 - frame.phaseW) * frame.parents.even.den, (1 - frame.phaseW) * frame.parents.even.num) := by
  unfold ChildFrame.sheetShift Fraction.unmodifiedDeck
  simp

/-- The sheet shift preserves parity: `d_q + n_q` is even. -/
theorem evenSite_sub_shift (frame : ChildFrame) (z : Site) :
    EvenSite (z - frame.sheetShift) ↔ EvenSite z := by
  have hev : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hs : (frame.sheetShift.1 + frame.sheetShift.2) % 2 = 0 := by
    rw [sheetShift_coords]
    simp only
    have : (1 - frame.phaseW) * frame.parents.even.den + (1 - frame.phaseW) * frame.parents.even.num =
        (1 - frame.phaseW) * (frame.parents.even.num + frame.parents.even.den) := by ring
    rw [this, Int.mul_emod]
    simp [hev]
  unfold EvenSite
  simp only [Prod.fst_sub, Prod.snd_sub]
  omega

/-- The parent t-grade of the shifted point: `t_p(z − sheetShift) = t_p(z) − (1 − W) ε`. -/
theorem tp_sub_shift (frame : ChildFrame) (z : Site) :
    frame.parentTGrade (z - frame.sheetShift) = frame.parentTGrade z - (1 - frame.phaseW) * frame.eps := by
  rw [TpFrame.parentTGrade_sub, W1ArcBottom.parentTGrade_sheetShift]

/-- The conjugate's period is `L' = 2D`. -/
theorem period_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    FreeEnum.period (frameAt (conjWord word)) = 2 * (frameAt word).parents.odd.den := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold FreeEnum.period
  rw [hcn, hcd]
  ring

/-- The conjugate's transverse deck vector is `V' = (−2N, 2D)`. -/
theorem vdeck_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) :
    Vdeck (frameAt (conjWord word)) = (-(2 * (frameAt word).parents.odd.num), 2 * (frameAt word).parents.odd.den) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  unfold Vdeck
  rw [hcn, hcd]
  ext <;> simp <;> ring

/-- The representative of an even `x` is odd. -/
theorem rep_not_even_of_even {word : Word} (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i) (hxe : EvenSite x) :
    ¬ EvenSite ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ) := by
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  unfold EvenSite at hxe ⊢
  have e : (-x.2 + 2 * N * m) + i = (x.1 - x.2 - 1) + 2 * (m * (N - D)) := by
    linear_combination (-1 : ℤ) * hk
  simp only
  rw [e]
  generalize m * (N - D) = c
  omega

/-- The representative of an odd `x` is even. -/
theorem rep_even_of_odd {word : Word} (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i) (hxo : ¬ EvenSite x) :
    EvenSite ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ) := by
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  unfold EvenSite at hxo ⊢
  have e : (-x.2 + 2 * N * m) + i = (x.1 - x.2 - 1) + 2 * (m * (N - D)) := by
    linear_combination (-1 : ℤ) * hk
  simp only
  rw [e]
  generalize m * (N - D) = c
  omega

/-- The conjugate's V spectrum at the representative: `vSpectrum'(s'(rep))` iff `1 ≤ t_p ≤ r − 1`. -/
theorem vSpectrum_rep {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (x : ℤ × ℤ) (m i : ℤ)
    (hk : x.1 - 1 = 2 * (frameAt word).parents.odd.den * m + i)
    (hN : 1 ≤ (frameAt word).parents.odd.num) :
    (frameAt (conjWord word)).vSpectrum
        ((frameAt (conjWord word)).sGrade ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ)) ↔
      1 ≤ (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ∧
        (frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2 ≤
          (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hs := QueryCP.key_sprime (frameAt word).parents.odd.num (frameAt word).parents.odd.den x.1 x.2 m i hk
  have hsg : (frameAt (conjWord word)).sGrade ((-x.2 + 2 * (frameAt word).parents.odd.num * m, i) : ℤ × ℤ) =
      2 * ((frameAt word).parents.odd.num * x.1 - (frameAt word).parents.odd.den * x.2) -
        2 * (frameAt word).parents.odd.num := by
    unfold ChildFrame.sGrade
    simp only
    rw [hcn, hcd]
    linear_combination hs
  rw [hsg]
  unfold ChildFrame.vSpectrum
  rw [hcn, hcd]
  omega

/-- **Uniqueness of the representative.** Under the conjugate's one-point-per-ordinate cut (named input `hcutC`), a free V
point of ordinate `i` in the period is the base point of that ordinate. -/
theorem rep_eq_base {word : Word} (hcutC : FreeEnum.CutOnePerOrdinate (frameAt (conjWord word))) {base : ℤ → Site}
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) {p : ℤ × ℤ} (hp : p ∈ (frameAt (conjWord word)).freeV)
    {i : ℤ} (hi0 : 0 ≤ i) (hi1 : i < FreeEnum.period (frameAt (conjWord word))) (hpi : p.2 = i) :
    p = base i := by
  obtain ⟨x0, -, huniq⟩ := hcutC i hi0 hi1
  have e1 : p.1 = x0 := huniq p.1 (by
    show (p.1, i) ∈ (frameAt (conjWord word)).freeV
    rw [← hpi]
    exact hp)
  have e2 : (base i).1 = x0 := huniq (base i).1 (by
    show ((base i).1, i) ∈ (frameAt (conjWord word)).freeV
    have h1 := (hbase i hi0 hi1).1
    have h2 := (hbase i hi0 hi1).2
    have h3 : ((base i).1, i) = base i := Prod.ext rfl h2.symm
    rw [h3]
    exact h1)
  exact Prod.ext (by rw [e1, e2]) (by rw [hpi, (hbase i hi0 hi1).2])

end FLatticePaper.QueryClassFrame
