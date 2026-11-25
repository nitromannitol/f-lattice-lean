import FLatticePaper.Plane.Induction.RootClassify
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.ClippedCore

/-! Task 72 / Q31 step 2, P4 for the even roots: the parent strip identity `Fp = h0`.

`quarterTurnField_eq_harmonic_of_sp` gives `FqW word y = harmonicGrid y` on the parent `s_p` strip `[1 − 2D, 2r − 1]`. For an even native
V site `z = (x, j)` with `0 ≤ s(z) ≤ 2n` (the even window) and `0 ≤ j ≤ L − 2`, `RootClassify.even_sp_range` puts `s_p(z)` in `[0, 2N]`, and
`s_p(z − V_q) = s_p(z) + 2ε` (`ClippedCore.sp_Vq`) lies in the strip too. So both `Fp z` and `Fp (z − V_q)` equal the harmonic grid. -/

namespace FLatticePaper.ParentStrip

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- The parent strip: `FqW = h0` on `1 − 2D ≤ r y₁ + c_p y₂ ≤ 2r − 1`, with `r = D + N`, `c_p = D − N`. -/
theorem FqW_eq_h0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {y : Site} (hlo : 1 - 2 * (frameAt word).parents.odd.den ≤
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * y.1
        + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * y.2)
    (hhi : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * y.1
        + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * y.2
        ≤ 2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) - 1) :
    FqW word y = harmonicGrid y := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  exact quarterTurnField_eq_harmonic_of_sp hSE.packet.strips hcn hcd hlo hhi

/-- **P4, even roots.** For an even native V site `z = (x, j)` with `0 ≤ j ≤ L − 2` and the even window `0 ≤ s(z) ≤ 2n`,
both `Fp z = h0 z` and `Fp (z − V_q) = h0 (z − V_q)`. -/
theorem even_strip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (hEv : EvenSite z) (hj0 : 0 ≤ z.2)
    (hjL : z.2 ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hs0 : 0 ≤ (frameAt word).sGrade z) (hs1 : (frameAt word).sGrade z ≤ 2 * (frameAt word).child.num) :
    FqW word z = harmonicGrid z ∧
      FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
  have hpos : 0 < (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  have hodd0 : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  obtain ⟨hDpos, hN0', hNle'⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hnn, hnd, -, hd3, -⟩ := (frameAt word).child_facts
  have hεdet : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num :=
    SheetOffsets.eps_eq_det
  have hεd : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).child.den
      - (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hεdet, ZoneI1.child_den_eq (frameAt word), ZoneI1.child_num_eq (frameAt word)]
    ring
  have hε1 : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  have hpar : (z.1 + z.2) % 2 = 0 := hEv
  have hs0' : 0 ≤ ((frameAt word).child.den + (frameAt word).child.num) * z.1
      + ((frameAt word).child.den - (frameAt word).child.num) * z.2 := by
    have := hs0
    unfold ChildFrame.sGrade at this
    exact this
  have hs1' : ((frameAt word).child.den + (frameAt word).child.num) * z.1
      + ((frameAt word).child.den - (frameAt word).child.num) * z.2 ≤ 2 * (frameAt word).child.num := by
    have := hs1
    unfold ChildFrame.sGrade at this
    exact this
  have hodd : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) % 2 = 1 := by omega
  have hodd' : ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) % 2 = 1 := by omega
  have hL : 0 < (frameAt word).child.den + (frameAt word).child.num := by omega
  obtain ⟨hp0, hpU⟩ := RootClassify.even_sp_range (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN0' hDpos
    hodd hodd' hL hj0 hjL hs0' hs1' hpar
  have hpU' : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1
      + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2
      ≤ 2 * (frameAt word).parents.odd.num := by
    rcases hε1 with h1 | h1
    · rw [h1] at hpU
      simp at hpU
      linarith
    · rw [h1] at hpU
      simp at hpU
      linarith
  have hD2 : 2 ≤ (frameAt word).parents.odd.den := by omega
  have hy : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (z.1 - ((frameAt word).parents.even.num - (frameAt word).parents.even.den))
      + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (z.2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den))
      = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1
        + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2 + 2 * (frameAt word).eps := by
    have E := ClippedCore.sp_Vq (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).parents.even.num (frameAt word).parents.even.den
    linear_combination (-1 : ℤ) * E + (-2 : ℤ) * hεdet
  constructor
  · exact FqW_eq_h0 h hSE (by linarith) (by linarith)
  · apply FqW_eq_h0 h hSE
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith

/-- **P4, odd roots.** For an odd native V site `z = (x, j)` with `0 ≤ j ≤ L − 2` and the odd window `2 − c ≤ s(z) ≤ L − 2`,
both `Fp z = h0 z` and `Fp (z − V_q) = h0 (z − V_q)`. -/
theorem odd_strip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (z : Site) (hOd : ¬ EvenSite z) (hj0 : 0 ≤ z.2)
    (hjL : z.2 ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hs0 : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ (frameAt word).sGrade z)
    (hs1 : (frameAt word).sGrade z ≤ (frameAt word).child.den + (frameAt word).child.num - 2) :
    FqW word z = harmonicGrid z ∧
      FqW word (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid (z - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
  have hpos : 0 < (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  have hodd0 : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  obtain ⟨hDpos, hN0', hNle'⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hnn, hnd, -, hd3, -⟩ := (frameAt word).child_facts
  have hεdet : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num :=
    SheetOffsets.eps_eq_det
  have hεd : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).child.den
      - (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hεdet, ZoneI1.child_den_eq (frameAt word), ZoneI1.child_num_eq (frameAt word)]
    ring
  have hε1 : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  have hpar : (z.1 + z.2) % 2 = 1 := by
    unfold EvenSite at hOd
    omega
  have hs0' : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤
      ((frameAt word).child.den + (frameAt word).child.num) * z.1
      + ((frameAt word).child.den - (frameAt word).child.num) * z.2 := by
    have := hs0
    unfold ChildFrame.sGrade at this
    exact this
  have hs1' : ((frameAt word).child.den + (frameAt word).child.num) * z.1
      + ((frameAt word).child.den - (frameAt word).child.num) * z.2
      ≤ (frameAt word).child.den + (frameAt word).child.num - 2 := by
    have := hs1
    unfold ChildFrame.sGrade at this
    exact this
  have hodd : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) % 2 = 1 := by omega
  have hodd' : ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) % 2 = 1 := by omega
  have hL : 0 < (frameAt word).child.den + (frameAt word).child.num := by omega
  obtain ⟨hlo, hhi⟩ := RootClassify.odd_sp_range (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN0' hDpos
    hodd hodd' hL hj0 hjL hs0' hs1' hpar
  have hD2 : 2 ≤ (frameAt word).parents.odd.den := by omega
  have hy : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (z.1 - ((frameAt word).parents.even.num - (frameAt word).parents.even.den))
      + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (z.2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den))
      = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1
        + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2 + 2 * (frameAt word).eps := by
    have E := ClippedCore.sp_Vq (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).parents.even.num (frameAt word).parents.even.den
    linear_combination (-1 : ℤ) * E + (-2 : ℤ) * hεdet
  constructor
  · apply FqW_eq_h0 h hSE
    · linarith
    · linarith
  · apply FqW_eq_h0 h hSE
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith

/-- **P4, the last root `vLast`.** Its parent grade is `s_p(vLast) = 2N − 2ε` (phase 0: `2N + 2`; phase 1: `2N − 2`), and
`s_p(vLast − V_q) = 2N`. Both lie in the parent strip `[1 − 2D, 2r − 1]`. -/
theorem even_strip_vLast {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    FqW word (frameAt word).vLast = harmonicGrid (frameAt word).vLast ∧
      FqW word ((frameAt word).vLast - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) =
        harmonicGrid ((frameAt word).vLast - ((frameAt word).parents.even.num - (frameAt word).parents.even.den,
          (frameAt word).parents.even.num + (frameAt word).parents.even.den)) := by
  have hpos : 0 < (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  have hodd0 : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  obtain ⟨hDpos, hN0', hNle'⟩ := (frameAt word).valid.odd_bounds
  have hεdet : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num :=
    SheetOffsets.eps_eq_det
  have hεd : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).child.den
      - (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hεdet, ZoneI1.child_den_eq (frameAt word), ZoneI1.child_num_eq (frameAt word)]
    ring
  have hε1 : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  have hD2 : 2 ≤ (frameAt word).parents.odd.den := by omega
  have hsp : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * (frameAt word).vLast.1
      + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (frameAt word).vLast.2
      = 2 * (frameAt word).parents.odd.num - 2 * (frameAt word).eps := by
    unfold ChildFrame.vLast
    simp only
    rw [hεd]
    ring
  have hy : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) *
        ((frameAt word).vLast.1 - ((frameAt word).parents.even.num - (frameAt word).parents.even.den))
      + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) *
        ((frameAt word).vLast.2 - ((frameAt word).parents.even.num + (frameAt word).parents.even.den))
      = 2 * (frameAt word).parents.odd.num := by
    have E := ClippedCore.sp_Vq (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).parents.even.num (frameAt word).parents.even.den
    linear_combination hsp + (-1 : ℤ) * E + (-2 : ℤ) * hεdet
  constructor
  · apply FqW_eq_h0 h hSE
    · rw [hsp]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith
    · rw [hsp]
      rcases hε1 with h1 | h1 <;> rw [h1] <;> linarith
  · apply FqW_eq_h0 h hSE
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      linarith
    · simp only [Prod.fst_sub, Prod.snd_sub]
      rw [hy]
      linarith

end FLatticePaper.ParentStrip
