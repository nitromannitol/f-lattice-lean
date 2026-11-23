import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! Task 72 (case (b), link 1): a strict interior site of the closed polygon is nonfree.

For `z` in `StrictInterior`, a deck translate `z + (iK + jV)` has `t = t(z) − jT` and `s = s(z) + iT`.

* H trace: a free H site has `hSpectrum t`; the H windows of `ShortPassages` (`avoid_H_even_low`, `avoid_H_odd_low`) exclude it for
  every `j`.
* V trace: a free V site lies in the closed polygon with `s` in the parity range and `vSpectrum s`. Odd strict interior points have
  `s > L − 2` and are excluded for every `i`. Even strict interior points have `2n < s < T`; `s > L − 2` is excluded for every `i`;
  for `s ≤ L − 2` only `i = 0` survives, and then `j = 0` (otherwise the translate leaves `E`), whose left neighbour lies in `E`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper ShortPassages

theorem strictInterior_nonfree (frame : ChildFrame) {z : Site}
    (hSI : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den z) : Nonfree frame z := by
  obtain ⟨hTd, hN0, hND, hD3⟩ := period_facts frame
  have hT0 : 0 ≤ frame.child.periodDenominator := by
    rw [hTd]
    nlinarith
  have hsz2 : frame.sGrade z % 2 = 0 := sGrade_even frame z
  have htz : frame.tGrade z = FLatticePaper.W1.w1t frame.child.num frame.child.den z := rfl
  have hsz : frame.sGrade z = FLatticePaper.W1.w1s frame.child.num frame.child.den z := rfl
  have hTz : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := rfl
  have hb := hSI.1
  have ha := hSI.2.1
  have hh := hSI.2.2.1
  have hc := hSI.2.2.2
  intro v hv hmem
  obtain ⟨i, j, rfl⟩ := hv
  simp only [Set.mem_union, ChildFrame.freeH, ChildFrame.freeV, Set.mem_setOf_eq] at hmem
  rcases hmem with ⟨hE, -, hsp⟩ | ⟨hE, hnot, hvs⟩
  · -- the H trace
    rw [tGrade_add_combine] at hsp
    by_cases he : EvenSite z
    · have hb' : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.tGrade z := by
        rw [htz]
        simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1T, if_pos he] at hb
        linarith [hTd]
      have ha' : frame.tGrade z < 2 := by
        rw [htz]
        simp only [FLatticePaper.W1.w1a, if_pos he] at ha
        exact ha
      exact avoid_H_even_low frame z he hb' ha' j hsp
    · have hb' : frame.child.den - frame.child.periodDenominator < frame.tGrade z := by
        rw [htz]
        simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1T, if_neg he] at hb
        linarith [hTd]
      have ha' : frame.tGrade z < frame.child.num := by
        rw [htz]
        simp only [FLatticePaper.W1.w1a, if_neg he] at ha
        exact ha
      exact avoid_H_odd_low frame z he hb' ha' j hsp
  · -- the V trace: the translate has `s' = s + iT` and lies in the closed polygon
    rw [sGrade_add_combine] at hvs
    have hvE : EvenSite (frame.child.modifiedDeck.combine i j) := evenSite_of_span frame ⟨i, j, rfl⟩
    by_cases he : EvenSite z
    · -- even strict interior: `2n < s < T`
      have hEz : EvenSite (z + frame.child.modifiedDeck.combine i j) := by
        unfold EvenSite at he hvE ⊢
        simp only [Prod.fst_add, Prod.snd_add] at he hvE ⊢
        omega
      rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hEz, tGrade_add_combine, sGrade_add_combine] at hE
      obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
      have hs1 : 2 * frame.child.num < frame.sGrade z := by
        rw [hsz]
        simp only [FLatticePaper.W1.w1h, if_pos he] at hh
        linarith [hTd]
      have hs2 : frame.sGrade z < frame.child.periodDenominator := by
        rw [hsz]
        simp only [FLatticePaper.W1.w1c, if_pos he] at hc
        linarith [hTd]
      have hs1' : 2 * frame.child.num + 2 ≤ frame.sGrade z := by omega
      have ht1 : frame.child.num + frame.child.den - 2 - frame.child.periodDenominator < frame.tGrade z := by
        rw [htz]
        simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1T, if_pos he] at hb
        linarith [hTd]
      have ht2 : frame.tGrade z < 2 := by
        rw [htz]
        simp only [FLatticePaper.W1.w1a, if_pos he] at ha
        exact ha
      rcases lt_trichotomy i 0 with hi | hi | hi
      · -- `i ≤ −1`: `s + iT < 0`
        have hiT : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
          nlinarith
        linarith
      · -- `i = 0`
        subst hi
        simp only [zero_mul, add_zero] at hvs
        unfold ChildFrame.vSpectrum at hvs
        obtain ⟨-, hvs'⟩ := hvs
        rcases hvs' with ⟨-, h2n⟩ | ⟨-, hL⟩
        · linarith
        · -- the exceptional case `s ≤ L − 2`: `j = 0`, then the left neighbour lies in `E`
          have hj0 : j = 0 := by
            rcases lt_trichotomy j 0 with hj | hj | hj
            · have hjT : j * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
                nlinarith
              linarith
            · exact hj
            · have hjT : frame.child.periodDenominator ≤ j * frame.child.periodDenominator := by
                nlinarith
              linarith
          subst hj0
          have hzero : frame.child.modifiedDeck.combine 0 0 = 0 := by
            unfold PeriodDeck.combine
            simp
          rw [hzero, add_zero] at hnot
          apply hnot
          have hodd' : ¬ EvenSite (z.1 - 1, z.2) := by
            unfold EvenSite at he ⊢
            simp only
            omega
          rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd']
          have e1 : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
            show frame.child.num * (z.1 - 1) - frame.child.den * z.2 = frame.tGrade z - frame.child.num
            unfold ChildFrame.tGrade
            ring
          have e2 : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
            show (frame.child.den + frame.child.num) * (z.1 - 1) + (frame.child.den - frame.child.num) * z.2 =
              frame.sGrade z - (frame.child.den + frame.child.num)
            unfold ChildFrame.sGrade
            ring
          rw [e1, e2]
          refine ⟨?_, ?_, ?_, ?_⟩
          · linarith [hTd]
          · linarith [hTd]
          · linarith
          · linarith [hTd]
      · -- `i ≥ 1`: `s + iT > T + 2n`
        have hiT : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by
          nlinarith
        linarith
    · -- odd strict interior: `L − 2 < s < T + 2 − c`
      have hEz : ¬ EvenSite (z + frame.child.modifiedDeck.combine i j) := by
        unfold EvenSite at he hvE ⊢
        simp only [Prod.fst_add, Prod.snd_add] at he hvE ⊢
        omega
      rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hEz, tGrade_add_combine, sGrade_add_combine] at hE
      obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
      have hs1 : frame.child.num + frame.child.den - 2 < frame.sGrade z := by
        rw [hsz]
        simp only [FLatticePaper.W1.w1h, if_neg he] at hh
        linarith [hTd]
      have hs2 : frame.sGrade z < frame.child.periodDenominator + (2 - frame.child.den + frame.child.num) := by
        rw [hsz]
        simp only [FLatticePaper.W1.w1c, if_neg he] at hc
        linarith [hTd]
      unfold ChildFrame.vSpectrum at hvs
      obtain ⟨-, hvs'⟩ := hvs
      rcases lt_trichotomy i 0 with hi | hi | hi
      · -- `i ≤ −1`: `s + iT < 2 − c`
        have hiT : i * frame.child.periodDenominator ≤ -frame.child.periodDenominator := by
          nlinarith
        linarith
      · -- `i = 0`: `s > L − 2` is not in the V spectrum
        subst hi
        simp only [zero_mul, add_zero] at hvs'
        rcases hvs' with ⟨-, h2n⟩ | ⟨-, hL⟩
        · linarith
        · linarith
      · -- `i ≥ 1`: `s + iT > L − 2`, and above `2n`
        have hiT : frame.child.periodDenominator ≤ i * frame.child.periodDenominator := by
          nlinarith
        rcases hvs' with ⟨-, h2n⟩ | ⟨-, hL⟩
        · linarith
        · linarith

end FLatticePaper.Induction
