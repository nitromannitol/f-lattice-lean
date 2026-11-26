import FLatticePaper.Plane.Induction.VLastOfT
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.FanInputs

/-! # The odd free V sites have `t ≥ 2d + n − P`

For an odd free V site with grades `t, s` and the identity `P x = (d − n) t + d s`, put `u = t + P` and `k = x + (d − n)`.
Then `P k = (d − n) u + d s`. The low `s`-range `[0, 2n]` forces `k = 1`, then `(d − n)(u − L) = d (2n − s)` and
coprimality give `u = L`, which is even, a contradiction. The high `s`-range `[2 − d + n, L − 2]` forces `k ∈ {0, 1, 2}`,
and each case closes by coprimality and parity. -/

namespace FLatticePaper.VOddLower

open Farey FLatticePaper FLatticePaper.Induction

theorem core_odd_lower (n d P t s x : ℤ) (hn0 : 0 < n) (hnd : n < d) (hdn : 2 ≤ d - n)
    (hnodd : n % 2 = 1) (hdodd : d % 2 = 1)
    (hP : P = d ^ 2 + 2 * d * n - n ^ 2) (hPev : P % 2 = 0)
    (hcop : IsCoprime (d - n) d)
    (hA : P * x = (d - n) * t + d * s) (htp : t % 2 = 1)
    (hpl : n - P ≤ t) (hsl : 2 - d + n ≤ s)
    (hsp : (0 ≤ s ∧ s ≤ 2 * n) ∨ (2 - d + n ≤ s ∧ s ≤ d + n - 2)) :
    2 * d + n - P ≤ t := by
  by_contra hcon
  have hPpos : 0 < P := by rw [hP]; nlinarith
  have hcpos : 0 < d - n := by omega
  have hdpos : 0 < d := by omega
  have hL : (d + n) % 2 = 0 := by omega
  have hu_lo : n ≤ t + P := by omega
  have hu_hi : t + P ≤ 2 * d + n - 2 := by omega
  have hk : P * (x + (d - n)) = (d - n) * (t + P) + d * s := by linear_combination hA
  have hcn : 0 < (d - n) * n := mul_pos hcpos hn0
  have e_u_lo : (d - n) * n ≤ (d - n) * (t + P) := mul_le_mul_of_nonneg_left hu_lo hcpos.le
  have e_u_hi : (d - n) * (t + P) ≤ (d - n) * (2 * d + n - 2) := mul_le_mul_of_nonneg_left hu_hi hcpos.le
  -- the key step: from c * (u - L) = d * (2n - s) and coprimality, with the bound 2n - s > -c, u - L = d * m and m ≥ 0
  have key_one : ∀ m : ℤ, ∀ (u : ℤ), (d - n) * (u - (d + n)) = d * (2 * n - s) → 2 * n - s = (d - n) * m →
      -(d - n) < 2 * n - s → t + P = u → (u = d + n) := by
    intro m u h1 h2 h3 h4
    have hm : 0 ≤ m := by
      by_contra hm
      have : m ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left this hcpos.le]
    have hdm : u - (d + n) = d * m := by
      have h5 : (d - n) * (u - (d + n)) = (d - n) * (d * m) := by rw [h1, h2]; ring
      exact mul_left_cancel₀ hcpos.ne' h5
    have hm0 : m = 0 := by
      by_contra hm0
      have hm1 : 1 ≤ m := by omega
      nlinarith [mul_le_mul_of_nonneg_left hm1 hdpos.le]
    rw [hm0, mul_zero] at hdm
    omega
  rcases hsp with ⟨hs0, hs2n⟩ | ⟨hs1, hs2⟩
  · -- LOW: 0 ≤ s ≤ 2n, so k = x + (d - n) = 1
    have hkpos : 0 < x + (d - n) := by
      by_contra h
      have h' : x + (d - n) ≤ 0 := by omega
      nlinarith [mul_le_mul_of_nonneg_left h' hPpos.le, mul_nonneg hdpos.le hs0]
    have hk2 : x + (d - n) < 2 := by
      by_contra h
      have h' : 2 ≤ x + (d - n) := by omega
      nlinarith [mul_le_mul_of_nonneg_left h' hPpos.le, mul_le_mul_of_nonneg_left hs2n hdpos.le]
    have hk1 : x + (d - n) = 1 := by omega
    have hbal : (d - n) * (t + P) + d * s = P := by rw [← hk, hk1]; ring
    have h1 : (d - n) * (t + P - (d + n)) = d * (2 * n - s) := by linear_combination hbal + hP
    have hdvd : (d - n) ∣ d * (2 * n - s) := ⟨t + P - (d + n), h1.symm⟩
    obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdvd
    exact key_one m (t + P) h1 hm (by omega) rfl |> fun h => by omega
  · -- HIGH: 2 - d + n ≤ s ≤ d + n - 2, so k ∈ {0, 1, 2}
    have hkge : 0 ≤ x + (d - n) := by
      by_contra h
      have h' : x + (d - n) ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left h' hPpos.le, mul_le_mul_of_nonneg_left hs1 hdpos.le]
    have hkle : x + (d - n) ≤ 2 := by
      by_contra h
      have h' : 3 ≤ x + (d - n) := by omega
      nlinarith [mul_le_mul_of_nonneg_left h' hPpos.le, mul_le_mul_of_nonneg_left hs2 hdpos.le]
    rcases (show x + (d - n) = 0 ∨ x + (d - n) = 1 ∨ x + (d - n) = 2 by omega) with h0 | h1' | h2'
    · -- k = 0: d s = -c (t + P) < 0, so s < 0 and s = c m with m ≥ 0 by the lower bound: contradiction
      have hbal0 : (d - n) * (t + P) + d * s = 0 := by rw [← hk, h0]; ring
      have hsneg : s < 0 := by
        by_contra h
        have h' : 0 ≤ s := by omega
        linarith [mul_nonneg hdpos.le h', mul_pos hcpos (show 0 < t + P by omega)]
      have hdvd0 : (d - n) ∣ d * s := ⟨-(t + P), by linear_combination hbal0⟩
      obtain ⟨m0, hm0⟩ := hcop.dvd_of_dvd_mul_left hdvd0
      rcases le_or_gt m0 (-1) with hm | hm
      · linarith [mul_le_mul_of_nonneg_left hm hcpos.le]
      · have : 0 ≤ m0 := by omega
        linarith [mul_nonneg hcpos.le this]
    · -- k = 1: the same relation as in the low case, with 2n - s > -(d - n) from s ≤ d + n - 2
      have hbal : (d - n) * (t + P) + d * s = P := by rw [← hk, h1']; ring
      have h1 : (d - n) * (t + P - (d + n)) = d * (2 * n - s) := by linear_combination hbal + hP
      have hdvd : (d - n) ∣ d * (2 * n - s) := ⟨t + P - (d + n), h1.symm⟩
      obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdvd
      have := key_one m (t + P) h1 hm (by omega) rfl
      omega
    · -- k = 2: (d - n)(t + P - 2L) = d (4n - s), so t + P - 2L = d m2 with m2 ∈ {-1, -2}
      have hbal2 : (d - n) * (t + P) + d * s = 2 * P := by rw [← hk, h2']; ring
      have h2 : (d - n) * (t + P - 2 * (d + n)) = d * (4 * n - s) := by linear_combination hbal2 + 2 * hP
      have hdvd2 : (d - n) ∣ d * (4 * n - s) := ⟨t + P - 2 * (d + n), h2.symm⟩
      obtain ⟨m2, hm2⟩ := hcop.dvd_of_dvd_mul_left hdvd2
      have hdm2 : t + P - 2 * (d + n) = d * m2 := by
        have h5 : (d - n) * (t + P - 2 * (d + n)) = (d - n) * (d * m2) := by rw [h2, hm2]; ring
        exact mul_left_cancel₀ hcpos.ne' h5
      have hm2a : m2 ≤ -1 := by
        by_contra h
        have h' : 0 ≤ m2 := by omega
        linarith [mul_nonneg hdpos.le h']
      have hm2b : -2 ≤ m2 := by
        by_contra h
        have h' : m2 ≤ -3 := by omega
        linarith [mul_le_mul_of_nonneg_left h' hdpos.le]
      interval_cases m2
      · -- m2 = -1: s = d + 3n, which is above d + n - 2
        omega
      · -- m2 = -2: t + P = 2n is even, contradicting t odd
        omega


open FLatticePaper.W1

/-- **An odd free V site has `t ≥ 2d + n − P`.** -/
theorem odd_lower_of_mem (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    2 * frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hmem := (FreeCutSucc.mem_freeV_iff frame z).mp hz
  obtain ⟨hcl, -, hvs⟩ := hmem
  unfold closedRect at hcl
  rw [if_neg hodd] at hcl
  have hpl : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z := by
    rw [frame_periodDenominator_eq]; exact hcl.1
  have hsl : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z := hcl.2.2.1
  have hsp : (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num) ∨
      (2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
        frame.sGrade z ≤ frame.child.den + frame.child.num - 2) := hvs.2
  have htp : frame.tGrade z % 2 = 1 := by
    have h := FanInputs.tGrade_mod_two frame z
    unfold EvenSite at hodd
    omega
  have hcop : IsCoprime (frame.child.den - frame.child.num) frame.child.den := by
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * frame.child.num + v * frame.child.den = 1 := frame.child_reduced
    exact ⟨-u, u + v, by linear_combination huv⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, frame.child.den = 2 * a + 1 := ⟨frame.child.den / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, frame.child.num = 2 * b + 1 := ⟨frame.child.num / 2, by omega⟩
  have hPQ : frame.child.periodDenominator = 2 * (2 * a ^ 2 + 4 * a + 4 * a * b - 2 * b ^ 2 + 1) := by
    rw [hP, ha, hb]; ring
  have hPev : frame.child.periodDenominator % 2 = 0 := by
    rw [hPQ]; exact Int.mul_emod_right 2 _
  exact core_odd_lower frame.child.num frame.child.den frame.child.periodDenominator (frame.tGrade z)
    (frame.sGrade z) z.1 hn0 hnd hdn hnodd hdodd hP hPev hcop (frame.ident_a z) htp hpl hsl hsp

end FLatticePaper.VOddLower
