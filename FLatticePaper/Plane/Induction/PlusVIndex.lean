import FLatticePaper.Plane.Induction.ConeBoundary
import FLatticePaper.Plane.Induction.ZoneI1

/-! # The plus V-index bound

The plus row carries the positive V labels `V_1..V_{L-r-2}`, where `L = d + n` and `r = odd.den + odd.num` (the minus row carries
`V_1..V_r`). The V index of a cone point is bounded as in `ConeBoundary.V_index` with `r` replaced by `L - r - 2`. The arithmetic
needs `2 ≤ n`, `0 ≤ odd.num`, `odd.num + 1 ≤ odd.den` and `1 ≤ even.num ≤ even.den`, not the minus hypothesis `1 ≤ odd.num`. -/

namespace FLatticePaper.PlusVIndex

open FLatticePaper FLatticePaper.Induction FLatticePaper.ConeBoundary FLatticePaper.ConeFaceArith

/-- The plus bound arithmetic: with `n = 2a + c`, `d = 2b + e`, `a = odd.num`, `b = odd.den`, `c = even.num`, `e = even.den`,
`n (L - r - 2) ≥ L + n - 1`, where `L = d + n` and `r = a + b`. The identity `n(L-r-2) - (d+n-1) = (b-a-1)(n-2) + (e-c)(n-1) + G`
with `G = 4a² + 6a(c-1) + 2c² - 3c - 1 ≥ 0` gives the bound. -/
theorem plus_r_arith {n d a b c e : ℤ} (hn : n = 2 * a + c) (hd : d = 2 * b + e) (hn2 : 2 ≤ n) (ha : 0 ≤ a)
    (hab : a + 1 ≤ b) (hc : 1 ≤ c) (hce : c ≤ e) :
    d + n - 1 ≤ n * (d + n - (b + a) - 2) := by
  have hG : 0 ≤ 4 * a * a + 6 * a * (c - 1) + 2 * c * c - 3 * c - 1 := by
    rcases (show c = 1 ∨ 2 ≤ c by omega) with h1 | h2
    · subst h1
      have ha1 : 1 ≤ a := by omega
      nlinarith
    · have h6 : 0 ≤ 6 * a * (c - 1) := by
        have : (0 : ℤ) ≤ c - 1 := by omega
        positivity
      nlinarith
  have hA : 0 ≤ (b - a - 1) * (n - 2) := mul_nonneg (by omega) (by omega)
  have hB : 0 ≤ (e - c) * (n - 1) := mul_nonneg (by omega) (by omega)
  subst hn hd
  nlinarith [hA, hB, hG]

/-- **The plus V index bound.** The V index of a cone point is at most `L - r - 2`, so the positive V labels `V_1..V_{L-r-2}`
of the plus row cover it. The hypotheses are those of `ConeBoundary.V_index`, with `1 ≤ odd.num` replaced by the arithmetic
facts of `plus_r_arith`. -/
theorem V_index_plus (frame : ChildFrame) {z x : Site} (hz1 : 2 ≤ z.1) (hzd : z.1 < frame.child.den)
    (hzt : frame.child.num + 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den - 2)
    (hn1 : 1 ≤ frame.child.num) (hnd : 2 * frame.child.num ≤ frame.child.den)
    (hnb2 : 2 ≤ frame.child.num) (hpa : 0 ≤ frame.parents.odd.num)
    (hpb : frame.parents.odd.num + 1 ≤ frame.parents.odd.den)
    (hpc : 1 ≤ frame.parents.even.num) (hpe : frame.parents.even.num ≤ frame.parents.even.den) {K : ℕ}
    (hKu : frame.child.num * (K : ℤ) ≤ frame.child.den + 3 * frame.child.num - 2)
    (hx : frame.openRect x) (hcone : CapRay.ConeRoot z K x) (hxe : EvenSite x)
    (hiopen : ¬ frame.openRect (incomingPos x)) :
    1 ≤ x.2 - frame.child.num ∧
      x.2 - frame.child.num ≤ frame.child.den + frame.child.num - (frame.parents.odd.den + frame.parents.odd.num) - 2 := by
  have hxe' : (x.1 + x.2) % 2 = 0 := hxe
  have hiO : ¬ EvenSite (incomingPos x) := by
    unfold incomingPos
    rw [if_pos hxe]
    intro h
    have h' : (x.1 + 1 + x.2) % 2 = 0 := h
    omega
  have hV := (odd_input_V frame hz1 hzt hn1 hnd hx hcone (Or.inr rfl) hiO hiopen).2
  obtain ⟨hn2, hd2⟩ := frame.child_odd
  have hT := periodDenominator_eq frame
  have hVs : frame.child.periodDenominator + 2 - frame.child.den + frame.child.num ≤
      (frame.child.den + frame.child.num) * (x.1 + 1) + (frame.child.den - frame.child.num) * x.2 := by
    unfold incomingPos at hV
    rw [if_pos hxe] at hV
    simp only [ChildFrame.sGrade] at hV
    linarith
  have hOx := hx
  unfold ChildFrame.openRect at hOx
  rw [if_pos hxe] at hOx
  simp only [ChildFrame.tGrade, ChildFrame.sGrade] at hOx
  obtain ⟨_, hOt2, _, hO4⟩ := hOx
  obtain ⟨k, hk⟩ := ConeFaceArith.t_par_even hn2 hd2 hxe'
  have hk2 : 2 * k < 2 := by linarith
  have hk0 : k ≤ 0 := by omega
  have ht0 : frame.child.num * x.1 - frame.child.den * x.2 ≤ 0 := by linarith
  have hzt2 : frame.child.num * z.1 - frame.child.den * z.2 ≤ frame.child.den - 2 := hzt.2
  have hzt1 : frame.child.num + 2 ≤ frame.child.num * z.1 - frame.child.den * z.2 := hzt.1
  have hz2 : z.2 ≤ frame.child.num - 1 := by
    have hzd' : z.1 ≤ frame.child.den - 1 := by omega
    have hA : frame.child.num * z.1 ≤ frame.child.num * (frame.child.den - 1) :=
      mul_le_mul_of_nonneg_left hzd' (by linarith)
    have hB : frame.child.den * z.2 < frame.child.den * frame.child.num := by nlinarith
    have hC := lt_of_mul_lt_mul_left hB (by linarith)
    omega
  have hcx := hcone.2.1
  have hr := plus_r_arith (ZoneI1.child_num_eq frame) (ZoneI1.child_den_eq frame) hnb2 hpa hpb hpc hpe
  have hup := V_up_arith (n := frame.child.num) (d := frame.child.den) (K := (K : ℤ)) (z2 := z.2) (x2 := x.2)
    (r := frame.child.den + frame.child.num - (frame.parents.odd.den + frame.parents.odd.num) - 2) (by linarith) hz2 (by linarith [hcx]) hKu hr
  refine ⟨?_, hup⟩
  by_contra hlow
  push Not at hlow
  have hk' : x.2 ≤ frame.child.num := by omega
  exact ConeFaceArith.V_low_arith hT hn1 hnd hn2 hd2 hxe' ht0 hO4 hVs hk'

end FLatticePaper.PlusVIndex
