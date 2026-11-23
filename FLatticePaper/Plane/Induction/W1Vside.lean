import FLatticePaper.Plane.Induction.W1Hc
import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 53, W1 section 2, the V side: the parent s-coordinate of the V-side query lies in the parent's h0 window.

With `T t_p... ` the identities `T · s_p(r) = C s(r) + 2 ε t(r)` (`parent_transform_s`), the V-side collar ranges of
W1_CONSTRUCTOR §2 (`even: L − T ≤ t ≤ 0, 2n < s ≤ 2L − 2`; `odd: d − T < t ≤ n − 2, L − 2 < s ≤ 3d + n − 2`) and the
parity of the lattice (`s` is even: `L` and `d − n` are even; `s_p` is even at even sites and `≡ D + N` mod 2 at odd sites),
the query coordinates `s* = s_p(r)` (W1) and `s* = s_p(r) − 2` (W0) satisfy the archive's windows. The integer cores below
are proved from these hypotheses only (the odd-W0 lower bound uses the parity of `s`, the lattice argument of the archive). -/

namespace FLatticePaper.W1Vside

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1Hc FLatticePaper.W1Seeds

/-- Even sites, ε = 1 (W1): `2N ≤ s_p < 2(D+N)`. -/
theorem even_pos (n d D N C s t T sp : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d) (hD : 1 ≤ D)
    (hC : C * (d + n) = (D + N) * T - 2 * n) (hCd : C * d = D * T + (d - n))
    (hT : 0 < T) (htp : T * sp = C * s + 2 * t)
    (hs1 : 2 * n + 2 ≤ s) (hs2 : s ≤ 2 * (d + n) - 2) (ht1 : d + n - T ≤ t) (ht2 : t ≤ 0)
    (hspe : sp % 2 = 0) : 2 * N ≤ sp ∧ sp < 2 * (D + N) := by
  have hC0 : 0 ≤ C := by nlinarith
  have hCpos : 0 < C := by nlinarith
  have hl : C * (2 * n + 2) ≤ C * s := mul_le_mul_of_nonneg_left hs1 hC0
  have hu : C * s ≤ C * (2 * (d + n) - 2) := mul_le_mul_of_nonneg_left hs2 hC0
  have hlow : T * (2 * N - 2) < T * sp := by nlinarith
  have hlow' : 2 * N - 2 < sp := lt_of_mul_lt_mul_left hlow hT.le
  have hup : T * sp < T * (2 * (D + N)) := by nlinarith
  have hup' : sp < 2 * (D + N) := lt_of_mul_lt_mul_left hup hT.le
  constructor
  · omega
  · exact hup'

/-- Even sites, ε = −1 (W0): `2N + 2 ≤ s_p < 2(D+N) + 2`, i.e. `2N ≤ s_p − 2 < 2(D+N)`. -/
theorem even_neg (n d D N C s t T sp : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hC : C * (d + n) = (D + N) * T + 2 * n) (hCd : C * d = D * T - (d - n))
    (hCL : d + n ≤ C) (hT : 0 < T) (htp : T * sp = C * s - 2 * t)
    (hs1 : 2 * n + 2 ≤ s) (hs2 : s ≤ 2 * (d + n) - 2) (ht1 : d + n - T ≤ t) (ht2 : t ≤ 0)
    (hspe : sp % 2 = 0) : 2 * N ≤ sp - 2 ∧ sp - 2 < 2 * (D + N) := by
  have hC0 : 0 ≤ C := by linarith
  have hl : C * (2 * n + 2) ≤ C * s := mul_le_mul_of_nonneg_left hs1 hC0
  have hu : C * s ≤ C * (2 * (d + n) - 2) := mul_le_mul_of_nonneg_left hs2 hC0
  have hlow : T * (2 * N) < T * sp := by nlinarith
  have hlow' : 2 * N < sp := lt_of_mul_lt_mul_left hlow hT.le
  have hup : T * sp < T * (2 * (D + N) + 2) := by nlinarith
  have hup' : sp < 2 * (D + N) + 2 := lt_of_mul_lt_mul_left hup hT.le
  constructor
  · omega
  · omega

/-- Odd sites, ε = 1 (W1): `D + N − 2 < s_p < 3D + N`. -/
theorem odd_pos (n d D N C s t T sp : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hC : C * (d + n) = (D + N) * T - 2 * n) (hCd : C * d = D * T + (d - n))
    (hCL : d + n ≤ C) (hT : 0 < T) (htp : T * sp = C * s + 2 * t)
    (hs1 : d + n ≤ s) (hs2 : s ≤ 3 * d + n - 2) (ht1 : d - T + 1 ≤ t) (ht2 : t ≤ n - 2) :
    (D + N) - 2 < sp ∧ sp < 3 * D + N := by
  have hl : C * (d + n) ≤ C * s := mul_le_mul_of_nonneg_left hs1 (by linarith)
  have hu : C * s ≤ C * (3 * d + n - 2) := mul_le_mul_of_nonneg_left hs2 (by linarith)
  have hlow : T * (D + N - 2) < T * sp := by nlinarith
  have hlow' : D + N - 2 < sp := lt_of_mul_lt_mul_left hlow hT.le
  have hup : T * sp < T * (3 * D + N) := by nlinarith
  have hup' : sp < 3 * D + N := lt_of_mul_lt_mul_left hup hT.le
  exact ⟨hlow', hup'⟩

/-- Odd sites, ε = −1 (W0): `D + N < s_p < 3D + N + 2`, i.e. `D + N − 2 < s_p − 2 < 3D + N`. -/
theorem odd_neg (n d D N C s t T sp : ℤ) (hn : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hC : C * (d + n) = (D + N) * T + 2 * n) (hCd : C * d = D * T - (d - n))
    (hCL : d + n ≤ C) (hT : 0 < T) (htp : T * sp = C * s - 2 * t)
    (hs1 : d + n ≤ s) (hs2 : s ≤ 3 * d + n - 2) (ht1 : d - T + 1 ≤ t) (ht2 : t ≤ n - 2) :
    (D + N) - 2 < sp - 2 ∧ sp - 2 < 3 * D + N := by
  have hl : C * (d + n) ≤ C * s := mul_le_mul_of_nonneg_left hs1 (by linarith)
  have hu : C * s ≤ C * (3 * d + n - 2) := mul_le_mul_of_nonneg_left hs2 (by linarith)
  have hlow : T * (D + N) < T * sp := by nlinarith
  have hlow' : D + N < sp := lt_of_mul_lt_mul_left hlow hT.le
  have hup : T * sp < T * (3 * D + N + 2) := by nlinarith
  have hup' : sp < 3 * D + N + 2 := lt_of_mul_lt_mul_left hup hT.le
  exact ⟨by omega, by omega⟩


open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 in
/-- The child's `s` is even at every site (`L` and `d − n` are even). -/
theorem w1s_even (frame : ChildFrame) (r : Site) : w1s frame.child.num frame.child.den r % 2 = 0 := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨k, hk⟩ : ∃ k : ℤ, frame.child.den + frame.child.num = 2 * k :=
    ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, frame.child.den - frame.child.num = 2 * m :=
    ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  unfold w1s
  rw [show (frame.child.den + frame.child.num) * r.1 + (frame.child.den - frame.child.num) * r.2 =
    2 * (k * r.1 + m * r.2) by linear_combination r.1 * hk + r.2 * hm]
  exact Int.mul_emod_right 2 _


/-- The V-side query for W1, `I − (y − V_q)` with `y = V + I − r` (the archive's `r = R − z`). -/
def queryOne (frame : ChildFrame) (r : Site) : Site :=
  (1 - ((1 + (frame.child.num - frame.child.den) - r.1) - (frame.parents.even.num - frame.parents.even.den)),
    -1 - ((-1 + (frame.child.num + frame.child.den) - r.2) - (frame.parents.even.num + frame.parents.even.den)))

/-- The V-side query for W0, `y − V_q` with `y = r`. -/
def queryZero (frame : ChildFrame) (r : Site) : Site :=
  (r.1 - (frame.parents.even.num - frame.parents.even.den), r.2 - (frame.parents.even.num + frame.parents.even.den))

/-- The parent coordinate of the W1 query is that of `r`. -/
theorem sp_queryOne (frame : ChildFrame) (hE : frame.eps = 1) (r : Site) :
    frame.parentSGrade (queryOne frame r) = frame.parentSGrade r := by
  have h1 := frame.eps_eq
  have h2 := even_det frame
  rw [hE] at h1 h2
  unfold ChildFrame.parentSGrade queryOne
  linear_combination (-2 : ℤ) * h1 + (-2 : ℤ) * h2

/-- The parent coordinate of the W0 query is that of `r` minus 2. -/
theorem sp_queryZero (frame : ChildFrame) (hE : frame.eps = -1) (r : Site) :
    frame.parentSGrade (queryZero frame r) = frame.parentSGrade r - 2 := by
  have h2 := even_det frame
  rw [hE] at h2
  unfold ChildFrame.parentSGrade queryZero
  linear_combination (2 : ℤ) * h2

/-- The parent coordinate of an even site is even. -/
theorem sp_even_of_even (frame : ChildFrame) (r : Site) (hr : EvenSite r) :
    frame.parentSGrade r % 2 = 0 := by
  have hr' : (r.1 + r.2) % 2 = 0 := hr
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r.1 + r.2 = 2 * k := ⟨(r.1 + r.2) / 2, by omega⟩
  unfold ChildFrame.parentSGrade
  rw [show (frame.parents.odd.den + frame.parents.odd.num) * r.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * r.2 =
      2 * ((frame.parents.odd.den + frame.parents.odd.num) * k - frame.parents.odd.num * r.2) by
    linear_combination (frame.parents.odd.den + frame.parents.odd.num) * hk]
  exact Int.mul_emod_right 2 _

/-- The parent h0 window: the conjugate's ordinary strip gives `Fp = h0` for `1 − 2D ≤ s_p ≤ 2(D+N) − 1`. -/
theorem parent_value {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hstrips : conj.HasStrips G) (Q : Site)
    (hlo : 1 - 2 * frame.parents.odd.den ≤ frame.parentSGrade Q)
    (hhi : frame.parentSGrade Q ≤ 2 * (frame.parents.odd.den + frame.parents.odd.num) - 1) :
    quarterTurnField G Q = harmonicGrid Q := by
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hconj
  apply quarterTurnField_eq_harmonic hstrips
  · rw [quarterTurn_site]
    unfold ChildFrame.tGrade ChildFrame.parentSGrade at *
    dsimp only
    rw [hcn, hcd]
    linarith
  · rw [quarterTurn_site]
    unfold ChildFrame.tGrade ChildFrame.parentSGrade at *
    dsimp only
    rw [hcn, hcd]
    linarith

/-- **The V-side even window, W1 (ε = 1): the parent query is in the parent h0 strip.** -/
theorem even_value_one {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hstrips : conj.HasStrips G) (hE : frame.eps = 1)
    (r : Site) (hr : EvenSite r)
    (ht1 : frame.child.den + frame.child.num - frame.child.periodDenominator ≤ w1t frame.child.num frame.child.den r)
    (ht2 : w1t frame.child.num frame.child.den r ≤ 0)
    (hs1 : 2 * frame.child.num < w1s frame.child.num frame.child.den r)
    (hs2 : w1s frame.child.num frame.child.den r ≤ 2 * (frame.child.den + frame.child.num) - 2) :
    quarterTurnField G (queryOne frame r) = harmonicGrid (queryOne frame r) := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := frame.valid.odd_bounds.2.1
  have hTs := parent_transform_s frame r
  have hCL := frame.parentC_mul_L
  have hCd := frame.parentC_mul_den
  rw [frame_periodDenominator_eq] at hCL hCd ht1
  rw [hE] at hTs hCL hCd
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hsp := sp_queryOne frame hE r
  have hsv := w1s_even frame r
  have hev := sp_even_of_even frame r hr
  obtain ⟨hlo, hhi⟩ := even_pos frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num
    frame.parentC (w1s frame.child.num frame.child.den r) (w1t frame.child.num frame.child.den r)
    (w1T frame.child.num frame.child.den) (frame.parentSGrade r) (by omega) (by omega) hD
    (by linarith [hCL]) (by linarith [hCd]) hT (by linarith [hTs]) (by omega) (by linarith [hs2])
    ht1 ht2 hev
  exact parent_value hconj hstrips (queryOne frame r) (by rw [hsp]; omega) (by rw [hsp]; omega)

/-- The W1 query keeps the parity of `r` (its coordinate sum is `r₁ + r₂` modulo 2). -/
theorem queryOne_sum (frame : ChildFrame) (r : Site) :
    (queryOne frame r).1 + (queryOne frame r).2 = r.1 + r.2 - 2 * (frame.child.num - frame.parents.even.num) := by
  unfold queryOne
  ring

/-- The W0 query keeps the parity of `r`. -/
theorem queryZero_sum (frame : ChildFrame) (r : Site) :
    (queryZero frame r).1 + (queryZero frame r).2 = r.1 + r.2 - 2 * frame.parents.even.num := by
  unfold queryZero
  ring

/-- On an odd site, `s_p ≡ D + N` modulo 2. -/
theorem sp_odd_parity (frame : ChildFrame) (r : Site) (hr : ¬ EvenSite r) :
    (frame.parentSGrade r - (frame.parents.odd.den + frame.parents.odd.num)) % 2 = 0 := by
  have hr' : ¬ ((r.1 + r.2) % 2 = 0) := hr
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r.1 + r.2 = 2 * k + 1 := ⟨(r.1 + r.2) / 2, by omega⟩
  unfold ChildFrame.parentSGrade
  rw [show (frame.parents.odd.den + frame.parents.odd.num) * r.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * r.2 -
      (frame.parents.odd.den + frame.parents.odd.num) =
      2 * ((frame.parents.odd.den + frame.parents.odd.num) * k - frame.parents.odd.num * r.2) by
    linear_combination (frame.parents.odd.den + frame.parents.odd.num) * hk]
  exact Int.mul_emod_right 2 _

/-- The parent constant dominates the child's `L`: `C = D(d+n) + N(d−n) ≥ d + n`. -/
theorem parentC_ge_L (frame : ChildFrame) : frame.child.den + frame.child.num ≤ frame.parentC := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := frame.valid.odd_bounds.2.1
  unfold ChildFrame.parentC
  nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.parents.odd.den - 1 by omega) (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega),
    mul_nonneg hN (show (0:ℤ) ≤ frame.child.den - frame.child.num by omega)]

/-- **The V-side even window, W0 (ε = −1).** -/
theorem even_value_zero {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hstrips : conj.HasStrips G) (hE : frame.eps = -1)
    (r : Site) (hr : EvenSite r)
    (ht1 : frame.child.den + frame.child.num - frame.child.periodDenominator ≤ w1t frame.child.num frame.child.den r)
    (ht2 : w1t frame.child.num frame.child.den r ≤ 0)
    (hs1 : 2 * frame.child.num < w1s frame.child.num frame.child.den r)
    (hs2 : w1s frame.child.num frame.child.den r ≤ 2 * (frame.child.den + frame.child.num) - 2) :
    quarterTurnField G (queryZero frame r) = harmonicGrid (queryZero frame r) := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := frame.valid.odd_bounds.2.1
  have hTs := parent_transform_s frame r
  have hCL := frame.parentC_mul_L
  have hCd := frame.parentC_mul_den
  rw [frame_periodDenominator_eq] at hCL hCd ht1
  rw [hE] at hTs hCL hCd
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hsp := sp_queryZero frame hE r
  have hsv := w1s_even frame r
  have hev := sp_even_of_even frame r hr
  have hCL' := parentC_ge_L frame
  obtain ⟨hlo, hhi⟩ := even_neg frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num
    frame.parentC (w1s frame.child.num frame.child.den r) (w1t frame.child.num frame.child.den r)
    (w1T frame.child.num frame.child.den) (frame.parentSGrade r) (by omega) (by omega)
    (by linarith [hCL]) (by linarith [hCd]) (parentC_ge_L frame) hT (by linarith [hTs]) (by omega) (by linarith [hs2])
    ht1 ht2 hev
  exact parent_value hconj hstrips (queryZero frame r) (by rw [hsp]; omega) (by rw [hsp]; omega)

/-- **The V-side odd window, W1 (ε = 1).** The parent coordinate `s* = s_p(r)` lies in `(D+N−2, 3D+N)` and is odd-parity
congruent to `D + N`, so `s* ≤ 3D + N − 2`; the parent h0 value on this range is the named strengthened strip `hStrong`
(W1_CONSTRUCTOR §1: `odd s_p ∈ [2 − 3D + N, 3D + N − 2]`). -/
theorem odd_value_one {frame : ChildFrame} {G : Field} (hE : frame.eps = 1)
    (hStrong : ∀ Q : Site, ¬ EvenSite Q → 2 - 3 * frame.parents.odd.den + frame.parents.odd.num ≤ frame.parentSGrade Q →
      frame.parentSGrade Q ≤ 3 * frame.parents.odd.den + frame.parents.odd.num - 2 →
      quarterTurnField G Q = harmonicGrid Q)
    (r : Site) (hr : ¬ EvenSite r)
    (ht1 : frame.child.den - frame.child.periodDenominator + 1 ≤ w1t frame.child.num frame.child.den r)
    (ht2 : w1t frame.child.num frame.child.den r ≤ frame.child.num - 2)
    (hs1 : frame.child.den + frame.child.num - 2 < w1s frame.child.num frame.child.den r)
    (hs2 : w1s frame.child.num frame.child.den r ≤ 3 * frame.child.den + frame.child.num - 2) :
    quarterTurnField G (queryOne frame r) = harmonicGrid (queryOne frame r) := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := frame.valid.odd_bounds.2.1
  have hNle : frame.parents.odd.num ≤ frame.parents.odd.den := frame.valid.odd_bounds.2.2
  have hTs := parent_transform_s frame r
  have hCL := frame.parentC_mul_L
  have hCd := frame.parentC_mul_den
  have hCn := frame.parentC_mul_num
  rw [frame_periodDenominator_eq] at hCL hCd hCn ht1
  rw [hE] at hTs hCL hCd hCn
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hsp := sp_queryOne frame hE r
  have hsv := w1s_even frame r
  have hpar := sp_odd_parity frame r hr
  have hCL' := parentC_ge_L frame
  have hev2 : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨hlo, hhi⟩ := odd_pos frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num
    frame.parentC (w1s frame.child.num frame.child.den r) (w1t frame.child.num frame.child.den r)
    (w1T frame.child.num frame.child.den) (frame.parentSGrade r) (by omega) (by omega)
    (by linarith [hCL]) (by linarith [hCd]) hCL' hT (by linarith [hTs]) (by omega) (by linarith [hs2])
    ht1 ht2
  have hQodd : ¬ EvenSite (queryOne frame r) := by
    have hq := queryOne_sum frame r
    have hr' : ¬ ((r.1 + r.2) % 2 = 0) := hr
    unfold EvenSite
    omega
  have hQsp : frame.parentSGrade (queryOne frame r) = frame.parentSGrade r := hsp
  exact hStrong (queryOne frame r) hQodd (by rw [hQsp]; omega) (by rw [hQsp]; omega)

/-- **The V-side odd window, W0 (ε = −1).** `s* = s_p(r) − 2 ∈ (D+N−2, 3D+N)`, odd-parity congruent to `D + N`, so
`s* ≤ 3D + N − 2`; the parent h0 value is the named strengthened strip `hStrong`. The lower bound `s_p(r) > D + N` uses
the parity of `s` (`s ≥ L`), the lattice argument of the archive. -/
theorem odd_value_zero {frame : ChildFrame} {G : Field} (hE : frame.eps = -1)
    (hStrong : ∀ Q : Site, ¬ EvenSite Q → 2 - 3 * frame.parents.odd.den + frame.parents.odd.num ≤ frame.parentSGrade Q →
      frame.parentSGrade Q ≤ 3 * frame.parents.odd.den + frame.parents.odd.num - 2 →
      quarterTurnField G Q = harmonicGrid Q)
    (r : Site) (hr : ¬ EvenSite r)
    (ht1 : frame.child.den - frame.child.periodDenominator + 1 ≤ w1t frame.child.num frame.child.den r)
    (ht2 : w1t frame.child.num frame.child.den r ≤ frame.child.num - 2)
    (hs1 : frame.child.den + frame.child.num - 2 < w1s frame.child.num frame.child.den r)
    (hs2 : w1s frame.child.num frame.child.den r ≤ 3 * frame.child.den + frame.child.num - 2) :
    quarterTurnField G (queryZero frame r) = harmonicGrid (queryZero frame r) := by
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hD : 1 ≤ frame.parents.odd.den := by have := frame.valid.odd_bounds.1; omega
  have hN : 0 ≤ frame.parents.odd.num := frame.valid.odd_bounds.2.1
  have hNle : frame.parents.odd.num ≤ frame.parents.odd.den := frame.valid.odd_bounds.2.2
  have hTs := parent_transform_s frame r
  have hCL := frame.parentC_mul_L
  have hCd := frame.parentC_mul_den
  rw [frame_periodDenominator_eq] at hCL hCd ht1
  rw [hE] at hTs hCL hCd
  have hT : 0 < w1T frame.child.num frame.child.den := by
    rw [← frame_periodDenominator_eq]
    exact Fraction.periodDenominator_pos (frame.valid.current_interior .even).inUnitInterval
  have hsp := sp_queryZero frame hE r
  have hpar := sp_odd_parity frame r hr
  have hCL' := parentC_ge_L frame
  have hev2 : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hsv := w1s_even frame r
  obtain ⟨hlo, hhi⟩ := odd_neg frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num
    frame.parentC (w1s frame.child.num frame.child.den r) (w1t frame.child.num frame.child.den r)
    (w1T frame.child.num frame.child.den) (frame.parentSGrade r) (by omega) (by omega)
    (by linarith [hCL]) (by linarith [hCd]) hCL' hT (by linarith [hTs]) (by omega) (by linarith [hs2])
    ht1 ht2
  have hQodd : ¬ EvenSite (queryZero frame r) := by
    have hq := queryZero_sum frame r
    have hr' : ¬ ((r.1 + r.2) % 2 = 0) := hr
    unfold EvenSite
    omega
  have hQsp : frame.parentSGrade (queryZero frame r) = frame.parentSGrade r - 2 := hsp
  exact hStrong (queryZero frame r) hQodd (by rw [hQsp]; omega) (by rw [hQsp]; omega)

end FLatticePaper.W1Vside
