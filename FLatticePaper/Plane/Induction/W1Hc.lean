import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.ParentStepDischarge
import FLatticePaper.Plane.Induction.SheetRegions
import FLatticePaper.Plane.Induction.VArcOffers

/-! Task 53: the discharge of hC, the second-branch sign at the seed point (PAIR_INDUCTION, even child, `fC = 1`).

The reduced parent point is `y* = w0` (ε = 1) and `y* = w0 − U_p` (ε = −1), `U_p = 2(D, N)`. Its parent coordinate is
`s_p(y*) = (D+N) y₁ + (D−N) y₂ = 2ε − 2N` (exact, from `N d − D n = ε`). The parent field `Fp = quarterTurnField G` equals
`h0` on the conjugate's ordinary strip (`quarterTurnField_eq_harmonic`), and `h0(y*) + a_q·(z0 − lv) + c_e = 1` (a
quadratic identity with the certificate `linear_combination`). The W0 exception (D − N = 1) is kept as a named input. -/

namespace FLatticePaper.W1Hc

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds

/-- `s_p(y*) = 2 − 2N` for ε = 1 (the explicit reduced point). -/
theorem core_sp_pos (n d D N : ℤ) (hc : N * d - D * n = 1) :
    (D + N) * (D * n - 2 * D - N * d + 2 * N + d - n) +
      (D - N) * (-(D * n) + 2 * D + N * d + 2 * N - d - n) = 2 - 2 * N := by
  linear_combination (2 - 2 * N) * hc

/-- `s_p(y*) = −2 − 2N` for ε = −1 (the reduced point `w0 − U_p`). -/
theorem core_sp_neg (n d D N : ℤ) (hc : N * d - D * n = -1) :
    (D + N) * (-(D * n) - 2 * D + N * d + 2 * N + d - n) +
      (D - N) * (D * n + 2 * D - N * d + 2 * N - d - n) = -2 - 2 * N := by
  linear_combination (2 * N + 2) * hc

/-- The quadratic identity at the ε = 1 reduced point: `h0(y*) + A = 1`, `A = a_q·z0 + c_e` (W = 1, lv = 0). -/
theorem core_h0_pos (n d D N M : ℤ) (hc : N * d - D * n = 1)
    (hM : 2 * M = (d - 2 * D) ^ 2 + 2 * (d - 2 * D) * (n - 2 * N) - (n - 2 * N) ^ 2 - ((d - 2 * D) + (n - 2 * N))) :
    (D * n - 2 * D - N * d + 2 * N + d - n) ^ 2 + 2 * (D * n - 2 * D - N * d + 2 * N + d - n) *
        (-(D * n) + 2 * D + N * d + 2 * N - d - n) - (-(D * n) + 2 * D + N * d + 2 * N - d - n) ^ 2 -
        2 * (-(D * n) + 2 * D + N * d + 2 * N - d - n) =
      4 * (1 - ((n - 2 * N) * (d * (1 - D - N) - D * (2 - (d + n))) -
        (d - 2 * D) * (n * (1 - D - N) - N * (2 - (d + n))) + (M + 2))) := by
  linear_combination (2 * D * n - 2 * N * d - 4) * hc + 2 * hM

/-- The quadratic identity at the ε = −1 reduced point `y* = w0 − U_p` (W = 0, lv = U_q). -/
theorem core_h0_neg (n d D N M : ℤ) (hc : N * d - D * n = -1)
    (hM : 2 * M = (d - 2 * D) ^ 2 + 2 * (d - 2 * D) * (n - 2 * N) - (n - 2 * N) ^ 2 - ((d - 2 * D) + (n - 2 * N))) :
    (-(D * n) - 2 * D + N * d + 2 * N + d - n) ^ 2 +
        2 * (-(D * n) - 2 * D + N * d + 2 * N + d - n) * (D * n + 2 * D - N * d + 2 * N - d - n) -
        (D * n + 2 * D - N * d + 2 * N - d - n) ^ 2 - 2 * (D * n + 2 * D - N * d + 2 * N - d - n) =
      4 * (1 - ((n - 2 * N) * (d * (D + N) + D * (2 - (d + n)) - (d - 2 * D)) -
        (d - 2 * D) * (n * (D + N) + N * (2 - (d + n)) - (n - 2 * N)) + M)) := by
  linear_combination (2 * D * n - 2 * N * d - 4) * hc + 2 * hM

/-- `h0 + A = 1` from the numerator identity and an even coordinate sum. -/
theorem h0_add_eq_one (p1 p2 A : ℤ) (hsum : (p1 + p2) % 2 = 0)
    (hP : p1 ^ 2 + 2 * p1 * p2 - p2 ^ 2 - 2 * p2 = 4 * (1 - A)) :
    harmonicGrid (p1, p2) + A = 1 := by
  unfold harmonicGrid
  dsimp only
  rw [hsum, sub_zero, hP, Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]
  ring

/-- The even parent's constant `(T_q − d_q − n_q)/2` is an integer `M`. -/
theorem even_constant_exists (dq nq : ℤ) :
    ∃ M : ℤ, 2 * M = dq * dq + 2 * dq * nq - nq * nq - (dq + nq) := by
  obtain ⟨a, ha⟩ := Int.even_mul_pred_self dq
  obtain ⟨b, hb⟩ := Int.even_mul_succ_self nq
  exact ⟨a - b + dq * nq, by linear_combination (-1 : ℤ) * ha + hb⟩

theorem sheetC_split (frame : ChildFrame) (Fp : Field) (z : Site) :
    frame.sheetC Fp z = Fp (z - frame.sheetShift - frame.sheetOffset) +
      (frame.siblingSlope (z - frame.sheetShift) + frame.sheetConstant) := by
  unfold ChildFrame.sheetC
  ring

theorem sheetConstant_eq (frame : ChildFrame) (M : ℤ)
    (hM : 2 * M = frame.parents.even.den * frame.parents.even.den + 2 * frame.parents.even.den * frame.parents.even.num -
      frame.parents.even.num * frame.parents.even.num - (frame.parents.even.den + frame.parents.even.num)) :
    frame.sheetConstant = M + 2 * frame.phaseW := by
  unfold ChildFrame.sheetConstant Fraction.periodDenominator
  have h2 : frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num -
      frame.parents.even.num ^ 2 - frame.parents.even.den - frame.parents.even.num = 2 * M := by
    linear_combination (-1 : ℤ) * hM
  rw [h2, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

theorem sheetShift_one (frame : ChildFrame) (hW : frame.phaseW = 1) : frame.sheetShift = (0, 0) := by
  unfold ChildFrame.sheetShift
  rw [hW, sub_self, zero_smul]
  rfl

theorem sheetOffset_one (frame : ChildFrame) (hE : frame.eps = 1) :
    frame.sheetOffset = (frame.parents.even.num, frame.parents.even.den + 2 * frame.parents.even.num) := by
  unfold ChildFrame.sheetOffset Fraction.unmodifiedDeck
  rw [hE]
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_mk, smul_eq_mul, one_mul, Prod.fst_add]
    ring
  · simp only [Prod.smul_mk, smul_eq_mul, one_mul, Prod.snd_add]
    ring

/-- The seed point of an ε = 1 child: `z0 = (d K − D(2 − L), n K − N(2 − L))` with `K = 1 − D − N`. -/
theorem seed_point_one (frame : ChildFrame) (hE : frame.eps = 1) (hW : frame.phaseW = 1) :
    seedPoint frame = (frame.child.den * (1 - frame.parents.odd.den - frame.parents.odd.num) -
        frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)),
      frame.child.num * (1 - frame.parents.odd.den - frame.parents.odd.num) -
        frame.parents.odd.num * (2 - (frame.child.den + frame.child.num))) := by
  unfold seedPoint seedK
  rw [hE, hW]
  exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)

/-- **The second branch at the seed point, ε = 1: `C(z0) = 1`.** The reduced point is `w0 = z0 − e` (W = 1, lv = 0);
its parent coordinate is `2 − 2N`, inside the conjugate's ordinary strip, so `Fp(w0) = h0(w0)`, and the quadratic
identity gives `h0(w0) + a_q·z0 + c_e = 1`. -/
theorem hC_one {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hstrips : conj.HasStrips G)
    (hE : frame.eps = 1) :
    frame.sheetC (quarterTurnField G) (seedPoint frame) = 1 := by
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hden : frame.child.den = 2 * frame.parents.odd.den + frame.parents.even.den := ZoneI1.child_den_eq frame
  have hnum : frame.child.num = 2 * frame.parents.odd.num + frame.parents.even.num := ZoneI1.child_num_eq frame
  have hW : frame.phaseW = 1 := phaseW_pos frame hE
  have hc : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = 1 := by
    have h := frame.eps_eq
    rw [hE] at h
    linarith
  have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by omega
  have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by omega
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hconj
  have hN1 : 1 ≤ frame.parents.odd.num := by
    nlinarith [mul_nonneg hN0 hpos.le]
  obtain ⟨M, hM⟩ := even_constant_exists frame.parents.even.den frame.parents.even.num
  have hM' : 2 * M = (frame.child.den - 2 * frame.parents.odd.den) ^ 2 +
      2 * (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num - 2 * frame.parents.odd.num) -
      (frame.child.num - 2 * frame.parents.odd.num) ^ 2 -
      ((frame.child.den - 2 * frame.parents.odd.den) + (frame.child.num - 2 * frame.parents.odd.num)) := by
    rw [hdq, hnq] at hM
    linear_combination hM
  have hw0 : seedPoint frame - frame.sheetShift - frame.sheetOffset =
      (frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den +
        2 * frame.parents.odd.num + frame.child.den - frame.child.num,
       -(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den +
        2 * frame.parents.odd.num - frame.child.den - frame.child.num) := by
    rw [seed_point_one frame hE hW, sheetShift_one frame hW, sheetOffset_one frame hE]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub, hnq]
      ring
    · simp only [Prod.snd_sub, hdq, hnq]
      ring
  have hsum : ((frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (-(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) % 2 = 0 := by
    rw [show (frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (-(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) = 2 * (2 * frame.parents.odd.num - frame.child.num) by ring]
    omega
  have hsp := core_sp_pos frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num hc
  have hstrip : quarterTurnField G ((frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (-(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) = harmonicGrid ((frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (-(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) := by
    apply quarterTurnField_eq_harmonic hstrips
    · rw [quarterTurn_site]
      unfold ChildFrame.tGrade
      dsimp only
      rw [hcn, hcd]
      linarith
    · rw [quarterTurn_site]
      unfold ChildFrame.tGrade
      dsimp only
      rw [hcn, hcd]
      linarith
  have hP := core_h0_pos frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num M hc hM'
  have hval := h0_add_eq_one (frame.parents.odd.den * frame.child.num - 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) (-(frame.parents.odd.den * frame.child.num) + 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (1 - frame.parents.odd.den - frame.parents.odd.num) - frame.parents.odd.den * (2 - (frame.child.den + frame.child.num))) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (1 - frame.parents.odd.den - frame.parents.odd.num) - frame.parents.odd.num * (2 - (frame.child.den + frame.child.num))) + (M + 2)) hsum hP
  have hA : frame.siblingSlope (seedPoint frame - frame.sheetShift) + frame.sheetConstant = ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (1 - frame.parents.odd.den - frame.parents.odd.num) - frame.parents.odd.den * (2 - (frame.child.den + frame.child.num))) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (1 - frame.parents.odd.den - frame.parents.odd.num) - frame.parents.odd.num * (2 - (frame.child.den + frame.child.num))) + (M + 2)) := by
    rw [sheetConstant_eq frame M hM, hW]
    unfold ChildFrame.siblingSlope
    rw [seed_point_one frame hE hW, sheetShift_one frame hW]
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hdq, hnq]
    ring
  rw [sheetC_split, hw0, hstrip, hA]
  exact hval

theorem sheetShift_zero (frame : ChildFrame) (hW : frame.phaseW = 0) :
    frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
  unfold ChildFrame.sheetShift Fraction.unmodifiedDeck
  rw [hW, sub_zero, one_smul]

theorem sheetOffset_neg (frame : ChildFrame) (hE : frame.eps = -1) :
    frame.sheetOffset = (frame.parents.even.num - 2 * frame.parents.even.den, frame.parents.even.den) := by
  unfold ChildFrame.sheetOffset Fraction.unmodifiedDeck
  rw [hE]
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.fst_add]
    ring
  · simp only [Prod.smul_mk, smul_eq_mul, Prod.snd_add]
    ring

/-- The seed point of an ε = −1 child (W = 0): `z0 = (d(D+N) + D(2−L), n(D+N) + N(2−L))`. -/
theorem seed_point_neg (frame : ChildFrame) (hE : frame.eps = -1) (hW : frame.phaseW = 0) :
    seedPoint frame = (frame.child.den * (frame.parents.odd.den + frame.parents.odd.num) +
        frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)),
      frame.child.num * (frame.parents.odd.den + frame.parents.odd.num) +
        frame.parents.odd.num * (2 - (frame.child.den + frame.child.num))) := by
  unfold seedPoint seedK
  rw [hE, hW]
  exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)

/-- **The ε = −1 second branch: `C(z0) = Fp(y*) + A`.** The query `w0 = y* + U_p` (W = 0, `lv = U_q`, `e = −U_q + V_q`);
`Fp(w0) = Fp(y*)` by the zero-character period `U_p` (`quarterTurnField_add_mul_up`). -/
theorem sheetC_neg_eq {frame conj : ChildFrame} {G : Field} {M : ℤ}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hE : frame.eps = -1) (hM : 2 * M = frame.parents.even.den * frame.parents.even.den +
      2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num * frame.parents.even.num -
      (frame.parents.even.den + frame.parents.even.num)) :
    frame.sheetC (quarterTurnField G) (seedPoint frame) =
      quarterTurnField G ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) + ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)) - (frame.child.den - 2 * frame.parents.odd.den)) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.num * (2 - (frame.child.den + frame.child.num)) - (frame.child.num - 2 * frame.parents.odd.num)) + M) := by
  have hW : frame.phaseW = 0 := phaseW_neg frame hE
  have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by
    have := ZoneI1.child_den_eq frame
    omega
  have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by
    have := ZoneI1.child_num_eq frame
    omega
  have hw0 : seedPoint frame - frame.sheetShift - frame.sheetOffset =
      ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) + (1 * (2 * frame.parents.odd.den), 1 * (2 * frame.parents.odd.num)) := by
    rw [seed_point_neg frame hE hW, sheetShift_zero frame hW, sheetOffset_neg frame hE]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub, Prod.fst_add, hdq, hnq]
      ring
    · simp only [Prod.snd_sub, Prod.snd_add, hdq, hnq]
      ring
  have hA : frame.siblingSlope (seedPoint frame - frame.sheetShift) + frame.sheetConstant = ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)) - (frame.child.den - 2 * frame.parents.odd.den)) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.num * (2 - (frame.child.den + frame.child.num)) - (frame.child.num - 2 * frame.parents.odd.num)) + M) := by
    rw [sheetConstant_eq frame M hM, hW]
    unfold ChildFrame.siblingSlope
    rw [seed_point_neg frame hE hW, sheetShift_zero frame hW]
    simp only [Prod.fst_sub, Prod.snd_sub, hdq, hnq]
    ring
  rw [sheetC_split, hw0, quarterTurnField_add_mul_up hconj hper 1, hA]

/-- **hC, ε = −1, non-exceptional (`D − N ≥ 2`): `C(z0) = 1`.** The reduced point `y*` has `s_p = −2 − 2N`, inside the
conjugate's strip (`t_c(Z y*) = D + 3N + 2 ≤ 3D + N − 1`), so `Fp(y*) = h0(y*)` and `h0(y*) + A = 1`. -/
theorem hC_neg_one {frame conj : ChildFrame} {G : Field} {M : ℤ}
    (hconj : conj.child = frame.parents.odd.rotate) (hstrips : conj.HasStrips G)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hE : frame.eps = -1) (hNE : 2 ≤ frame.parents.odd.den - frame.parents.odd.num)
    (hM : 2 * M = frame.parents.even.den * frame.parents.even.den +
      2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num * frame.parents.even.num -
      (frame.parents.even.den + frame.parents.even.num)) :
    frame.sheetC (quarterTurnField G) (seedPoint frame) = 1 := by
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := frame.child_facts
  have hc : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
    have h := frame.eps_eq
    rw [hE] at h
    linarith
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hconj
  have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by
    have := ZoneI1.child_den_eq frame
    omega
  have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by
    have := ZoneI1.child_num_eq frame
    omega
  have hM' : 2 * M = (frame.child.den - 2 * frame.parents.odd.den) ^ 2 +
      2 * (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num - 2 * frame.parents.odd.num) -
      (frame.child.num - 2 * frame.parents.odd.num) ^ 2 -
      ((frame.child.den - 2 * frame.parents.odd.den) + (frame.child.num - 2 * frame.parents.odd.num)) := by
    rw [hdq, hnq] at hM
    linear_combination hM
  rw [sheetC_neg_eq hconj hper hE hM]
  have hsp := core_sp_neg frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num hc
  have hstrip : quarterTurnField G ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) = harmonicGrid ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) := by
    apply quarterTurnField_eq_harmonic hstrips
    · rw [quarterTurn_site]
      unfold ChildFrame.tGrade
      dsimp only
      rw [hcn, hcd]
      linarith
    · rw [quarterTurn_site]
      unfold ChildFrame.tGrade
      dsimp only
      rw [hcn, hcd]
      linarith
  have hsum : ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) % 2 = 0 := by
    rw [show (-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) = 2 * (2 * frame.parents.odd.num - frame.child.num) by ring]
    omega
  have hP := core_h0_neg frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num M hc hM'
  have hval := h0_add_eq_one (-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)) - (frame.child.den - 2 * frame.parents.odd.den)) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.num * (2 - (frame.child.den + frame.child.num)) - (frame.child.num - 2 * frame.parents.odd.num)) + M) hsum hP
  rw [hstrip]
  exact hval


/-- **hC, ε = −1, exceptional (`D − N = 1`), given the base value.** The reduced point is `y*` with `s_p(y*) = −2D`, one row
below the conjugate's strip; its value `Fp(y*) = h0(y*) − 1` is the pure-run value `G = −1` (PAIR_INDUCTION, W0 exception;
the conjugate is `replicate (D − 2) three`, base value named as `hExc`). Then `C(z0) = 0`. -/
theorem hC_neg_exc {frame conj : ChildFrame} {G : Field} {M : ℤ}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hper : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hE : frame.eps = -1)
    (hM : 2 * M = frame.parents.even.den * frame.parents.even.den +
      2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num * frame.parents.even.num -
      (frame.parents.even.den + frame.parents.even.num))
    (hExc : quarterTurnField G ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) = harmonicGrid ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num), (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) - 1) :
    frame.sheetC (quarterTurnField G) (seedPoint frame) = 0 := by
  have hc : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
    have h := frame.eps_eq
    rw [hE] at h
    linarith
  have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by
    have := ZoneI1.child_den_eq frame
    omega
  have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by
    have := ZoneI1.child_num_eq frame
    omega
  have hM' : 2 * M = (frame.child.den - 2 * frame.parents.odd.den) ^ 2 +
      2 * (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num - 2 * frame.parents.odd.num) -
      (frame.child.num - 2 * frame.parents.odd.num) ^ 2 -
      ((frame.child.den - 2 * frame.parents.odd.den) + (frame.child.num - 2 * frame.parents.odd.num)) := by
    rw [hdq, hnq] at hM
    linear_combination hM
  rw [sheetC_neg_eq hconj hper hE hM, hExc]
  have hsum : ((-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num)) % 2 = 0 := by
    rw [show (-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) + (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) = 2 * (2 * frame.parents.odd.num - frame.child.num) by ring]
    omega
  have hP := core_h0_neg frame.child.num frame.child.den frame.parents.odd.den frame.parents.odd.num M hc hM'
  have hval := h0_add_eq_one (-(frame.parents.odd.den * frame.child.num) - 2 * frame.parents.odd.den + frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num + frame.child.den - frame.child.num) (frame.parents.odd.den * frame.child.num + 2 * frame.parents.odd.den - frame.parents.odd.num * frame.child.den + 2 * frame.parents.odd.num - frame.child.den - frame.child.num) ((frame.child.num - 2 * frame.parents.odd.num) * (frame.child.den * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.den * (2 - (frame.child.den + frame.child.num)) - (frame.child.den - 2 * frame.parents.odd.den)) - (frame.child.den - 2 * frame.parents.odd.den) * (frame.child.num * (frame.parents.odd.den + frame.parents.odd.num) + frame.parents.odd.num * (2 - (frame.child.den + frame.child.num)) - (frame.child.num - 2 * frame.parents.odd.num)) + M) hsum hP
  linarith

/-- **hC from the packet of the conjugate (task 53).** For a proper word `w` the second-branch sign at the seed point
holds: `C(z0) = 1` (ε = 1; ε = −1 with `D − N ≥ 2`) and `C(z0) = 0` (the W0 exception `D − N = 1`, base value `hExc`). -/
theorem hC_of_packet {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hpk : (frameAt (conjWord w)).Packet (standardField (conjWord w)))
    (hExc : (frameAt w).eps = -1 → (frameAt w).parents.odd.den - (frameAt w).parents.odd.num = 1 →
      quarterTurnField (standardField (conjWord w)) ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) = harmonicGrid ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) - 1) :
    0 ≤ (frameAt w).sheetC (quarterTurnField (standardField (conjWord w))) (seedPoint (frameAt w)) := by
  have hconj : (frameAt (conjWord w)).child = (frameAt w).parents.odd.rotate := frameAt_conj_child hproper
  have hstr := hpk.strips
  have hper := hpk.periods
  obtain ⟨hDpos, hN0, hNle⟩ := (frameAt w).valid.odd_bounds
  obtain ⟨hpos, hnlt, hdn, hd3, -⟩ := (frameAt w).child_facts
  rcases (frameAt w).eps_unit with h | h
  · rw [hC_one hconj hstr h]
    norm_num
  · obtain ⟨M, hM⟩ := even_constant_exists (frameAt w).parents.even.den (frameAt w).parents.even.num
    by_cases hX : (frameAt w).parents.odd.den - (frameAt w).parents.odd.num = 1
    · rw [show (frameAt w).sheetC _ _ = 0 from hC_neg_exc hconj hper h hM (hExc h hX)]
    · have hc : (frameAt w).parents.odd.num * (frameAt w).child.den - (frameAt w).parents.odd.den * (frameAt w).child.num = -1 := by
        have hh := (frameAt w).eps_eq
        rw [h] at hh
        linarith
      have hNE : 2 ≤ (frameAt w).parents.odd.den - (frameAt w).parents.odd.num := by
        by_contra hlt
        have hle : (frameAt w).parents.odd.den - (frameAt w).parents.odd.num ≤ 1 := by omega
        have hge : 0 ≤ (frameAt w).parents.odd.den - (frameAt w).parents.odd.num := by omega
        have hcase : (frameAt w).parents.odd.den - (frameAt w).parents.odd.num = 0 := by omega
        have hNeq : (frameAt w).parents.odd.num = (frameAt w).parents.odd.den := by omega
        rw [hNeq] at hc
        nlinarith
      rw [show (frameAt w).sheetC _ _ = 1 from hC_neg_one hconj hstr hper h hNE hM]
      norm_num

/-- **The even seed from the packet, with hC discharged (task 53).** Only the W0 exception value `hExc` stays named. -/
theorem even_zero_of_packet_hc {w : Word} (hproper : ∃ x ∈ w, x ≠ Digit.three)
    (hpar : SeedFields (conjWord w))
    (hconj : (frameAt (conjWord w)).Packet (standardField (conjWord w)))
    (hO : OpenInputs w)
    (hExc : (frameAt w).eps = -1 → (frameAt w).parents.odd.den - (frameAt w).parents.odd.num = 1 →
      quarterTurnField (standardField (conjWord w)) ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) = harmonicGrid ((-((frameAt w).parents.odd.den * (frameAt w).child.num) - 2 * (frameAt w).parents.odd.den + (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num + (frameAt w).child.den - (frameAt w).child.num), ((frameAt w).parents.odd.den * (frameAt w).child.num + 2 * (frameAt w).parents.odd.den - (frameAt w).parents.odd.num * (frameAt w).child.den + 2 * (frameAt w).parents.odd.num - (frameAt w).child.den - (frameAt w).child.num)) - 1) :
    ∀ z : Site, EvenSite z →
      (frameAt w).tGrade z = 2 - ((frameAt w).child.den + (frameAt w).child.num) → standardField w z = 0 :=
  even_zero_of_packet hproper hpar hconj hO (hC_of_packet hproper hconj hExc)

end FLatticePaper.W1Hc
