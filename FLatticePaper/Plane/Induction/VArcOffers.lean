import FLatticePaper.Plane.Induction.VArcLongitudinal
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.SheetRegions
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.StrongEstimates

/-! Task 56 (Q2, the offers of the longitudinal exits), derived from the conjugate packet.

The offers of `LongitudinalOffers` are statements about the sheets `A`, `C` of `Fp = quarterTurnField G` at `v + X`, where
`G = standardField (conjWord word)` is the earlier field. The derivation uses only the packet of the earlier word:

* the period `U_p ↦ T_e` of the quarter turn (the earlier child's transverse vector is `Z(U_p)`): `Fp` is `U_p`-periodic
  (`quarterTurnField_add_up`), since the constant `cV_e = −D − B` of the earlier child matches the harmonic shift;
* the sheet facts of `sheetFacts_of_conjPacket` (zero strip of `A`, harmonic identity on the active sheet).

This file proves the first offer for `W = 0`, with the periodicity. -/

namespace FLatticePaper.Induction
open Farey

/-- The quarter turn `Z(x) = (−x₂, x₁ − 1)` of the field's argument. -/
theorem mapSite_quarterTurn_eq (x : Site) :
    QuarterTurn.counterclockwise.mapSite (0, -1) x = (-x.2, x.1 - 1) := by
  ext <;> simp [QuarterTurn.mapSite, QuarterTurn.turn, sub_eq_add_neg]

/-- The harmonic grid along the even vector `(2D, 2N)`: `h(w + (2D, 2N)) = h(w) + s_p(w) + (B − N)`, with
`s_p(w) = (D + N) w₁ + (D − N) w₂` and `B = D² + 2DN − N²`. -/
theorem harmonicGrid_add_two (D N : ℤ) (w : Site) :
    harmonicGrid (w + (2 * D, 2 * N)) =
      harmonicGrid w + ((D + N) * w.1 + (D - N) * w.2 + (D ^ 2 + 2 * D * N - N ^ 2 - N)) := by
  obtain ⟨x1, x2⟩ := w
  unfold harmonicGrid
  simp only [Prod.fst_add, Prod.snd_add]
  have hp : (x1 + 2 * D + (x2 + 2 * N)) % 2 = (x1 + x2) % 2 := by omega
  rw [hp]
  have key : (x1 + 2 * D) ^ 2 + 2 * (x1 + 2 * D) * (x2 + 2 * N) - (x2 + 2 * N) ^ 2 - 2 * (x2 + 2 * N) - (x1 + x2) % 2
      = (x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2)
        + 4 * ((D + N) * x1 + (D - N) * x2 + (D ^ 2 + 2 * D * N - N ^ 2 - N)) := by ring
  rw [key]
  generalize x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2 - 2 * x2 - (x1 + x2) % 2 = X
  generalize (D + N) * x1 + (D - N) * x2 + (D ^ 2 + 2 * D * N - N ^ 2 - N) = Y
  omega

/-- The odd parent `N / D` of the current word reads the earlier child: `num = D − N`, `den = D + N`. -/
theorem conj_child_num_den {frame conj : ChildFrame} (hconj : conj.child = frame.parents.odd.rotate) :
    conj.child.num = frame.parents.odd.den - frame.parents.odd.num ∧
      conj.child.den = frame.parents.odd.den + frame.parents.odd.num := by
  rw [hconj, Fraction.rotate_of_odd frame.valid.odd_parity]
  exact ⟨rfl, rfl⟩

/-- The periodicity of the quarter-turned earlier field along `(2D, 2N)`: the earlier child's transverse period, with the
constant `cV_e = −D − B` (from `coherentConstantV_eq`, the earlier period `2B`), cancels the harmonic shift. -/
theorem quarterTurnField_add_two {conj : ChildFrame} {G : Field}
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    {D N : ℤ} (hnum : conj.child.num = D - N) (hden : conj.child.den = D + N) (w : Site) :
    quarterTurnField G (w + (2 * D, 2 * N)) = quarterTurnField G w := by
  have hcV := conj.coherentConstantV_eq
  have hPer : conj.child.periodDenominator = 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hnum, hden]
    ring
  rw [hnum, hden, hPer] at hcV
  have hcV' : conj.coherentConstantV = -D - (D ^ 2 + 2 * D * N - N ^ 2) := by linarith
  have hTr : conj.child.modifiedDeck.transverse = (-2 * N, 2 * D) := by
    rw [conj.child_modifiedDeck_transverse, hnum, hden]
    congr 1 <;> ring
  have hZ : QuarterTurn.counterclockwise.mapSite (0, -1) (w + (2 * D, 2 * N)) =
      QuarterTurn.counterclockwise.mapSite (0, -1) w + conj.child.modifiedDeck.transverse := by
    rw [mapSite_quarterTurn_eq, mapSite_quarterTurn_eq, hTr]
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  unfold quarterTurnField
  rw [hZ, hG.2, harmonicGrid_add_two, mapSite_quarterTurn_eq]
  unfold Fraction.transverseGrade
  rw [hden, hnum, hcV']
  ring

/-- The first offer for `W = 0`: the sheet `A` at `v + U_p` is `Fp(v − U_q)` (periodicity), which is at least the sheet
minimum `h(v)` (the harmonic strip), since `A(v) = Fp(v − U_q)` is one of the two sheets of the minimum. -/
theorem first_offer_of_phase_zero {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hS : frame.StripInputs (frame.sheetMin (quarterTurnField G)))
    (hW : frame.phaseW = 0) {v : Site} (hv : v ∈ frame.closedPolygon)
    (hs : frame.sGrade v ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    harmonicGrid v ≤ frame.sheetA (quarterTurnField G) (v + frame.offsetX) := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hX : frame.offsetX = (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := frame.offsetX_of_W0 hW
  have hsh : frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
    ext <;> simp [ChildFrame.sheetShift, Fraction.unmodifiedDeck, hW]
  have hA : frame.sheetMin (quarterTurnField G) v ≤ frame.sheetA (quarterTurnField G) v := by
    unfold ChildFrame.sheetMin
    exact min_le_left _ _
  rw [← hS.harmonic v hv hs, hX]
  unfold ChildFrame.sheetA at hA ⊢
  rw [hsh] at hA ⊢
  have e : v + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) - (frame.parents.even.den, frame.parents.even.num) =
      (v - (frame.parents.even.den, frame.parents.even.num)) + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
    abel
  rw [e, quarterTurnField_add_two hG hnum hden]
  exact hA


/-- The sharp inequality of the parent: `(K + 2)(d + n − 2) < (D + N) T` for `N d = D n + 1` (checked on the lattice and
proved for all parameters of the Farey relations). -/
theorem splus_ineq (N D n d : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2 * N ≤ n) (h2D : 2 * D ≤ d)
    (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hrel : N * d = D * n + 1) :
    ((D * (d + n) + N * (d - n)) + 2) * (d + n - 2) < (D + N) * (d ^ 2 + 2 * d * n - n ^ 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 h2D), mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 hND),
    mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 hnd), mul_nonneg (sub_nonneg.2 h2D) (sub_nonneg.2 hnd),
    mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 hn), mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 h2N)]

/-- The sheet shift `(1 − W)·U_q` vanishes for `W = 1`: the sheet `A` is `Fp` itself. -/
theorem sheetShift_of_phase_one {frame : ChildFrame} (hW : frame.phaseW = 1) : frame.sheetShift = 0 := by
  ext <;> simp [ChildFrame.sheetShift, Fraction.unmodifiedDeck, hW]

/-- The parent zero strip, in the parent transverse grade `t_p(x) = N x₁ − D x₂`: `Fp x = 0` for `1 − D ≤ t_p(x) ≤ N + 2D − 1`
(the strip of the earlier child, transported by the quarter turn: `s_e(Zx) = 2 t_p(x) − 2N`). -/
theorem quarterTurnField_zero_of_tp {conj : ChildFrame} {G : Field} (hStrips : conj.HasStrips G)
    {N D : ℤ} (hnum : conj.child.num = D - N) (hden : conj.child.den = D + N) {x : Site}
    (hlo : 1 - D ≤ N * x.1 - D * x.2) (hhi : N * x.1 - D * x.2 ≤ N + 2 * D - 1) :
    quarterTurnField G x = 0 := by
  have e : conj.sGrade (QuarterTurn.counterclockwise.mapSite (0, -1) x) = 2 * (N * x.1 - D * x.2) - 2 * N := by
    rw [mapSite_quarterTurn_eq]
    unfold ChildFrame.sGrade
    dsimp only
    rw [hnum, hden]
    ring
  apply quarterTurnField_eq_zero hStrips
  · rw [e, hden]
    linarith
  · rw [e, hden, hnum]
    linarith

/-- `s ≤ d + n − 2` on the longitudinal range: the grade `s` is even, and `d + n` is even. -/
theorem sGrade_le_pred (frame : ChildFrame) {z : Site} (hs : frame.sGrade z ≤ frame.child.den + frame.child.num - 1) :
    frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
  have h2 : frame.sGrade z % 2 = 0 := frame.sGrade_mod_two z
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  omega

/-- `t ≤ d + n − 2` on the closed polygon, for `n ≥ 2` (the even bound is `d + n − 2`, the odd bound `d`). -/
theorem tGrade_le_pred (frame : ChildFrame) {z : Site} (hz : z ∈ frame.closedPolygon) (hn : 2 ≤ frame.child.num) :
    frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
  have h := hz
  unfold ChildFrame.closedPolygon at h
  simp only [Set.mem_setOf_eq] at h
  split_ifs at h
  · omega
  · omega

/-- The parent identity `T · t_p(z) = ε s(z) + K t(z)` with `K = D(d + n) + N(d − n)` (`ε = N d − D n`). -/
theorem tp_identity (frame : ChildFrame) (z : Site) :
    frame.child.periodDenominator * (frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2) =
      frame.eps * frame.sGrade z +
        (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.tGrade z := by
  have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hε : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num := frame.eps_eq
  rw [hPD]
  unfold ChildFrame.sGrade ChildFrame.tGrade
  linear_combination (-((frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2)) * hε

/-- The longitudinal bound on the parent transverse grade: with `ε = 1`, `t_p(z) < D + N` on the closed polygon where
`s(z) ≤ d + n − 1`. -/
theorem tp_lt_of_mem (frame : ChildFrame) (hε : frame.eps = 1) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hs : frame.sGrade z ≤ frame.child.den + frame.child.num - 1) :
    frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2 < frame.parents.odd.den + frame.parents.odd.num := by
  obtain ⟨hnpos, hnd, hdiff, hd3, hTdef⟩ := frame.child_facts
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hN1 : 1 ≤ frame.parents.odd.num := by omega
  have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
  have hn2 : 2 * frame.parents.odd.num ≤ frame.child.num := by
    have := frame.child_num_eq
    omega
  have hd2 : 2 * frame.parents.odd.den ≤ frame.child.den := by
    have := frame.child_den_eq
    omega
  have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num + 1 := by
    have h := frame.eps_eq
    rw [hε] at h
    linarith
  have hT : 0 < frame.child.periodDenominator := by
    have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
      unfold Fraction.periodDenominator
      ring
    rw [hPD]
    nlinarith
  have hid := tp_identity frame z
  rw [hε, one_mul] at hid
  have hsle := sGrade_le_pred frame hs
  have htle := tGrade_le_pred frame hz (by omega)
  have hK : 0 ≤ frame.parents.odd.den * (frame.child.den + frame.child.num)
      + frame.parents.odd.num * (frame.child.den - frame.child.num) := by
    nlinarith
  have hsp := splus_ineq frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    hN1 hND hn2 hd2 (by omega) (by omega) hrel
  have hKt := mul_le_mul_of_nonneg_left htle hK
  have hstep : frame.child.periodDenominator * (frame.parents.odd.num * z.1 - frame.parents.odd.den * z.2) <
      frame.child.periodDenominator * (frame.parents.odd.den + frame.parents.odd.num) := by
    rw [hid]
    have hd0 : 0 ≤ frame.child.den + frame.child.num - 2 := by omega
    nlinarith
  exact lt_of_mul_lt_mul_left hstep hT.le


/-- The first offer for `W = 1`: `h(v) ≤ A(v + U_q) = Fp(v + U_q)`. The sheet minimum gives `h(v) ≤ Fp(v)`; the step
`Fp(v + U_q) ≥ Fp(v)` is `ParentStepSign` (named) when `t_p(v) + 1 < N`, and otherwise both values lie in the parent zero
strip, where `Fp = 0`. -/
theorem first_offer_of_phase_one {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hStrips : conj.HasStrips G)
    (hS : frame.StripInputs (frame.sheetMin (quarterTurnField G)))
    (hPSS : ParentStepSign frame (quarterTurnField G))
    (hW : frame.phaseW = 1) (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    {v : Site} (hv : v ∈ frame.closedPolygon)
    (hs : frame.sGrade v ≤ frame.child.den + frame.child.num - 1) :
    harmonicGrid v ≤ frame.sheetA (quarterTurnField G) (v + frame.offsetX) := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hε : frame.eps = 1 := by
    rcases frame.eps_unit with h | h
    · exact h
    · unfold ChildFrame.phaseW at hW
      rw [h] at hW
      norm_num at hW
  obtain ⟨hnpos, hnd, -, -, -⟩ := frame.child_facts
  have hdn : 0 ≤ frame.child.den + frame.child.num := by omega
  have hN1 : 1 ≤ frame.parents.odd.num := by omega
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by
    obtain ⟨-, -, hNle⟩ := frame.valid.odd_bounds
    omega
  have hDpos : 2 ≤ frame.parents.odd.den := by omega
  have hX : frame.offsetX = (frame.parents.even.den, frame.parents.even.num) := frame.offsetX_of_W1 hW
  have hA : frame.sheetMin (quarterTurnField G) v ≤ frame.sheetA (quarterTurnField G) v := by
    unfold ChildFrame.sheetMin
    exact min_le_left _ _
  rw [← hS.harmonic v hv (by omega), hX]
  unfold ChildFrame.sheetA at hA ⊢
  rw [sheetShift_of_phase_one hW, sub_zero] at hA ⊢
  set x : Site := v + (frame.parents.even.den, frame.parents.even.num) with hx
  have hEv : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  have hpar : (x.1 + x.2) % 2 = (v.1 + v.2) % 2 := by
    rw [hx]
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hE : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den :=
    rfl
  have h1 : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = 1 := by
    rw [← hE, hε]
  have hshift : frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 =
      (frame.parents.odd.num * v.1 - frame.parents.odd.den * v.2) + 1 := by
    rw [hx]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination h1
  have hzv := tp_lt_of_mem frame hε hv hN hn hs
  by_cases hk : frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 < frame.parents.odd.num
  · exact le_trans hA ((hPSS x v hpar hshift).1 hk)
  · replace hk := not_lt.mp hk
    have hzv' : frame.parents.odd.num * v.1 - frame.parents.odd.den * v.2 + 1 ≤
        frame.parents.odd.den + frame.parents.odd.num := Int.add_one_le_iff.mpr hzv
    have hvlo : 1 - frame.parents.odd.den ≤ frame.parents.odd.num * v.1 - frame.parents.odd.den * v.2 := by
      linarith
    have hvhi : frame.parents.odd.num * v.1 - frame.parents.odd.den * v.2 ≤
        frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
      linarith
    have hxlo : 1 - frame.parents.odd.den ≤ frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 := by
      linarith
    have hxhi : frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2 ≤
        frame.parents.odd.num + 2 * frame.parents.odd.den - 1 := by
      linarith
    have hx0 := quarterTurnField_zero_of_tp hStrips hnum hden hvlo hvhi
    have hx1 := quarterTurnField_zero_of_tp hStrips hnum hden hxlo hxhi
    rw [hx0] at hA
    rw [hx1]
    exact hA


/-- The sharp inequality of the parent for `ε = −1` (`N d = D n − 1`): `−(b + 1) T < K (2 − (d − n)) − 2 (d + n − 2)`. -/
theorem sminus_ineq (N D n d : ℤ) (hN1 : 1 ≤ N) (hND : N + 1 ≤ D) (h2N : 2 * N ≤ n) (h2D : 2 * D ≤ d)
    (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hrel : N * d = D * n - 1) :
    -((D - N) + 1) * (d ^ 2 + 2 * d * n - n ^ 2) < (D * (d + n) + N * (d - n)) * (2 - (d - n)) - 2 * (d + n - 2) := by
  nlinarith [mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 h2D), mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 hND),
    mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 hnd), mul_nonneg (sub_nonneg.2 h2D) (sub_nonneg.2 hnd),
    mul_nonneg (sub_nonneg.2 h2N) (sub_nonneg.2 hn), mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 h2N)]

/-- The sheet shift `(1 − W) U_q` for `W = 0` is `U_q`, the offset `e = V_q + ε U_q`; the transverse vector of the
even parent is `V_q = (n_q − d_q, n_q + d_q)` and its kernel `U_q = (d_q, n_q)`. -/
theorem sp_identity (frame : ChildFrame) (z : Site) :
    frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2) =
      (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.sGrade z +
        2 * frame.eps * frame.tGrade z := by
  have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hε : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num := frame.eps_eq
  rw [hPD]
  unfold ChildFrame.sGrade ChildFrame.tGrade
  linear_combination (-(2 * (frame.child.num * z.1 - frame.child.den * z.2))) * hε

/-- The parent `s`-grade `s_p(z) = (D + N) z₁ + (D − N) z₂` for `ε = 1`: `1 − 2D ≤ s_p(z) ≤ r − 1` on the longitudinal range. -/
theorem sp_window_plus (frame : ChildFrame) (hε : frame.eps = 1) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hs : frame.sGrade z ≤ frame.child.den + frame.child.num - 1) :
    1 - 2 * frame.parents.odd.den ≤ (frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2 ∧
      (frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2 ≤ frame.parents.odd.den + frame.parents.odd.num - 1 := by
  obtain ⟨hnpos, -, hdiff, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hN1 : 1 ≤ frame.parents.odd.num := by omega
  have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
  have hn2 : 2 * frame.parents.odd.num ≤ frame.child.num := by
    have := frame.child_num_eq
    omega
  have hd2 : 2 * frame.parents.odd.den ≤ frame.child.den := by
    have := frame.child_den_eq
    omega
  have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num + 1 := by
    have h := frame.eps_eq
    rw [hε] at h
    linarith
  have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hT : 0 < frame.child.periodDenominator := by
    rw [hPD]
    nlinarith
  have hid : frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * z.2) =
      (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.sGrade z +
        2 * frame.tGrade z := by
    have h := sp_identity frame z
    rw [hε] at h
    linarith
  have hsle := sGrade_le_pred frame hs
  have htle := tGrade_le_pred frame hz (by omega)
  have hK : 0 ≤ frame.parents.odd.den * (frame.child.den + frame.child.num)
      + frame.parents.odd.num * (frame.child.den - frame.child.num) := by
    nlinarith
  have hsp := splus_ineq frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    hN1 hND hn2 hd2 hn hnd hrel
  have hKt := mul_le_mul_of_nonneg_left htle hK
  have hup : (frame.parents.odd.den + frame.parents.odd.num) * z.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * z.2 < frame.parents.odd.den + frame.parents.odd.num := by
    have hstep : frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2) <
        frame.child.periodDenominator * (frame.parents.odd.den + frame.parents.odd.num) := by
      rw [hid]
      have hd0 : 0 ≤ frame.child.den + frame.child.num - 2 := by omega
      nlinarith
    exact lt_of_mul_lt_mul_left hstep hT.le
  have hE : (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧
      0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∨
      (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hlow := sr_core_low_harm1 frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    frame.child.periodDenominator (frame.tGrade z) (frame.sGrade z) hN1 hND hn2 hd2 (by omega) hnd (by omega) hrel hPD hE
  have hlt : frame.child.periodDenominator * (-2 * frame.parents.odd.den) <
      frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2) := by
    have e1 : frame.child.periodDenominator * (-2 * frame.parents.odd.den) =
        -(2 * frame.parents.odd.den * frame.child.periodDenominator) := by ring
    rw [e1, hid]
    linarith
  have hlow' := Int.add_one_le_iff.mpr (lt_of_mul_lt_mul_left hlt hT.le)
  exact ⟨by linarith, by linarith [Int.add_one_le_iff.mpr hup]⟩


/-- The sibling identity of `sr_core_up_C` for `N d = D n − 1`: with `n_q = n − 2N`, `d_q = d − 2D`, the constant of the sibling
terms is `−2 T` (the numerator of the `C`-sheet upper bound). -/
theorem sib_identity (N D n d : ℤ) (hrel : N * d = D * n - 1) :
    2 * (n * ((n - 2 * N) - (d - 2 * D)) - d * ((n - 2 * N) + (d - 2 * D))) -
        (D * (d + n) + N * (d - n)) * ((d + n) * ((n - 2 * N) - (d - 2 * D)) + (d - n) * ((n - 2 * N) + (d - 2 * D)))
      = -2 * (d ^ 2 + 2 * d * n - n ^ 2) := by
  linear_combination (4 * (D * (d + n) + N * (d - n))) * hrel

/-- The parent `s`-grade for `ε = −1`: `−b ≤ s_p(z) ≤ 2r + 1` on the longitudinal range. -/
theorem sp_window_minus (frame : ChildFrame) (hε : frame.eps = -1) {z : Site} (hz : z ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hsl : 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hs : frame.sGrade z ≤ frame.child.den + frame.child.num - 1) :
    -(frame.parents.odd.den - frame.parents.odd.num) ≤
        (frame.parents.odd.den + frame.parents.odd.num) * z.1 + (frame.parents.odd.den - frame.parents.odd.num) * z.2 ∧
      (frame.parents.odd.den + frame.parents.odd.num) * z.1 + (frame.parents.odd.den - frame.parents.odd.num) * z.2 ≤
        2 * (frame.parents.odd.den + frame.parents.odd.num) + 1 := by
  obtain ⟨hnpos, -, hdiff, -, -⟩ := frame.child_facts
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
  have hN1 : 1 ≤ frame.parents.odd.num := by omega
  have hND : frame.parents.odd.num + 1 ≤ frame.parents.odd.den := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hn2 : 2 * frame.parents.odd.num ≤ frame.child.num := by
    have := frame.child_num_eq
    omega
  have hd2 : 2 * frame.parents.odd.den ≤ frame.child.den := by
    have := frame.child_den_eq
    omega
  have hrel : frame.parents.odd.num * frame.child.den = frame.parents.odd.den * frame.child.num - 1 := by
    have h := frame.eps_eq
    rw [hε] at h
    linarith
  have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hT : 0 < frame.child.periodDenominator := by
    rw [hPD]
    nlinarith
  have hid : frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * z.2) =
      (frame.parents.odd.den * (frame.child.den + frame.child.num)
          + frame.parents.odd.num * (frame.child.den - frame.child.num)) * frame.sGrade z -
        2 * frame.tGrade z := by
    have h := sp_identity frame z
    rw [hε] at h
    linarith
  have hsle := sGrade_le_pred frame hs
  have htle := tGrade_le_pred frame hz (by omega)
  have hK : 0 ≤ frame.parents.odd.den * (frame.child.den + frame.child.num)
      + frame.parents.odd.num * (frame.child.den - frame.child.num) := by
    nlinarith
  have hsp := sminus_ineq frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    hN1 hND hn2 hd2 hn hnd hrel
  have hlow_s := mul_le_mul_of_nonneg_left hsl hK
  have hstep : frame.child.periodDenominator * (-((frame.parents.odd.den - frame.parents.odd.num) + 1)) <
      frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
        (frame.parents.odd.den - frame.parents.odd.num) * z.2) := by
    rw [hid, hPD]
    nlinarith
  have hlow' := Int.add_one_le_iff.mpr (lt_of_mul_lt_mul_left hstep hT.le)
  have hE : (2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 ∧
      0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ frame.child.periodDenominator + 2 * frame.child.num) ∨
      (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
    rcases (frame.mem_closedPolygon_iff z).mp hz with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hnq : frame.parents.even.num = frame.child.num - 2 * frame.parents.odd.num := by
    have := frame.child_num_eq
    omega
  have hdq : frame.parents.even.den = frame.child.den - 2 * frame.parents.odd.den := by
    have := frame.child_den_eq
    omega
  have hup := sr_core_up_C frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den
    frame.parents.even.num frame.parents.even.den frame.child.periodDenominator (frame.tGrade z) (frame.sGrade z)
    hN1 hND hn2 hd2 (by omega) hnd (by omega) hrel hPD hnq hdq hE (by omega)
  have hsib := sib_identity frame.parents.odd.num frame.parents.odd.den frame.child.num frame.child.den hrel
  rw [hnq, hdq] at hup
  have hstepU : frame.child.periodDenominator * ((frame.parents.odd.den + frame.parents.odd.num) * z.1 +
      (frame.parents.odd.den - frame.parents.odd.num) * z.2) <
      frame.child.periodDenominator * (2 * (frame.parents.odd.den + frame.parents.odd.num) + 2) := by
    rw [hid, hPD]
    rw [hPD] at hup
    linarith [hup, hsib]
  have hup' := lt_of_mul_lt_mul_left hstepU hT.le
  exact ⟨by linarith, by linarith [Int.add_one_le_iff.mpr hup']⟩

/-- The harmonic value of the quarter-turned earlier field at `y`, from the ordinary zero-and-harmonic strip of the earlier
child: `Fp(y) = h(y)` when `1 − 2D ≤ s_p(y) ≤ 2r − 1` (with `s_p(y) = (D + N) y₁ + (D − N) y₂`). -/
theorem quarterTurnField_eq_harmonic_of_sp {conj : ChildFrame} {G : Field} (hStrips : conj.HasStrips G)
    {N D : ℤ} (hnum : conj.child.num = D - N) (hden : conj.child.den = D + N) {y : Site}
    (hw1 : 1 - 2 * D ≤ (D + N) * y.1 + (D - N) * y.2)
    (hw2 : (D + N) * y.1 + (D - N) * y.2 ≤ 2 * (D + N) - 1) :
    quarterTurnField G y = harmonicGrid y := by
  have e : conj.tGrade (QuarterTurn.counterclockwise.mapSite (0, -1) y) =
      (D + N) - ((D + N) * y.1 + (D - N) * y.2) := by
    unfold ChildFrame.tGrade
    rw [mapSite_quarterTurn_eq, hnum, hden]
    dsimp only
    ring
  have hlo : 1 - conj.child.den ≤ conj.tGrade (QuarterTurn.counterclockwise.mapSite (0, -1) y) := by
    rw [e, hden]
    linarith
  have hhi : conj.tGrade (QuarterTurn.counterclockwise.mapSite (0, -1) y) ≤
      conj.child.num + 2 * conj.child.den - 1 := by
    rw [e, hnum, hden]
    linarith
  exact quarterTurnField_eq_harmonic hStrips hlo hhi

/-- The harmonic value at `−V_q = (d_q − n_q, −n_q − d_q)`: `h(−V_q) = −M` when `T_q − d_q − n_q = 2M`. -/
theorem harmonicGrid_neg_Vq (nq dq T M : ℤ) (hT : T = dq ^ 2 + 2 * dq * nq - nq ^ 2) (hM : T - dq - nq = 2 * M) :
    harmonicGrid (-(nq - dq, nq + dq)) = -M := by
  show harmonicGrid (-(nq - dq), -(nq + dq)) = -M
  unfold harmonicGrid
  dsimp only
  have hpar : (-(nq - dq) + -(nq + dq)) % 2 = 0 := by omega
  rw [hpar]
  have key : (-(nq - dq)) ^ 2 + 2 * (-(nq - dq)) * (-(nq + dq)) - (-(nq + dq)) ^ 2 - 2 * (-(nq + dq)) - 0
      = -4 * M := by
    rw [hT] at hM
    linear_combination (-2 : ℤ) * hM
  rw [key]
  omega


/-- The second offer for `ε = 1` (`W = 1`): `C(v + U_q) = h(v) + 2`. The point `v − V_q` has `s_p = s_p(v) + 2`, which lies in
the window of the earlier child's strip, so `Fp(v − V_q) = h(v − V_q)`, and the harmonic translation gives `h(v) + h(−V_q)`. -/
theorem second_offer_plus {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate) (hStrips : conj.HasStrips G)
    (hε : frame.eps = 1) {v : Site} (hv : v ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hs : frame.sGrade v ≤ frame.child.den + frame.child.num - 1) :
    frame.sheetC (quarterTurnField G) (v + frame.offsetX) = harmonicGrid v + 2 := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hW : frame.phaseW = 1 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hX : frame.offsetX = (frame.parents.even.den, frame.parents.even.num) := frame.offsetX_of_W1 hW
  have hc := frame.sheetConstant_exact
  rw [hW] at hc
  have hT_q : frame.parents.even.periodDenominator =
      frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hε' : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = 1 := by
    have h : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den := rfl
    rw [← h]
    exact hε
  have hV : (frame.parents.odd.den + frame.parents.odd.num) * (frame.parents.even.num - frame.parents.even.den) +
      (frame.parents.odd.den - frame.parents.odd.num) * (frame.parents.even.num + frame.parents.even.den) = -2 := by
    linear_combination (-2 : ℤ) * hε'
  obtain ⟨hw1, hw2⟩ := sp_window_plus frame hε hv hN hn hs
  have hr : 3 ≤ frame.parents.odd.den + frame.parents.odd.num := by
    obtain ⟨-, -, hNle⟩ := frame.valid.odd_bounds
    have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
    omega
  have hspy : (frame.parents.odd.den + frame.parents.odd.num) * (v.1 - (frame.parents.even.num - frame.parents.even.den)) +
      (frame.parents.odd.den - frame.parents.odd.num) * (v.2 - (frame.parents.even.num + frame.parents.even.den)) =
      ((frame.parents.odd.den + frame.parents.odd.num) * v.1 + (frame.parents.odd.den - frame.parents.odd.num) * v.2) + 2 := by
    linear_combination (-1 : ℤ) * hV
  have hy : quarterTurnField G (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) =
      harmonicGrid (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) := by
    apply quarterTurnField_eq_harmonic_of_sp hStrips hnum hden
    · simp only [Prod.fst_sub, Prod.snd_sub]
      linarith
    · simp only [Prod.fst_sub, Prod.snd_sub]
      linarith
  obtain ⟨M, hM⟩ : ∃ M : ℤ, frame.parents.even.periodDenominator - frame.parents.even.den - frame.parents.even.num = 2 * M :=
    ⟨frame.sheetConstant - 2, by linarith⟩
  have hcM : frame.sheetConstant = M + 2 := by linarith
  have hEvV : EvenSite (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := by
    unfold EvenSite
    have hEv : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
    show ((frame.parents.even.num - frame.parents.even.den) + (frame.parents.even.num + frame.parents.even.den)) % 2 = 0
    omega
  have hsh : frame.sheetShift = 0 := sheetShift_of_phase_one hW
  have hoff : frame.sheetOffset = frame.parents.even.unmodifiedDeck.transverse + frame.parents.even.unmodifiedDeck.kernel := by
    unfold ChildFrame.sheetOffset
    rw [hε, one_smul]
  have hKer : frame.parents.even.unmodifiedDeck.kernel = (frame.parents.even.den, frame.parents.even.num) := rfl
  have hTra : frame.parents.even.unmodifiedDeck.transverse =
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := rfl
  have harg : v + (frame.parents.even.den, frame.parents.even.num) - frame.sheetShift - frame.sheetOffset =
      v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := by
    rw [hsh, hoff, hKer, hTra]
    ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, sub_zero] <;> ring
  have hneg := harmonicGrid_neg_Vq frame.parents.even.num frame.parents.even.den frame.parents.even.periodDenominator M
    hT_q hM
  have hsub := harmonicGrid_sub_even (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) v hEvV
  have e1 : ((frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).1 +
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).2) / 2 =
      frame.parents.even.num := by
    show (frame.parents.even.num - frame.parents.even.den + (frame.parents.even.num + frame.parents.even.den)) / 2 = _
    omega
  have e2 : ((frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).1 -
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).2) / 2 =
      -frame.parents.even.den := by
    show (frame.parents.even.num - frame.parents.even.den - (frame.parents.even.num + frame.parents.even.den)) / 2 = _
    omega
  rw [e1, e2] at hsub
  unfold ChildFrame.sheetC
  rw [hX, harg, hy, hsub, hneg]
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_add, Prod.snd_add, sub_zero, hsh]
  rw [hcM]
  ring


/-- The second offer for `ε = −1` (`W = 0`): `C(v + U_p) = h(v) + 2`. The periodicity moves `v + U_p − V_q` to `v − V_q`,
where `s_p = s_p(v) − 2` lies in the window of the earlier child's strip (`s_p(v) ≥ −b` from `sp_window_minus`). -/
theorem second_offer_minus {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hStrips : conj.HasStrips G)
    (hε : frame.eps = -1) {v : Site} (hv : v ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hsl : 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade v)
    (hs : frame.sGrade v ≤ frame.child.den + frame.child.num - 1) :
    frame.sheetC (quarterTurnField G) (v + frame.offsetX) = harmonicGrid v + 2 := by
  obtain ⟨hnum, hden⟩ := conj_child_num_den hconj
  have hW : frame.phaseW = 0 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hX : frame.offsetX = (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := frame.offsetX_of_W0 hW
  have hc := frame.sheetConstant_exact
  rw [hW] at hc
  have hT_q : frame.parents.even.periodDenominator =
      frame.parents.even.den ^ 2 + 2 * frame.parents.even.den * frame.parents.even.num - frame.parents.even.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hε' : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = -1 := by
    have h : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den := rfl
    rw [← h]
    exact hε
  have hV : (frame.parents.odd.den + frame.parents.odd.num) * (frame.parents.even.num - frame.parents.even.den) +
      (frame.parents.odd.den - frame.parents.odd.num) * (frame.parents.even.num + frame.parents.even.den) = 2 := by
    linear_combination (-2 : ℤ) * hε'
  obtain ⟨hw1, hw2⟩ := sp_window_minus frame hε hv hN hn hsl hs
  have hr : 3 ≤ frame.parents.odd.den + frame.parents.odd.num := by
    obtain ⟨-, -, hNle⟩ := frame.valid.odd_bounds
    have hoddpar : (frame.parents.odd.num + frame.parents.odd.den) % 2 = 1 := frame.valid.odd_parity
    omega
  have hspy : (frame.parents.odd.den + frame.parents.odd.num) * (v.1 - (frame.parents.even.num - frame.parents.even.den)) +
      (frame.parents.odd.den - frame.parents.odd.num) * (v.2 - (frame.parents.even.num + frame.parents.even.den)) =
      ((frame.parents.odd.den + frame.parents.odd.num) * v.1 + (frame.parents.odd.den - frame.parents.odd.num) * v.2) - 2 := by
    linear_combination (-1 : ℤ) * hV
  have hy : quarterTurnField G (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) =
      harmonicGrid (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) := by
    apply quarterTurnField_eq_harmonic_of_sp hStrips hnum hden
    · simp only [Prod.fst_sub, Prod.snd_sub]
      linarith
    · simp only [Prod.fst_sub, Prod.snd_sub]
      linarith
  obtain ⟨M, hM⟩ : ∃ M : ℤ, frame.parents.even.periodDenominator - frame.parents.even.den - frame.parents.even.num = 2 * M :=
    ⟨frame.sheetConstant, by linarith⟩
  have hcM : frame.sheetConstant = M := by linarith
  have hEvV : EvenSite (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := by
    unfold EvenSite
    have hEv : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
    show ((frame.parents.even.num - frame.parents.even.den) + (frame.parents.even.num + frame.parents.even.den)) % 2 = 0
    omega
  have hsh : frame.sheetShift = (frame.parents.even.den, frame.parents.even.num) := by
    ext <;> simp [ChildFrame.sheetShift, Fraction.unmodifiedDeck, hW]
  have hoff : frame.sheetOffset = frame.parents.even.unmodifiedDeck.transverse + -frame.parents.even.unmodifiedDeck.kernel := by
    unfold ChildFrame.sheetOffset
    rw [hε, neg_one_smul ℤ]
  have hKer : frame.parents.even.unmodifiedDeck.kernel = (frame.parents.even.den, frame.parents.even.num) := rfl
  have hTra : frame.parents.even.unmodifiedDeck.transverse =
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) := rfl
  have harg : v + (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) - frame.sheetShift - frame.sheetOffset =
      (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)) +
        (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
    rw [hsh, hoff, hKer, hTra]
    ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_neg, Prod.snd_add, Prod.snd_sub, Prod.snd_neg] <;> ring
  have hneg := harmonicGrid_neg_Vq frame.parents.even.num frame.parents.even.den frame.parents.even.periodDenominator M
    hT_q hM
  have hEvV' := hEvV
  have hsub := harmonicGrid_sub_even (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den) v hEvV'
  have e1 : ((frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).1 +
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).2) / 2 =
      frame.parents.even.num := by
    show (frame.parents.even.num - frame.parents.even.den + (frame.parents.even.num + frame.parents.even.den)) / 2 = _
    omega
  have e2 : ((frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).1 -
      (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den).2) / 2 =
      -frame.parents.even.den := by
    show (frame.parents.even.num - frame.parents.even.den - (frame.parents.even.num + frame.parents.even.den)) / 2 = _
    omega
  rw [e1, e2] at hsub
  have hper := quarterTurnField_add_two hG hnum hden
    (v - (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den))
  unfold ChildFrame.sheetC
  rw [hX, harg, hper, hy, hsub, hneg]
  unfold ChildFrame.siblingSlope
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hsh]
  rw [hcM]
  linear_combination (-2 : ℤ) * hε'

/-- The second offer: `C(v + X) = h(v) + 2` on the longitudinal range (both phases). -/
theorem second_offer_of_longitudinal {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hStrips : conj.HasStrips G)
    {v : Site} (hv : v ∈ frame.closedPolygon)
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num)
    (hsl : 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade v)
    (hs : frame.sGrade v ≤ frame.child.den + frame.child.num - 1) :
    frame.sheetC (quarterTurnField G) (v + frame.offsetX) = harmonicGrid v + 2 := by
  rcases frame.eps_unit with h | h
  · exact second_offer_plus hconj hStrips h hv hN hn hs
  · exact second_offer_minus hconj hG hStrips h hv hN hn hsl hs


/-! ### The offsets stay in `E` -/

/-- The lattice identity `n s(v) − L t(v) = T v₂` (`L = d + n`, `T = d² + 2dn − n²`, `v₂` the second lattice coordinate). -/
theorem lattice_identity_second (frame : ChildFrame) (v : Site) :
    frame.child.num * frame.sGrade v - (frame.child.den + frame.child.num) * frame.tGrade v =
      frame.child.periodDenominator * v.2 := by
  have hPD : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  rw [hPD]
  unfold ChildFrame.sGrade ChildFrame.tGrade
  ring

/-- On an even site the child `t`-grade is even (`d − n` is even, `x − y` is even). -/
theorem tGrade_even_of_evenSite (frame : ChildFrame) {v : Site} (hv : EvenSite v) : frame.tGrade v % 2 = 0 := by
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hv' : (v.1 + v.2) % 2 = 0 := hv
  obtain ⟨k, hk⟩ : ∃ k : ℤ, frame.child.den - frame.child.num = 2 * k := ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v.1 - v.2 = 2 * m := ⟨(v.1 - v.2) / 2, by omega⟩
  have ht : frame.tGrade v = 2 * (frame.child.num * m - k * v.2) := by
    unfold ChildFrame.tGrade
    linear_combination frame.child.num * hm - v.2 * hk
  rw [ht]
  generalize frame.child.num * m - k * v.2 = A
  omega

/-- The even top edge is not reached on the longitudinal range: `t = L − 2`, `0 ≤ s ≤ L − 1` is impossible, since the lattice
identity forces `v₂ = −1`, then `n s = 2n² − 2L`, so `n ∣ 2d` against `gcd(n, d) = 1`. -/
theorem even_top_false (n d s v2 : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hcop : IsCoprime n d) (hs0 : 0 ≤ s)
    (hs1 : s ≤ d + n - 1) (hid : n * s - (d + n) * (d + n - 2) = (d ^ 2 + 2 * d * n - n ^ 2) * v2) : False := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hLT : (d + n) * (d + n - 2) < 2 * (d ^ 2 + 2 * d * n - n ^ 2) := by nlinarith
  have hneg : v2 < 0 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hgt : -2 < v2 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hv2 : v2 = -1 := by omega
  subst hv2
  have hns : n * s = 2 * n ^ 2 - 2 * (d + n) := by linear_combination hid
  have hdvd : n ∣ 2 * d := ⟨2 * n - s - 2, by linear_combination hns⟩
  have h2 : n ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have := Int.le_of_dvd (by norm_num) h2
  omega

/-- The odd top edge `t = d` is not reached on the longitudinal range `2 − (d − n) ≤ s ≤ L − 1`: the identity forces `v₂ = −1`,
then `n (s + d − n) = 0`. -/
theorem odd_top_false (n d s v2 : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hs0 : 2 - (d - n) ≤ s)
    (hs1 : s ≤ d + n - 1) (hid : n * s - (d + n) * d = (d ^ 2 + 2 * d * n - n ^ 2) * v2) : False := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hneg : v2 < 0 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hgt : -2 < v2 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hv2 : v2 = -1 := by omega
  subst hv2
  have h0 : n * (s + (d - n)) = 0 := by linear_combination hid
  rcases mul_eq_zero.mp h0 with h | h
  · omega
  · omega

/-- The odd edge `t = d − 1` is not reached on the longitudinal range (the identity forces `v₂ = −1`, which is too small). -/
theorem odd_top_one_false (n d s v2 : ℤ) (hn : 3 ≤ n) (hnd : n + 2 ≤ d) (hs0 : 2 - (d - n) ≤ s)
    (hs1 : s ≤ d + n - 1) (hid : n * s - (d + n) * (d - 1) = (d ^ 2 + 2 * d * n - n ^ 2) * v2) : False := by
  have hT : 0 < d ^ 2 + 2 * d * n - n ^ 2 := by nlinarith
  have hneg : v2 < 0 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hgt : -2 < v2 := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  have hv2 : v2 = -1 := by omega
  subst hv2
  nlinarith


/-- The offset `X` of the longitudinal exits: `t(X) = 2` and `c − 2 ≤ s(X) ≤ T − c + 1` (`c = d − n`, `T` the period). It is
`X = U_q` for `W = 1` (`s(X) = T − 2K`) and `X = U_p` for `W = 0` (`s(X) = 2K`), with `K = D(d + n) + N(d − n)`. -/
theorem offset_data (frame : ChildFrame) :
    ∃ dX nX : ℤ, frame.offsetX = (dX, nX) ∧
      frame.child.num * dX - frame.child.den * nX = 2 ∧
      (frame.child.den - frame.child.num) - 2 ≤
        (frame.child.den + frame.child.num) * dX + (frame.child.den - frame.child.num) * nX ∧
      (frame.child.den + frame.child.num) * dX + (frame.child.den - frame.child.num) * nX ≤
        frame.child.periodDenominator - (frame.child.den - frame.child.num) + 1 ∧
      (dX + nX) % 2 = 0 := by
  have hPD : frame.child.periodDenominator =
      frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hnum := frame.child_num_eq
  have hden := frame.child_den_eq
  obtain ⟨hDpos, hN0, hNle⟩ := frame.valid.odd_bounds
  obtain ⟨hdq0, hnq0, hnqle⟩ := frame.valid.even_bounds
  have hevpar : (frame.parents.even.num + frame.parents.even.den) % 2 = 0 := frame.valid.even_parity
  obtain ⟨hnpos, -, hdiff, -, -⟩ := frame.child_facts
  have hD1 : 1 ≤ frame.parents.odd.den := by omega
  have hdq1 : 1 ≤ frame.parents.even.den := by omega
  have hnq0' : 0 ≤ frame.parents.even.num := by omega
  have hN0' : 0 ≤ frame.parents.odd.num := by omega
  have hTK : frame.child.periodDenominator =
      2 * (frame.parents.odd.den * (frame.child.den + frame.child.num) +
          frame.parents.odd.num * (frame.child.den - frame.child.num)) +
        frame.parents.even.den * (frame.child.den + frame.child.num) +
        frame.parents.even.num * (frame.child.den - frame.child.num) := by
    rw [hPD, hnum, hden]
    ring
  have hK : frame.child.den - frame.child.num ≤
      frame.parents.odd.den * (frame.child.den + frame.child.num) +
        frame.parents.odd.num * (frame.child.den - frame.child.num) := by
    nlinarith
  have hdL : frame.child.den + frame.child.num ≤ frame.parents.even.den * (frame.child.den + frame.child.num) := by
    nlinarith
  have hncn : 0 ≤ frame.parents.even.num * (frame.child.den - frame.child.num) := by
    nlinarith
  rcases frame.eps_unit with heps | heps
  · have hW : frame.phaseW = 1 := by
      unfold ChildFrame.phaseW
      rw [heps]
      norm_num
    have hX : frame.offsetX = (frame.parents.even.den, frame.parents.even.num) := frame.offsetX_of_W1 hW
    have hε : frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den = 1 := by
      have e : frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.even.num * frame.parents.odd.den :=
        rfl
      rw [← e]
      exact heps
    refine ⟨frame.parents.even.den, frame.parents.even.num, hX, ?_, ?_, ?_, ?_⟩
    · rw [hnum, hden]
      linear_combination 2 * hε
    · linarith
    · linarith
    · omega
  · have hW : frame.phaseW = 0 := by
      unfold ChildFrame.phaseW
      rw [heps]
      norm_num
    have hX : frame.offsetX = (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := frame.offsetX_of_W0 hW
    have hε : frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num = -1 := by
      have e := frame.eps_eq
      rw [← e]
      exact heps
    refine ⟨2 * frame.parents.odd.den, 2 * frame.parents.odd.num, hX, ?_, ?_, ?_, ?_⟩
    · linear_combination (-2 : ℤ) * hε
    · linarith
    · linarith
    · omega

/-- The sheet offset keeps the longitudinal point in the closed polygon: the top edges are not reached on the longitudinal range
(`top_exclusion`), and the offset adds `t = 2` and `s ∈ [c − 2, T − c + 1]`. -/
theorem mem_offset_of_longRange (frame : ChildFrame) {v : Site} (hv : v ∈ frame.closedPolygon)
    (hsl : 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade v)
    (hsu : frame.sGrade v ≤ frame.child.den + frame.child.num - 1) (hn : 3 ≤ frame.child.num) :
    v + frame.offsetX ∈ frame.closedPolygon := by
  obtain ⟨dX, nX, hX, ht2, hs1, hs2, hpar⟩ := offset_data frame
  rw [hX]
  have hcop : IsCoprime frame.child.num frame.child.den := frame.child_reduced
  have hPD : frame.child.periodDenominator =
      frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  obtain ⟨hnpos, hnd0, hdiff, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have htz : frame.tGrade (v + (dX, nX)) = frame.tGrade v + 2 := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination ht2
  have hsz : frame.sGrade (v + (dX, nX)) =
      frame.sGrade v + ((frame.child.den + frame.child.num) * dX + (frame.child.den - frame.child.num) * nX) := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hEq : EvenSite (v + (dX, nX)) ↔ EvenSite v := by
    unfold EvenSite
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  rcases (frame.mem_closedPolygon_iff v).mp hv with ⟨hve, hb⟩ | ⟨hvo, hb⟩
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have htop : frame.tGrade v ≤ frame.child.den + frame.child.num - 4 := by
      have hte := tGrade_even_of_evenSite frame hve
      by_contra hcon
      have h1 : frame.tGrade v = frame.child.den + frame.child.num - 2 ∨
          frame.tGrade v = frame.child.den + frame.child.num - 3 := by
        omega
      rcases h1 with h1 | h1
      · have hid := lattice_identity_second frame v
        rw [h1, hPD] at hid
        exact even_top_false frame.child.num frame.child.den (frame.sGrade v) v.2 hn hnd hcop hb3 hsu hid
      · omega
    refine (frame.mem_closedPolygon_iff _).mpr (Or.inl ⟨hEq.mpr hve, ?_, ?_, ?_, ?_⟩)
    · rw [htz]
      linarith
    · rw [htz]
      omega
    · rw [hsz]
      linarith
    · rw [hsz]
      linarith
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have htop : frame.tGrade v ≤ frame.child.den - 2 := by
      by_contra hcon
      have h1 : frame.tGrade v = frame.child.den - 1 ∨ frame.tGrade v = frame.child.den := by
        omega
      rcases h1 with h1 | h1
      · have hid := lattice_identity_second frame v
        rw [h1, hPD] at hid
        exact odd_top_one_false frame.child.num frame.child.den (frame.sGrade v) v.2 hn hnd (by linarith) hsu hid
      · have hid := lattice_identity_second frame v
        rw [h1, hPD] at hid
        exact odd_top_false frame.child.num frame.child.den (frame.sGrade v) v.2 hn hnd (by linarith) hsu hid
    refine (frame.mem_closedPolygon_iff _).mpr (Or.inr ⟨fun h => hvo (hEq.mp h), ?_, ?_, ?_, ?_⟩)
    · rw [htz]
      linarith
    · rw [htz]
      omega
    · rw [hsz]
      linarith
    · rw [hsz]
      linarith


/-- The offers of the longitudinal exits, for the quarter-turned earlier field of the packet: `mem` (the offset stays in `E`),
`first` (`first_offer_of_phase_zero`, `first_offer_of_phase_one` with the named `ParentStepSign`), `second`. -/
theorem longitudinalOffers_of_conj {frame conj : ChildFrame} {G : Field}
    (hconj : conj.child = frame.parents.odd.rotate)
    (hG : HasGeneratorPeriods conj.child G conj.coherentConstantU conj.coherentConstantV)
    (hStrips : conj.HasStrips G)
    (hS : frame.StripInputs (frame.sheetMin (quarterTurnField G)))
    (hPSS : ParentStepSign frame (quarterTurnField G))
    (hN : 0 < frame.parents.odd.num) (hn : 3 ≤ frame.child.num) :
    frame.LongitudinalOffers (quarterTurnField G) where
  mem := fun v hv hr => by
    obtain ⟨hr1, hr2⟩ := hr
    exact mem_offset_of_longRange frame hv hr1 hr2 hn
  first := fun v hv hr => by
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨hnpos, hnd, -, -, -⟩ := frame.child_facts
    rcases frame.eps_unit with h | h
    · have hW : frame.phaseW = 1 := by
        unfold ChildFrame.phaseW
        rw [h]
        norm_num
      exact first_offer_of_phase_one hconj hStrips hS hPSS hW hN hn hv hr2
    · have hW : frame.phaseW = 0 := by
        unfold ChildFrame.phaseW
        rw [h]
        norm_num
      exact first_offer_of_phase_zero hconj hG hS hW hv (by omega)
  second := fun v hv hr => by
    obtain ⟨hr1, hr2⟩ := hr
    exact second_offer_of_longitudinal hconj hG hStrips hv hN hn hr1 hr2

/-- The V-arc range `VArcInputs` of the current word, from the strong estimates of the earlier word `conjWord word`, the named
`ParentStepSign` (the one input left to w2), and the child strip and height inputs. -/
theorem vArcInputs_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {F : Field}
    (hSE : StrongEstimates (conjWord word))
    (hPSS : ParentStepSign (frameAt word) (quarterTurnField (standardField (conjWord word))))
    (hS : (frameAt word).StripInputs ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hH : (frameAt word).HeightInputs ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))))
    (hagree : ∀ y ∈ (frameAt word).closedPolygon,
      F y = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y)
    (hper : HasGeneratorPeriods (frameAt word).child F 0 (frameAt word).coherentConstantV) :
    VArcInputs (frameAt word) F :=
  vArcInputs_of_longitudinal h hS hH hagree hper
    (longitudinalOffers_of_conj (frameAt_conj_child h) hSE.packet.periods hSE.packet.strips hS hPSS
      (frameAt_odd_num_pos h) (child_num_ge_three h))

end FLatticePaper.Induction
