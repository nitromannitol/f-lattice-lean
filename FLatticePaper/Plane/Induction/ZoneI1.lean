import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.ZeroRegion
import FLatticePaper.Plane.Induction.WordInduction

/-! # The frame-level facts of the zone of I1 (task 49, the wrapper of step (d))

For the earlier word `u` with child `(D − N, D + N)` (so `N = parentN u`, `D = parentD u`), the packet periods of the standard
field give the kernel and transverse relations used by `ZoneHyp`, with the coherent constants `0` and `−(B + D)`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace ZoneI1

/-- The value of the harmonic grid from its numerator. -/
theorem harmonicGrid_of_numerator (x : Site) (k : ℤ)
    (h : x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - (x.1 + x.2) % 2 = 4 * k) : harmonicGrid x = k := by
  unfold harmonicGrid
  rw [h]
  exact Int.mul_ediv_cancel_left k (by norm_num)

/-- The kernel of the child `(D − N, D + N)` (even) is `(D + N, D − N)`. -/
theorem kernel_of_even (U : ChildFrame) : U.child.modifiedDeck.kernel = (U.child.den, U.child.num) := by
  have he : (U.child.num + U.child.den) % 2 = 0 := U.child_even
  unfold Fraction.modifiedDeck Fraction.periodMultiplicity
  rw [if_pos he]
  simp

/-- The transverse vector of the child is `(num − den, num + den)`. -/
theorem transverse_of_child (U : ChildFrame) :
    U.child.modifiedDeck.transverse = (U.child.num - U.child.den, U.child.num + U.child.den) := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck
  rfl

/-- The coherent constant of the kernel is zero (integer form, child `(b, r) = (D − N, D + N)`). -/
theorem cU_value (D N b r : ℤ) (hb : b = D - N) (hr : r = D + N) :
    harmonicGrid (b - r + 1, b + r - 1) - (b * (b - r + 1) - r * (b + r - 1))
      + ((r + b) - (r ^ 2 + 2 * r * b - b ^ 2)) / 2 = 0 := by
  subst hb hr
  have hh : harmonicGrid ((D - N) - (D + N) + 1, (D - N) + (D + N) - 1) = D + N ^ 2 - 2 * D * N - D ^ 2 := by
    apply harmonicGrid_of_numerator
    have hp : ((D - N) - (D + N) + 1 + ((D - N) + (D + N) - 1)) % 2 = 0 := by omega
    rw [hp]
    ring
  rw [hh]
  have hd : ((D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)) / 2
      = D + N ^ 2 - 2 * D * N - D ^ 2 := by
    rw [show (D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)
        = 2 * (D + N ^ 2 - 2 * D * N - D ^ 2) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hd]
  ring

/-- The coherent constant of the transverse is `−(B + D)` (integer form). -/
theorem cV_value (D N b r : ℤ) (hb : b = D - N) (hr : r = D + N) :
    ((r + b) - (r ^ 2 + 2 * r * b - b ^ 2)) / 2 - (b * (b + 1) - r * (2 * b + r - 1))
      + (b * (b - r) - r * (b + r)) = -(D ^ 2 + 2 * D * N - N ^ 2 + D) := by
  subst hb hr
  have hd : ((D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)) / 2
      = D - (D ^ 2 + 2 * D * N - N ^ 2) := by
    rw [show (D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)
        = 2 * (D - (D ^ 2 + 2 * D * N - N ^ 2)) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hd]
  ring

/-- The packet periods of the earlier standard field, in the form of `ZoneHyp`: the kernel `(D + N, D − N)` is a zero period
and the transverse `(−2N, 2D)` shifts by `t(y) − (B + D)`. -/
theorem periods_of_packet (U : ChildFrame) (F : Field) (hP : U.Packet F) (N D : ℤ)
    (hb : U.child.num = D - N) (hr : U.child.den = D + N) :
    (∀ y : Site, F (y + (D + N, D - N)) = F y) ∧
    (∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2)
      - (D ^ 2 + 2 * D * N - N ^ 2 + D)) := by
  obtain ⟨p1, p2⟩ := hP.periods
  have hU : U.coherentConstantU = 0 := by
    have e : U.child.modifiedDeck.transverse + (1, -1)
        = (U.child.num - U.child.den + 1, U.child.num + U.child.den - 1) := by
      rw [transverse_of_child U]
      ext
      · simp
      · simp; ring
    unfold ChildFrame.coherentConstantU ChildFrame.symmetryConstant ChildFrame.tGrade
    rw [e]
    unfold Fraction.periodDenominator
    have := cU_value D N U.child.num U.child.den hb hr
    linear_combination this
  have hV : U.coherentConstantV = -(D ^ 2 + 2 * D * N - N ^ 2 + D) := by
    have e2 : U.child.modifiedDeck.kernel + U.child.modifiedDeck.transverse + (1, -1)
        = (U.child.num + 1, 2 * U.child.num + U.child.den - 1) := by
      rw [kernel_of_even U, transverse_of_child U]
      ext
      · simp
      · simp; ring
    unfold ChildFrame.coherentConstantV ChildFrame.symmetryConstant ChildFrame.centre ChildFrame.tGrade
    rw [e2, transverse_of_child U]
    unfold Fraction.periodDenominator
    have := cV_value D N U.child.num U.child.den hb hr
    linear_combination this
  constructor
  · intro y
    have h := p1 y
    rw [kernel_of_even U, hU, hr, hb] at h
    simpa using h
  · intro y
    have h := p2 y
    rw [transverse_of_child U, hV, hb, hr] at h
    unfold Fraction.transverseGrade at h
    rw [hb, hr] at h
    have e : ((D - N) - (D + N), (D - N) + (D + N)) = (-2 * N, 2 * D) := by
      ext
      · first | (simp; done) | (simp; ring)
      · first | (simp; done) | (simp; ring)
    rw [e] at h
    linear_combination h

/-- The polygon of the zone is inside the closed polygon of the earlier child. -/
theorem polyU_closed (U : ChildFrame) (N D : ℤ) (hb : U.child.num = D - N) (hr : U.child.den = D + N) (y : Site)
    (hP : ZoneSlip.PolyU N D y) : y ∈ U.closedPolygon := by
  have hT : U.child.periodDenominator = 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hb, hr]
    ring
  have hs : U.sGrade y = 2 * D * y.1 + 2 * N * y.2 := by
    unfold ChildFrame.sGrade
    rw [hb, hr]
    ring
  have ht : U.tGrade y = (D - N) * y.1 - (D + N) * y.2 := by
    unfold ChildFrame.tGrade
    rw [hb, hr]
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq]
  rcases hP with ⟨he, h1, h2, h3, h4⟩ | ⟨hne, h1, h2, h3, h4⟩
  · rw [if_pos he, hT, ht, hs, hb, hr]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [if_neg hne, hT, ht, hs, hb, hr]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The slip of the standard field at the child's shortShift is `F y − F (y + (2ε_u D_u, 2ε_u N_u))`. -/
theorem slip_eq_shortShift (U : ChildFrame) (F : Field) (y : Site) :
    U.slip F 1 y = F y - F (y + (2 * U.eps * U.parents.odd.den, 2 * U.eps * U.parents.odd.num)) := by
  unfold ChildFrame.slip ChildFrame.shortShift
  rw [one_smul]

/-- The determinant of the earlier parents: `N_u (D + N) − D_u (D − N) = ε_u`. -/
theorem det_conj (U : ChildFrame) (N D : ℤ) (hb : U.child.num = D - N) (hr : U.child.den = D + N) :
    U.parents.odd.num * (D + N) - U.parents.odd.den * (D - N) = U.eps := by
  have hcn : U.child.num = 2 * U.parents.odd.num + U.parents.even.num := by
    unfold ChildFrame.child Parents.current Parents.combine
    ring
  have hcd : U.child.den = 2 * U.parents.odd.den + U.parents.even.den := by
    unfold ChildFrame.child Parents.current Parents.combine
    ring
  have he : U.eps = U.parents.odd.num * U.parents.even.den - U.parents.even.num * U.parents.odd.den := by
    unfold ChildFrame.eps Fraction.det
    ring
  rw [he, ← hb, ← hr, hcn, hcd]
  ring

theorem child_num_eq (V : ChildFrame) : V.child.num = 2 * V.parents.odd.num + V.parents.even.num := by
  unfold ChildFrame.child Parents.current Parents.combine
  ring

theorem child_den_eq (V : ChildFrame) : V.child.den = 2 * V.parents.odd.den + V.parents.even.den := by
  unfold ChildFrame.child Parents.current Parents.combine
  ring

theorem eps_eq (V : ChildFrame) :
    V.eps = V.parents.odd.num * V.parents.even.den - V.parents.even.num * V.parents.odd.den := by
  unfold ChildFrame.eps Fraction.det
  ring

/-- The four bounds of the zone box, from the closed polygon of the word (both parities). -/
theorem closed_bounds (V : ChildFrame) (z : Site) (hz : z ∈ V.closedPolygon) :
    V.child.num * z.1 - V.child.den * z.2 ≤ V.child.den + V.child.num - 1 ∧
    2 - V.child.den + V.child.num ≤ (V.child.den + V.child.num) * z.1 + (V.child.den - V.child.num) * z.2 ∧
    (V.child.den + V.child.num) * z.1 + (V.child.den - V.child.num) * z.2
      ≤ V.child.den * V.child.den + 2 * V.child.den * V.child.num - V.child.num * V.child.num
        + V.child.den + V.child.num - 2 := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := V.child_facts
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq] at hz
  unfold ChildFrame.tGrade at *
  by_cases he : EvenSite z
  · rw [if_pos he] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [hT] at h1 h4
    unfold ChildFrame.sGrade at h3 h4
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rw [if_neg he] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [hT] at h1
    unfold ChildFrame.sGrade at h3 h4
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- The zone box: `t(z) ≥ 1 − d` on the closed polygon of the word forces `0 ≤ z₁ ≤ d`, `0 ≤ z₂ ≤ n`. -/
theorem box_of_closed (V : ChildFrame) (z : Site) (hz : z ∈ V.closedPolygon)
    (ht : 1 - V.child.den ≤ V.tGrade z) :
    0 ≤ z.1 ∧ z.1 ≤ V.child.den ∧ 0 ≤ z.2 ∧ z.2 ≤ V.child.num := by
  obtain ⟨hn0, hnd, -, -, -⟩ := V.child_facts
  obtain ⟨b1, b2, b3⟩ := closed_bounds V z hz
  unfold ChildFrame.tGrade at ht
  exact ZeroRegion.zeroRegion_box V.child.num V.child.den z.1 z.2 hn0 hnd ht b1 b2 b3

/-- The sheet of the word in coordinates (the frame's `sheetC` with its shift, offset and constant unfolded). -/
theorem sheetC_expr (V : ChildFrame) (Fp : Site → ℤ) (z : Site) :
    V.sheetC Fp z = Fp (z.1 - (1 - V.phaseW) * V.parents.even.den
        - (V.parents.even.num - V.parents.even.den + V.eps * V.parents.even.den),
        z.2 - (1 - V.phaseW) * V.parents.even.num
        - (V.parents.even.num + V.parents.even.den + V.eps * V.parents.even.num))
      + (V.parents.even.num * (z.1 - (1 - V.phaseW) * V.parents.even.den)
        - V.parents.even.den * (z.2 - (1 - V.phaseW) * V.parents.even.num))
      + ((V.parents.even.den * V.parents.even.den + 2 * V.parents.even.den * V.parents.even.num
          - V.parents.even.num * V.parents.even.num - V.parents.even.den - V.parents.even.num) / 2
        + 2 * V.phaseW) := by
  unfold ChildFrame.sheetC ChildFrame.sheetShift ChildFrame.sheetOffset ChildFrame.siblingSlope
    ChildFrame.sheetConstant Fraction.periodDenominator Fraction.unmodifiedDeck
  simp only [smul_eq_mul, Prod.smul_mk, Prod.fst_sub, Prod.snd_sub, Prod.mk_add_mk]
  congr 1
  ring_nf

/-- Step (d), the zone of I1 at a proper word: the sheet `C(z)` of the word is nonnegative on the zone of the word, from
the strong estimates of the earlier conjugate. -/
theorem I1_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) (z : Site)
    (hz : z ∈ (frameAt word).closedPolygon)
    (ht : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z) :
    0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z := by
  have hcj : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate :=
    frameAt_conj_child h
  have hodd := (frameAt word).valid.odd_parity
  have hrot := Fraction.rotate_of_odd hodd
  set N := (frameAt word).parents.odd.num with hN
  set D := (frameAt word).parents.odd.den with hD
  set nq := (frameAt word).parents.even.num with hnq
  set dq := (frameAt word).parents.even.den with hdq
  have hrot' : (frameAt word).parents.odd.rotate = ⟨D - N, D + N⟩ := hrot
  have hb : (frameAt (conjWord word)).child.num = D - N := by rw [hcj, hrot']
  have hr : (frameAt (conjWord word)).child.den = D + N := by rw [hcj, hrot']
  obtain ⟨huN, -, huDN, -, -⟩ := ChildFrame.child_facts (frameAt (conjWord word))
  have hN1 : 1 ≤ N := by rw [hr, hb] at huDN; omega
  have hND : N < D := by rw [hb] at huN; omega
  have hoddN : (N + D) % 2 = 1 := hodd
  have hrodd : (D + N) % 2 = 1 := by omega
  set Nu := (frameAt (conjWord word)).parents.odd.num with hNu
  set Du := (frameAt (conjWord word)).parents.odd.den with hDu
  set epsU := (frameAt (conjWord word)).eps with hepsU
  have hdet : Nu * (D + N) - Du * (D - N) = epsU := det_conj (frameAt (conjWord word)) N D hb hr
  have hepsU' : epsU = 1 ∨ epsU = -1 := by
    have h2 : (epsU - 1) * (epsU + 1) = 0 := by
      linear_combination (frameAt (conjWord word)).eps_sq
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; linarith
    · right; linarith
  have hoddu : (Nu + Du) % 2 = 1 := by
    have := (frameAt (conjWord word)).valid.odd_parity
    unfold Fraction.Odd at this
    exact this
  obtain ⟨hK, hT⟩ := periods_of_packet (frameAt (conjWord word)) (standardField (conjWord word))
    hS.packet N D hb hr
  have hslip : ∀ y : Site, ZoneSlip.PolyU N D y →
      0 ≤ ZoneSlip.slipU (standardField (conjWord word)) (2 * epsU * Du, 2 * epsU * Nu) y ∧
      ZoneSlip.slipU (standardField (conjWord word)) (2 * epsU * Du, 2 * epsU * Nu) y ≤ 2 := by
    intro y hy
    have hc := polyU_closed (frameAt (conjWord word)) N D hb hr y hy
    have hsr := hS.slipRange y hc
    rw [slip_eq_shortShift] at hsr
    unfold ZoneSlip.slipU
    exact hsr
  have hstrip : ∀ y : Site, 1 - (D + N) ≤ (D - N) * y.1 - (D + N) * y.2 →
      (D - N) * y.1 - (D + N) * y.2 ≤ (D - N) + 2 * (D + N) - 1 → standardField (conjWord word) y = 0 := by
    intro y h1 h2
    have ht' : (frameAt (conjWord word)).tGrade y = (D - N) * y.1 - (D + N) * y.2 := by
      unfold ChildFrame.tGrade
      rw [hb, hr]
    apply hS.packet.strips.1 y
    · rw [ht', hr]; exact h1
    · rw [ht', hb, hr]; exact h2
  have hpN : parentN (conjWord word) = N := by
    unfold parentN
    rw [hr, hb]
    omega
  have hpD : parentD (conjWord word) = D := by
    unfold parentD
    rw [hr, hb]
    omega
  have hzs : ∀ x : Site, 1 - D ≤ N * x.1 - D * x.2 → N * x.1 - D * x.2 ≤ N + 2 * D - 1 →
      quarterTurnField (standardField (conjWord word)) x = 0 := by
    intro x h1 h2
    apply hS.zeroStripInterval x
    · rw [hpN, hpD]; exact h1
    · rw [hpN, hpD]; exact h2
  have hzev : ∀ x : Site, (x.1 + x.2) % 2 = 0 → N * x.1 - D * x.2 = -D →
      quarterTurnField (standardField (conjWord word)) x = 0 := by
    intro x h1 h2
    apply hS.zeroEvenLine x h1
    rw [hpN, hpD]; exact h2
  have hcn : (frameAt word).child.num = 2 * N + nq := child_num_eq (frameAt word)
  have hcd : (frameAt word).child.den = 2 * D + dq := child_den_eq (frameAt word)
  have hep : (frameAt word).eps = N * dq - nq * D := eps_eq (frameAt word)
  have hdq0 : 0 < 2 * D + dq := by
    obtain ⟨-, -, -, h3, -⟩ := ChildFrame.child_facts (frameAt word)
    rw [hcd] at h3
    omega
  have H : ZoneCase.ZoneHyp (standardField (conjWord word)) N D Nu Du epsU :=
    { hN := by omega
      hND := hND
      hr := hrodd
      hdet := hdet
      hepsU := hepsU'
      hodd := hoddu
      hK := hK
      hT := hT
      hslip := hslip
      hstrip := hstrip }
  obtain ⟨k1, hk1⟩ := Int.even_mul_pred_self dq
  obtain ⟨k2, hk2⟩ := Int.even_mul_succ_self nq
  have hcq : 2 * (k1 - k2 + dq * nq) = dq * dq + 2 * dq * nq - nq * nq - dq - nq := by
    linear_combination (-1 : ℤ) * hk1 + hk2
  have hdiv : (dq * dq + 2 * dq * nq - nq * nq - dq - nq) / 2 = k1 - k2 + dq * nq := by
    rw [← hcq]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hsheet := sheetC_expr (frameAt word) (quarterTurnField (standardField (conjWord word))) z
  rw [← hnq, ← hdq] at hsheet
  have hw2 : ((frameAt word).eps - 1) * ((frameAt word).eps + 1) = 0 := by
    linear_combination (frameAt word).eps_sq
  have hε : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1 := by
    rw [← hep]
    rcases mul_eq_zero.mp hw2 with h3 | h3
    · left; linarith
    · right; linarith
  obtain ⟨hz1, hz1', hz2, hz2'⟩ := box_of_closed (frameAt word) z hz ht
  rw [hcd] at hz1'
  rw [hcn] at hz2'
  have ht1 : 1 - (2 * D + dq) ≤ (2 * N + nq) * z.1 - (2 * D + dq) * z.2 := by
    have h5 := ht
    unfold ChildFrame.tGrade at h5
    rw [hcn, hcd] at h5
    exact h5
  have ht2 : (2 * N + nq) * z.1 - (2 * D + dq) * z.2 ≤ (2 * D + dq) + (2 * N + nq) - 1 := by
    obtain ⟨b1, -, -⟩ := closed_bounds (frameAt word) z hz
    rw [hcn, hcd] at b1
    exact b1
  have hph : (frameAt word).phaseW = (1 + (N * dq - nq * D)) / 2 := by
    unfold ChildFrame.phaseW
    rw [hep]
  rw [hsheet, hep]
  rcases hε with hε1 | hε1
  · have hph1 : (frameAt word).phaseW = 1 := by
      rw [hph, hε1]
      norm_num
    rw [hph1, hdiv]
    exact ZoneCase.I1_core_plus (standardField (conjWord word)) N D nq dq Nu Du epsU (k1 - k2 + dq * nq) H hε1
      hdq0 hcq hzs hzev z.1 z.2 hz1 hz1' hz2 hz2' ht1 ht2
  · have hph0 : (frameAt word).phaseW = 0 := by
      rw [hph, hε1]
      norm_num
    rw [hph0, hdiv]
    exact ZoneCase.I1_core_minus (standardField (conjWord word)) N D nq dq Nu Du epsU (k1 - k2 + dq * nq) H hε1
      hdq0 hcq hzs hzev z.1 z.2 hz1 hz1' hz2 hz2' ht1 ht2

end ZoneI1

end FLatticePaper.Induction
