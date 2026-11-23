import FLatticePaper.Plane.Induction.HarmI2
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.ParentStepDischarge

/-! # The frame-level harmonic region of I2 (task 49, the wrapper of the harmonic step)

The other sheet is at least `h₀` on the harmonic band `E ∩ {s ≤ 2L − 1}` of the word, for both signs of `ε`, from the strong
estimates of the earlier conjugate. The parent step `f(u) ≤ f(u − U_q)` is a named input in the form of `ParentStepSign`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper ZoneI1

namespace HarmWrap

/-- The sheet `A` in coordinates: its shift is `(1 − W) U_q`. -/
theorem sheetA_expr (V : ChildFrame) (Fp : Site → ℤ) (z : Site) :
    V.sheetA Fp z = Fp (z.1 - (1 - V.phaseW) * V.parents.even.den, z.2 - (1 - V.phaseW) * V.parents.even.num) := by
  unfold ChildFrame.sheetA ChildFrame.sheetShift Fraction.unmodifiedDeck
  simp only [smul_eq_mul, Prod.smul_mk]
  rfl

/-- The lower bound `1 − T ≤ t` of the closed polygon. -/
theorem closed_lower (V : ChildFrame) (z : Site) (hz : z ∈ V.closedPolygon) :
    1 - V.child.periodDenominator ≤ V.tGrade z := by
  obtain ⟨hn0, -, -, -, -⟩ := V.child_facts
  have h1n : 1 ≤ V.child.num := by omega
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq] at hz
  by_cases he : EvenSite z
  · rw [if_pos he] at hz
    obtain ⟨h1, -⟩ := hz
    linarith
  · rw [if_neg he] at hz
    obtain ⟨h1, -⟩ := hz
    linarith


/-- The other sheet is at least `h₀` on the harmonic band of the word, for both signs of `ε` (the fix's harmonic region):
for `ε = +1` the sheet `C`, for `ε = −1` the sheet `A`. The parent step is the named input `hps` (`ParentStepSign` with the
word's odd parent, discharged from the strong estimates of the conjugate). -/
theorem I2_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word))
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon)
    (hs : (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    ((frameAt word).eps = 1 →
        harmonicGrid z ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z) ∧
    ((frameAt word).eps = -1 →
        harmonicGrid z ≤ (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z) := by
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
  have hps := parentStepSign_of_strong h hS
  unfold ParentStepSign at hps
  have hevQ : (nq + dq) % 2 = 0 := (frameAt word).valid.even_parity
  have hsharm : ∀ y : Site, 1 - 2 * (D + N) ≤ 2 * D * y.1 + 2 * N * y.2 →
      2 * D * y.1 + 2 * N * y.2 ≤ 2 * (2 * D) - 1 → standardField (conjWord word) y = harmonicGrid y := by
    intro y h1 h2
    apply hS.packet.strips.2 y
    · have e : ChildFrame.sGrade (frameAt (conjWord word)) y = 2 * D * y.1 + 2 * N * y.2 := by
        unfold ChildFrame.sGrade
        rw [hr, hb]
        ring
      rw [e, hr]; exact h1
    · have e : ChildFrame.sGrade (frameAt (conjWord word)) y = 2 * D * y.1 + 2 * N * y.2 := by
        unfold ChildFrame.sGrade
        rw [hr, hb]
        ring
      rw [e, hr, hb]; linarith
  have hbin : ∀ c : Site, laplacian (standardField (conjWord word)) c = -1 ∨
      laplacian (standardField (conjWord word)) c = 0 := fun c => hS.packet.binary c
  have hN1 : 1 ≤ N := by
    obtain ⟨hn0, -, hdn, -, -⟩ := ChildFrame.child_facts (frameAt (conjWord word))
    rw [hr, hb] at hdn
    omega
  have hn_geo : 1 ≤ 2 * N + nq := by
    obtain ⟨hn0, -, -, -, -⟩ := ChildFrame.child_facts (frameAt word)
    rw [hcn] at hn0
    omega
  have hnd_geo : 2 * N + nq + 2 ≤ 2 * D + dq := by
    obtain ⟨-, -, hdn, -, -⟩ := ChildFrame.child_facts (frameAt word)
    rw [hcn, hcd] at hdn
    omega
  obtain ⟨b1, b2, -⟩ := closed_bounds (frameAt word) z hz
  rw [hcn, hcd] at b1 b2
  have hlow := closed_lower (frameAt word) z hz
  unfold Fraction.periodDenominator ChildFrame.tGrade at hlow
  rw [hcn, hcd] at hlow
  have hT_geo : 1 - ((2 * D + dq) * (2 * D + dq) + 2 * (2 * D + dq) * (2 * N + nq) - (2 * N + nq) * (2 * N + nq))
      ≤ (2 * N + nq) * z.1 - (2 * D + dq) * z.2 := by
    linarith
  have hD_geo : ((2 * D + dq) + (2 * N + nq)) * z.1 + ((2 * D + dq) - (2 * N + nq)) * z.2
      ≤ 2 * ((2 * D + dq) + (2 * N + nq)) - 1 := by
    unfold ChildFrame.sGrade at hs
    rw [hcn, hcd] at hs
    exact hs
  have hepsW : N * dq - nq * D = 1 ∨ N * dq - nq * D = -1 := by
    have hw2 : (N * dq - nq * D - 1) * (N * dq - nq * D + 1) = 0 := by
      have := (frameAt word).eps_sq
      rw [hep] at this
      linear_combination this
    rcases mul_eq_zero.mp hw2 with h3 | h3
    · left; linarith
    · right; linarith
  have hK' := hK
  constructor
  · intro he1
    have hε1 : N * dq - nq * D = 1 := by rw [← hep]; exact he1
    obtain ⟨hy, hm1, hm2, hbig⟩ := HarmI2.geo_window N D nq dq (2 * N + nq) (2 * D + dq) z.1 z.2 1 rfl rfl
      (Or.inr ⟨rfl, hε1⟩) hN1 hND hn_geo hnd_geo hrodd hT_geo b1 b2 hD_geo
    have hnn := HarmI2.harmR_nonneg (standardField (conjWord word)) N D Nu Du epsU nq dq H hsharm hbin hevQ hps hzs
      (Or.inl hε1) (z.1 - 1 * ((2 * N + nq) - (2 * D + dq)), z.2 - 1 * ((2 * N + nq) + (2 * D + dq)))
      hm1 hm2 hy hbig
    simp only [one_mul] at hnn
    have hid := HarmI2.sheetC_eq_harmR (standardField (conjWord word)) N D nq dq (k1 - k2 + dq * nq) hK hε1
      hcq z
    have hphW1 : (frameAt word).phaseW = 1 := by
      unfold ChildFrame.phaseW
      rw [hep, hε1]
      norm_num
    rw [sheetC_expr, hphW1, hep, ← hnq, ← hdq, hdiv]
    linarith
  · intro he
    have hε1 : N * dq - nq * D = -1 := by rw [← hep]; exact he
    obtain ⟨hy, hm1, hm2, hbig⟩ := HarmI2.geo_window N D nq dq (2 * N + nq) (2 * D + dq) z.1 z.2 0 rfl rfl
      (Or.inl ⟨rfl, hε1⟩) hN1 hND hn_geo hnd_geo hrodd hT_geo b1 b2 hD_geo
    simp only [zero_mul, sub_zero] at hy hm1 hm2 hbig
    have hnn := HarmI2.harmR_nonneg (standardField (conjWord word)) N D Nu Du epsU nq dq H hsharm hbin hevQ hps hzs
      (Or.inr hε1) z hm1 hm2 hy hbig
    have hphW0 : (frameAt word).phaseW = 0 := by
      unfold ChildFrame.phaseW
      rw [hep, hε1]
      norm_num
    have key := HarmI2.sheetA_eq_harmR (standardField (conjWord word)) dq nq z
    rw [HarmWrap.sheetA_expr, hphW0, ← hnq, ← hdq]
    linarith

end HarmWrap

end FLatticePaper.Induction
