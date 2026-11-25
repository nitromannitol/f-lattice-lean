import FLatticePaper.Plane.Induction.EarlierValues
import FLatticePaper.Plane.Induction.PriceReflect
import FLatticePaper.Plane.Induction.LiftPsi
import FLatticePaper.Plane.Induction.Q3VStar

/-! Task w3, step 2(a) endpoints and the period rule, for the conjugate's frame `C` and field `G`.

The raw slip `Dq C G η z = G z − G (z + η σ')` is taken along the short shift `σ' = C.shortShift`.
* `Dq_transverse`, `Dq_smul_transverse`: the period rule `Dq (z + m V') = Dq z + 2 η m` (height law of the packet, `t(σ') = −2`).
* `Dq_down`, `Dq_diag`: the zero strip gives `Dq = 0` at `(0,−1)` and `(1,−1)`.
* `even_endpoint_period`: an even free-V site with `s = 0` lies on an ordinate in `L'Z` (gcd argument).
* `valOdd`: at the odd lower endpoint `p = vAt j` (`s(p) = 2 − c'`), `Φ'(p) = c₀' + Dq (V'_{j − ε'r'})`. -/

namespace FLatticePaper.EndpointDeck

open Farey FLatticePaper FLatticePaper.Induction

/-- The raw slip `D_η(z) = G z − G (z + η σ')` of the frame's field along its short shift. -/
def Dq (C : ChildFrame) (G : Field) (η : ℤ) (z : Site) : ℤ :=
  G z - G (z + η • C.shortShift)

/-- `den·σ'₂ − num·σ'₁ = 2`, the height of the short shift. -/
theorem den_shortShift_det (C : ChildFrame) :
    C.child.den * C.shortShift.2 - C.child.num * C.shortShift.1 = 2 := by
  have h := C.tGrade_shortShift
  unfold ChildFrame.tGrade at h
  linarith

theorem transverse_eq_Vdeck (C : ChildFrame) : C.child.modifiedDeck.transverse = Vdeck C := by
  rw [PriceReflect.transverse_vec]
  rfl

/-- **The period rule.** `Dq (z + V') = Dq z + 2η`, from the height law `G(z+V') = G z − transverseGrade z + c`. -/
theorem Dq_transverse (C : ChildFrame) {G : Field} (hP : C.Packet G) (η : ℤ) (z : Site) :
    Dq C G η (z + Vdeck C) = Dq C G η z + 2 * η := by
  have hp := hP.periods.2
  have h1 := hp z
  have h2 := hp (z + η • C.shortShift)
  rw [transverse_eq_Vdeck] at h1 h2
  have hσ := den_shortShift_det C
  have e : z + Vdeck C + η • C.shortShift = (z + η • C.shortShift) + Vdeck C := by abel
  unfold Dq
  rw [e, h1, h2]
  unfold Fraction.transverseGrade
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination η * hσ

/-- The period rule for `m` periods. -/
theorem Dq_smul_transverse (C : ChildFrame) {G : Field} (hP : C.Packet G) (η : ℤ) (m : ℤ) (z : Site) :
    Dq C G η (z + m • Vdeck C) = Dq C G η z + 2 * η * m := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ k ih =>
    have e : z + ((k : ℤ) + 1) • Vdeck C = (z + (k : ℤ) • Vdeck C) + Vdeck C := by
      rw [add_smul, one_smul, add_assoc]
    rw [e, Dq_transverse C hP η, ih z]
    ring
  | pred k ih =>
    have e2 : z + (-(k : ℤ) - 1) • Vdeck C + Vdeck C = z + (-(k : ℤ)) • Vdeck C := by
      rw [sub_smul, one_smul]
      abel
    have h1 := Dq_transverse C hP η (z + (-(k : ℤ) - 1) • Vdeck C)
    rw [e2, ih z] at h1
    linear_combination (-1 : ℤ) * h1

/-- The zero strip gives `Dq = 0` when `z` and `z + η σ'` both have `t`-grade in the strip. -/
theorem Dq_zero (C : ChildFrame) {G : Field} (hS : C.HasStrips G) (η : ℤ) (z : Site)
    (h1 : 1 - C.child.den ≤ C.tGrade z) (h2 : C.tGrade z ≤ C.child.num + 2 * C.child.den - 1)
    (h3 : 1 - C.child.den ≤ C.tGrade z - 2 * η) (h4 : C.tGrade z - 2 * η ≤ C.child.num + 2 * C.child.den - 1) :
    Dq C G η z = 0 := by
  have hz := hS.1 z h1 h2
  have hw : C.tGrade (z + η • C.shortShift) = C.tGrade z - 2 * η := by
    have ht := C.tGrade_shortShift
    unfold ChildFrame.tGrade at ht ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination η * ht
  have hw' := hS.1 (z + η • C.shortShift) (by rw [hw]; exact h3) (by rw [hw]; exact h4)
  unfold Dq
  rw [hz, hw']
  ring

/-- At `(0,−1)` the `t`-grade is `d`, and `d − 2η` stays in the strip. -/
theorem Dq_down (C : ChildFrame) {G : Field} (hS : C.HasStrips G) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    Dq C G η (0, -1) = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
  have ht : C.tGrade ((0 : ℤ), (-1 : ℤ)) = C.child.den := by
    unfold ChildFrame.tGrade
    ring
  apply Dq_zero C hS η _ <;> rw [ht] <;> rcases hη with rfl | rfl <;> omega

/-- At `(1,−1)` the `t`-grade is `n + d` (the period), and `n + d − 2η` stays in the strip. -/
theorem Dq_diag (C : ChildFrame) {G : Field} (hS : C.HasStrips G) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    Dq C G η (1, -1) = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, -⟩ := C.child_facts
  have ht : C.tGrade ((1 : ℤ), (-1 : ℤ)) = C.child.num + C.child.den := by
    unfold ChildFrame.tGrade
    ring
  apply Dq_zero C hS η _ <;> rw [ht] <;> rcases hη with rfl | rfl <;> omega

/-- gcd step: `D x + N y = 0` and `x + y` even with `N + D` odd force `y = 2 D m`. -/
theorem gcd_even (N D : ℤ) (hcop : IsCoprime N D) (hD : 0 < D) (hodd : (N + D) % 2 = 1) (x y : ℤ)
    (hs : D * x + N * y = 0) (hev : (x + y) % 2 = 0) : ∃ m : ℤ, y = 2 * D * m := by
  have hdvd : D ∣ N * y := ⟨-x, by linear_combination hs⟩
  obtain ⟨k, hk⟩ := (hcop.symm).dvd_of_dvd_mul_left hdvd
  have hx : x + N * k = 0 := by
    have h0 : D * (x + N * k) = 0 := by
      rw [hk] at hs
      linear_combination hs
    rcases mul_eq_zero.mp h0 with h | h
    · omega
    · exact h
  have hxy : x + y = (D - N) * k := by
    rw [hk]
    linear_combination hx
  have hodd' : Odd (D - N) := Int.odd_iff.mpr (by omega)
  have hevk : Even k := by
    have hE : Even (x + y) := Int.even_iff.mpr hev
    rw [hxy, Int.even_mul] at hE
    rcases hE with h | h
    · exact absurd h (Int.not_even_iff_odd.mpr hodd')
    · exact h
  obtain ⟨t, ht⟩ := hevk
  exact ⟨t, by rw [hk, ht]; ring⟩

/-- Odd form: `D q₁ + N q₂ = −N` with `q₁ + q₂` odd gives `q = (0,−1) + m(−2N, 2D)`. -/
theorem odd_form (N D : ℤ) (hcop : IsCoprime N D) (hD : 0 < D) (hodd : (N + D) % 2 = 1) (q1 q2 : ℤ)
    (hs : D * q1 + N * q2 = -N) (hpar : (q1 + q2) % 2 = 1) :
    ∃ m : ℤ, q1 = -N * (2 * m) ∧ q2 = D * (2 * m) - 1 := by
  have hdvd : D ∣ N * (q2 + 1) := ⟨-q1, by linear_combination hs⟩
  obtain ⟨t, ht⟩ := (hcop.symm).dvd_of_dvd_mul_left hdvd
  have hq1 : q1 = -N * t := by
    have h0 : D * (q1 + N * t) = 0 := by linear_combination hs - N * ht
    rcases mul_eq_zero.mp h0 with h | h
    · omega
    · linarith
  have hE : Even ((D - N) * t) := by
    apply Int.even_iff.mpr
    have e : (D - N) * t = (q1 + q2) + 1 := by linear_combination (-1 : ℤ) * hq1 - ht
    rw [e]
    omega
  have hodd' : ¬ Even (D - N) := Int.not_even_iff_odd.mpr (Int.odd_iff.mpr (by omega))
  have hte : Even t := by
    rcases Int.even_mul.mp hE with h | h
    · exact absurd h hodd'
    · exact h
  obtain ⟨m, hm⟩ := hte
  subst hm
  refine ⟨m, ?_, ?_⟩
  · rw [hq1]
    ring
  · linear_combination ht

/-- **Even endpoint (gcd).** An even site with `s = 0` has ordinate in `L'Z`, `L' = period` of the conjugate. -/
theorem even_zero_period {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (p : Site)
    (hev : EvenSite p) (hs0 : (frameAt (conjWord word)).sGrade p = 0) :
    ∃ m : ℤ, p.2 = m * FreeEnum.period (frameAt (conjWord word)) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hcop := LiftPsi.isCoprime_ND_of_frame (frameAt word)
  have hodd := (frameAt word).valid.odd_parity
  have hD : 0 < (frameAt word).parents.odd.den := by
    obtain ⟨hn0, hnd, hdn, hd3, -⟩ := (frameAt (conjWord word)).child_facts
    omega
  have hs : (frameAt word).parents.odd.den * p.1 + (frameAt word).parents.odd.num * p.2 = 0 := by
    unfold ChildFrame.sGrade at hs0
    rw [hcn, hcd] at hs0
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
    linear_combination hs0
  obtain ⟨m, hm⟩ := gcd_even _ _ hcop hD hodd p.1 p.2 hs (by unfold EvenSite at hev; exact hev)
  refine ⟨m, ?_⟩
  rw [hm, FreeEnum.period, hcn, hcd]
  ring

/-- **Odd lower endpoint.** At an odd site `p = vAt j` with `s(p) = 2 − c'`, the earlier price is the nominal
`c₀' + D_η(V'_{j − ε'r'})`. Both sides are `c₀' + 2ηm`: `p − v' = (0,−1) + m V'` and `V'_{j−ε'r'} = (1,−1) + m V'`. -/
theorem valOdd {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period (frameAt (conjWord word)) →
      base r ∈ (frameAt (conjWord word)).freeV ∧ (base r).2 = r) (j : ℤ)
    (hodd : ¬ EvenSite (FreeEnum.vAt (frameAt (conjWord word)) base j))
    (hlow : (frameAt (conjWord word)).sGrade (FreeEnum.vAt (frameAt (conjWord word)) base j) =
      2 - ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num)) :
    FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
        (frameAt (oddBirthPrefix word)).eps (frameAt word).eps (FreeEnum.vAt (frameAt (conjWord word)) base j) =
      (frameAt (conjWord word)).cutPrice +
        (standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (j - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
              (frameAt (conjWord word)).parents.odd.num))) -
          standardField (conjWord word) (FreeEnum.vAt (frameAt (conjWord word)) base
            (j - (frameAt (conjWord word)).eps * ((frameAt (conjWord word)).parents.odd.den +
              (frameAt (conjWord word)).parents.odd.num)) +
            (frameAt word).eps • (frameAt (conjWord word)).shortShift)) := by
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hcop := LiftPsi.isCoprime_ND_of_frame (frameAt word)
  have hodd0 := (frameAt word).valid.odd_parity
  have hD : 0 < (frameAt word).parents.odd.den := by
    obtain ⟨hn0, hnd, hdn, hd3, -⟩ := (frameAt (conjWord word)).child_facts
    omega
  have hP : (frameAt (conjWord word)).Packet (standardField (conjWord word)) := hSE.packet
  have hηu := (frameAt word).eps_unit
  set C := frameAt (conjWord word) with hC
  set G := standardField (conjWord word) with hG
  set η := (frameAt word).eps with hη
  set N := (frameAt word).parents.odd.num with hN
  set D := (frameAt word).parents.odd.den with hD'
  set p := FreeEnum.vAt C base j with hp
  set v := C.parentShift with hv
  have hpj : p.2 = j := FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2) j
  have hvs : C.sGrade v = 2 := VWindow.sGrade_parentShift C
  -- the shifted site `q = p − v` is odd with `s(q) = −2N`
  have hq_par : ¬ EvenSite (p - v) := by
    intro he
    have hiff := VWindow.evenSite_add_parentShift C (p - v)
    rw [sub_add_cancel] at hiff
    exact hodd (hiff.mpr he)
  have hqs : D * (p - v).1 + N * (p - v).2 = -N := by
    have h1 := hlow
    have h2 := hvs
    unfold ChildFrame.sGrade at h1 h2
    rw [hcn, hcd] at h1 h2
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination h1 - h2
  have hpar : ((p - v).1 + (p - v).2) % 2 = 1 := by
    unfold EvenSite at hq_par
    omega
  obtain ⟨m, hm1, hm2⟩ := odd_form N D hcop hD hodd0 (p - v).1 (p - v).2 hqs hpar
  have hV : Vdeck C = (-2 * N, 2 * D) := by
    unfold Vdeck
    rw [hcn, hcd]
    ext <;> simp <;> ring
  have hq : p - v = (0, -1) + m • Vdeck C := by
    have e1 : ((0 : ℤ), (-1 : ℤ)) + m • Vdeck C = (-N * (2 * m), D * (2 * m) - 1) := by
      rw [hV]
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
      constructor <;> ring
    rw [e1]
    exact Prod.ext hm1 hm2
  have hidx : j - C.eps * (C.parents.odd.den + C.parents.odd.num) = -1 + m * FreeEnum.period C := by
    have hv2 : v.2 = C.eps * (C.parents.odd.num + C.parents.odd.den) := by
      rw [hv]
      unfold ChildFrame.parentShift
      dsimp only
    have hperiod : FreeEnum.period C = 2 * D := by
      unfold FreeEnum.period
      rw [hcn, hcd]
      ring
    have h2 : (p - v).2 = j - v.2 := by
      simp only [Prod.snd_sub, hpj]
    rw [hperiod]
    have : (p - v).2 = D * (2 * m) - 1 := hm2
    linear_combination (-1 : ℤ) * h2 + this + hv2
  have hw1 : (EvenSite ((1 : ℤ), (-1 : ℤ)) →
        0 ≤ C.sGrade ((1 : ℤ), (-1 : ℤ)) ∧ C.sGrade ((1 : ℤ), (-1 : ℤ)) ≤ 2 * C.child.num) ∧
      (¬ EvenSite ((1 : ℤ), (-1 : ℤ)) →
        2 - C.child.den + C.child.num ≤ C.sGrade ((1 : ℤ), (-1 : ℤ)) ∧
          C.sGrade ((1 : ℤ), (-1 : ℤ)) ≤ C.child.den + C.child.num - 2) := by
    have hsq : C.sGrade ((1 : ℤ), (-1 : ℤ)) = 2 * C.child.num := by
      unfold ChildFrame.sGrade
      ring
    obtain ⟨hn0, -, -, -, -⟩ := C.child_facts
    refine ⟨fun _ => ⟨by rw [hsq]; omega, by rw [hsq]⟩, fun hne => absurd ?_ hne⟩
    unfold EvenSite
    norm_num
  have hm1pt : FreeEnum.vAt C base (-1) = ((1 : ℤ), (-1 : ℤ)) := by
    apply VWindow.row_unique C
    · rw [FreeEnum.vAt_snd C base (fun r h0 h1 => (hbase r h0 h1).2)]
    · exact VWindow.vAt_window C base hbase (-1)
    · exact hw1
  have hr : FreeEnum.vAt C base (j - C.eps * (C.parents.odd.den + C.parents.odd.num)) =
      ((1 : ℤ), (-1 : ℤ)) + m • Vdeck C := by
    rw [hidx, EarlierValues.vAt_add_mul_period, hm1pt]
  have hS := hP.strips
  have k1 := Dq_smul_transverse C hP η m (0, -1)
  have k2 := Dq_smul_transverse C hP η m (1, -1)
  have d1 := Dq_down C hS η hηu
  have d2 := Dq_diag C hS η hηu
  unfold Dq at k1 k2 d1 d2
  rw [EarlierV.earlierP_eq_price_add, EarlierV.price_vAt_eq hSE base hbase j, hq, hr]
  linarith

end FLatticePaper.EndpointDeck
