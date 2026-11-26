import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.SheetDifference
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.Bands
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StrongInduction
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.CrossingLattice
import FLatticePaper.Plane.Induction.SeedTransverse
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.SheetOffsets

/-! # The cross-branch identity for the sheet `C` at the child's transverse vector (audit section 1)

For the word `w` with child `(n, d)`, transverse `V = (n - d, n + d)`, kernel `K = (d, n)`, sign `ε`, sheet shift `lv`
and offset `e`, the identity (checked numerically for all tested words)

  `C(y + V) = Fp(y − ε K − lv) + (n y₁ − d y₂) + cV`,

where `Fp = quarterTurnField (standardField (conjWord w))`, `C = sheetC Fp`, `cV` the coherent constant of `w`.
It follows from the two periods of the conjugate field along its kernel `K'` and transverse `V'`, since
`Z(y + V − lv − e) − Z(y − εK − lv) = −2 K' + ε V'`, with `K' = (d', n')`, `V' = (n' − d', n' + d')`.

Here `G = standardField (conjWord w)` and its periods come from the conjugate packet. -/

namespace FLatticePaper.HtopCross

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1 Farey

/-- The periods of the conjugate standard field along the conjugate child's kernel and transverse vector. -/
theorem conj_periods {word : Word} (hSE : StrongEstimates (conjWord word)) :
    (∀ s : Site, standardField (conjWord word) (s + ((frameAt (conjWord word)).child.den,
        (frameAt (conjWord word)).child.num)) =
      standardField (conjWord word) s + (frameAt (conjWord word)).coherentConstantU) ∧
    (∀ s : Site, standardField (conjWord word) (s + ((frameAt (conjWord word)).child.num -
        (frameAt (conjWord word)).child.den, (frameAt (conjWord word)).child.num +
        (frameAt (conjWord word)).child.den)) =
      standardField (conjWord word) s -
        ((frameAt (conjWord word)).child.den * s.2 - (frameAt (conjWord word)).child.num * s.1) +
        (frameAt (conjWord word)).coherentConstantV) := by
  have hP := hSE.packet.periods
  obtain ⟨h1, h2⟩ := hP
  refine ⟨fun s => ?_, fun s => ?_⟩
  · have := h1 s
    rw [StripColours.kernel_eq] at this
    exact this
  · have := h2 s
    rw [StripColours.transverse_eq] at this
    unfold Fraction.transverseGrade at this
    exact this

/-! ## The conjugate period steps, for the conjugate kernel `(dp, np)` and transverse `(np - dp, np + dp)` -/

/-- The shift `(np - 3dp, dp - np)`, that is `-2K' + V'`: the `ε = +1` step. -/
theorem period_eps_plus (G : Site → ℤ) (dp np U V : ℤ)
    (hK : ∀ s : Site, G (s + (dp, np)) = G s + U)
    (hT : ∀ s : Site, G (s + (np - dp, np + dp)) = G s - (dp * s.2 - np * s.1) + V) (w : Site) :
    G (w + (np - 3 * dp, dp - np)) = G w - 2 * U - (dp * w.2 - np * w.1) + V := by
  have hKm : ∀ s : Site, G (s - (dp, np)) = G s - U := by
    intro s
    have h := hK (s - (dp, np))
    rw [sub_add_cancel] at h
    linarith
  have hK2 : ∀ s : Site, G (s - (2 * dp, 2 * np)) = G s - 2 * U := by
    intro s
    have a := hKm (s - (dp, np))
    have b := hKm s
    have e : s - (dp, np) - (dp, np) = s - (2 * dp, 2 * np) := by
      ext <;> simp <;> ring
    rw [e] at a
    linarith
  have e2 : w + (np - 3 * dp, dp - np) = (w - (2 * dp, 2 * np)) + (np - dp, np + dp) := by
    ext <;> simp <;> ring
  rw [e2, hT, hK2]
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The shift `(-dp - np, -3np - dp)`, that is `-2K' - V'`: the `ε = −1` step. -/
theorem period_eps_minus (G : Site → ℤ) (dp np U V : ℤ)
    (hK : ∀ s : Site, G (s + (dp, np)) = G s + U)
    (hT : ∀ s : Site, G (s + (np - dp, np + dp)) = G s - (dp * s.2 - np * s.1) + V) (w : Site) :
    G (w + (-dp - np, -3 * np - dp)) =
      G w - 2 * U + (dp * w.2 - np * w.1) - (dp ^ 2 + 2 * dp * np - np ^ 2) - V := by
  have hKm : ∀ s : Site, G (s - (dp, np)) = G s - U := by
    intro s
    have h := hK (s - (dp, np))
    rw [sub_add_cancel] at h
    linarith
  have hK2 : ∀ s : Site, G (s - (2 * dp, 2 * np)) = G s - 2 * U := by
    intro s
    have a := hKm (s - (dp, np))
    have b := hKm s
    have e : s - (dp, np) - (dp, np) = s - (2 * dp, 2 * np) := by
      ext <;> simp <;> ring
    rw [e] at a
    linarith
  have hs := hT (w - (2 * dp, 2 * np) + (dp - np, -np - dp))
  have e3 : w - (2 * dp, 2 * np) + (dp - np, -np - dp) + (np - dp, np + dp) = w - (2 * dp, 2 * np) := by
    ext <;> simp <;> ring
  rw [e3, hK2] at hs
  have e4 : w + (-dp - np, -3 * np - dp) = w - (2 * dp, 2 * np) + (dp - np, -np - dp) := by
    ext <;> simp <;> ring
  rw [e4]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hs ⊢
  linarith


/-! ## The cross-branch identity, the `ε = +1` case (in the parent integers) -/

/-- **The cross-branch identity at `ε = +1`** (with `lv = 0`, `e = (nq, 2nq + dq)`, `K = (d, n)`, `V = (n − d, n + d)`). -/
theorem core_plus (G : Site → ℤ) (n d nq dq No Do Vc cV ce : ℤ)
    (hn : n = 2 * No + nq) (hd : d = 2 * Do + dq)
    (hK : ∀ s : Site, G (s + (Do + No, Do - No)) = G s)
    (hT : ∀ s : Site, G (s + ((Do - No) - (Do + No), (Do - No) + (Do + No))) =
      G s - ((Do + No) * s.2 - (Do - No) * s.1) + Vc)
    (hVc : 2 * Vc = -(((Do + No) ^ 2 + 2 * (Do + No) * (Do - No) - (Do - No) ^ 2) + ((Do + No) + (Do - No))))
    (hcV : 2 * cV = -((d * d + 2 * d * n - n * n) + (d + n)))
    (hce : 2 * ce = (dq * dq + 2 * dq * nq - nq * nq) - dq - nq + 4)
    (hdet : No * dq - Do * nq = 1)
    (y : Site) :
    G (-(y.2 + (n + d) - (2 * nq + dq)), y.1 + (n - d) - nq - 1) +
        harmonicGrid (y.1 + (n - d) - nq, y.2 + (n + d) - (2 * nq + dq)) +
        (nq * (y.1 + (n - d)) - dq * (y.2 + (n + d))) + ce =
      G (-(y.2 - n), y.1 - d - 1) + harmonicGrid (y.1 - d, y.2 - n) + (n * y.1 - d * y.2) + cV := by
  have hK' : ∀ s : Site, G (s + (Do + No, Do - No)) = G s + 0 := fun s => by rw [hK s]; ring
  have hA := period_eps_plus G (Do + No) (Do - No) 0 Vc hK' hT (-(y.2 - n), y.1 - d - 1)
  have hAeq : (-(y.2 + (n + d) - (2 * nq + dq)), y.1 + (n - d) - nq - 1) =
      (-(y.2 - n), y.1 - d - 1) + ((Do - No) - 3 * (Do + No), (Do + No) - (Do - No)) := by
    subst hn hd
    ext <;> simp <;> ring
  rw [hAeq, hA]
  have h4B := harmonicGrid_exact (y.1 + (n - d) - nq, y.2 + (n + d) - (2 * nq + dq))
  have h4D := harmonicGrid_exact (y.1 - d, y.2 - n)
  have hpar : ((y.1 + (n - d) - nq) + (y.2 + (n + d) - (2 * nq + dq))) % 2 = ((y.1 - d) + (y.2 - n)) % 2 := by
    subst hn hd
    omega
  rw [hpar] at h4B
  dsimp only at hA h4B h4D ⊢
  subst hn hd
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination h4B - h4D + 2 * hVc + 2 * hce - 2 * hcV - 8 * hdet


/-! ## The cross-branch identity, the `ε = −1` case (in the parent integers) -/

/-- **The cross-branch identity at `ε = −1`** (with `lv = (dq, nq)`, `e = (nq − 2dq, dq)`, `K = (d, n)`, `V = (n − d, n + d)`). -/
theorem core_minus (G : Site → ℤ) (n d nq dq No Do Vc cV ce : ℤ)
    (hn : n = 2 * No + nq) (hd : d = 2 * Do + dq)
    (hK : ∀ s : Site, G (s + (Do + No, Do - No)) = G s)
    (hT : ∀ s : Site, G (s + ((Do - No) - (Do + No), (Do - No) + (Do + No))) =
      G s - ((Do + No) * s.2 - (Do - No) * s.1) + Vc)
    (hVc : 2 * Vc = -(((Do + No) ^ 2 + 2 * (Do + No) * (Do - No) - (Do - No) ^ 2) + ((Do + No) + (Do - No))))
    (hcV : 2 * cV = -((d * d + 2 * d * n - n * n) + (d + n)))
    (hce : 2 * ce = (dq * dq + 2 * dq * nq - nq * nq) - dq - nq)
    (y : Site) :
    G (-(y.2 + (n + d) - nq - dq), y.1 + (n - d) + dq - nq - 1) +
        harmonicGrid (y.1 + (n - d) + dq - nq, y.2 + (n + d) - nq - dq) +
        (nq * (y.1 + (n - d) - dq) - dq * (y.2 + (n + d) - nq)) + ce =
      G (-(y.2 + n - nq), y.1 + d - dq - 1) + harmonicGrid (y.1 + d - dq, y.2 + n - nq) +
        (n * y.1 - d * y.2) + cV := by
  have hK' : ∀ s : Site, G (s + (Do + No, Do - No)) = G s + 0 := fun s => by rw [hK s]; ring
  have hA := period_eps_minus G (Do + No) (Do - No) 0 Vc hK' hT (-(y.2 + n - nq), y.1 + d - dq - 1)
  have hAeq : (-(y.2 + (n + d) - nq - dq), y.1 + (n - d) + dq - nq - 1) =
      (-(y.2 + n - nq), y.1 + d - dq - 1) + (-((Do + No) : ℤ) - (Do - No), -3 * (Do - No) - (Do + No)) := by
    subst hn hd
    ext <;> simp <;> ring
  rw [hAeq, hA]
  have h4B := harmonicGrid_exact (y.1 + (n - d) + dq - nq, y.2 + (n + d) - nq - dq)
  have h4D := harmonicGrid_exact (y.1 + d - dq, y.2 + n - nq)
  have hpar : ((y.1 + (n - d) + dq - nq) + (y.2 + (n + d) - nq - dq)) % 2 =
      ((y.1 + d - dq) + (y.2 + n - nq)) % 2 := by
    subst hn hd
    omega
  rw [hpar] at h4B
  dsimp only at h4B h4D ⊢
  subst hn hd
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination h4B - h4D - 2 * hVc + 2 * hce - 2 * hcV




/-! ## The frame-level cross-branch identity (both signs) -/

/-- Subtraction of a pair literal, componentwise. -/
theorem site_sub_pair (y : Site) (a b : ℤ) : y - (a, b) = (y.1 - a, y.2 - b) := rfl

/-- Addition of a pair literal, componentwise. -/
theorem site_add_pair (y : Site) (a b : ℤ) : y + (a, b) = (y.1 + a, y.2 + b) := rfl



/-- The quarter-turn field as the conjugate field at the quarter turn plus the harmonic grid. -/
theorem qtf_eq (F : Site → ℤ) (x : Site) :
    quarterTurnField F x = F (-x.2, x.1 - 1) + harmonicGrid x := by
  have h := FLatticePaper.Induction.ZoneCase.qtf_sub_h0 F x
  linarith

/-- The shared data of the cross-branch identity: the conjugate periods in the parent integers `(No, Do) = (odd.num, odd.den)`,
the conjugate constant and the word constant in closed form. -/
theorem cross_common {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    (∀ s : Site, standardField (conjWord word) (s + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num,
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num)) =
      standardField (conjWord word) s) ∧
    (∀ s : Site, standardField (conjWord word) (s + (((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num),
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) +
          ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))) =
      standardField (conjWord word) s - (((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * s.2 -
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * s.1) +
        (frameAt (conjWord word)).coherentConstantV) ∧
    2 * (frameAt (conjWord word)).coherentConstantV =
      -((((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) ^ 2 +
        2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) *
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) -
        ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) ^ 2) +
        (((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) +
          ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num))) ∧
    2 * (frameAt word).coherentConstantV =
      -(((frameAt word).child.den ^ 2 + 2 * (frameAt word).child.den * (frameAt word).child.num -
        (frameAt word).child.num ^ 2) + ((frameAt word).child.den + (frameAt word).child.num)) := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  have hP := conj_periods hSE
  rw [FLatticePaper.Induction.coherentConstantU_eq_zero, hcn, hcd] at hP
  obtain ⟨hP1, hP2⟩ := hP
  obtain ⟨hcnO, hcdO⟩ := (frameAt (conjWord word)).child_odd
  obtain ⟨hnO, hdO⟩ := (frameAt word).child_odd
  -- the conjugate constant
  have hTc : ((frameAt (conjWord word)).child.den ^ 2 + 2 * (frameAt (conjWord word)).child.den *
      (frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.num ^ 2) % 2 = 0 := by
    have := FLatticePaper.CrossingLattice.parity_w1T hcnO hcdO
    unfold FLatticePaper.W1.w1T at this
    exact this
  have hVc2 : 2 * (frameAt (conjWord word)).coherentConstantV =
      -((((frameAt (conjWord word)).child.den ^ 2 + 2 * (frameAt (conjWord word)).child.den *
        (frameAt (conjWord word)).child.num - (frameAt (conjWord word)).child.num ^ 2) +
        ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num))) := by
    have hL : ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) % 2 = 0 := by omega
    have hdiv : 2 ∣ (frameAt (conjWord word)).child.periodDenominator +
        ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) :=
      Int.dvd_of_emod_eq_zero (by unfold Fraction.periodDenominator; omega)
    rw [FLatticePaper.Induction.SeedTransverse.coherentConstantV_eq _ hL hTc, mul_neg,
      Int.mul_ediv_cancel' hdiv]
    rfl
  -- the word's constant
  have hTw : ((frameAt word).child.den ^ 2 + 2 * (frameAt word).child.den * (frameAt word).child.num -
      (frameAt word).child.num ^ 2) % 2 = 0 := by
    have := FLatticePaper.CrossingLattice.parity_w1T hnO hdO
    unfold FLatticePaper.W1.w1T at this
    exact this
  have hcVc : 2 * (frameAt word).coherentConstantV =
      -(((frameAt word).child.den ^ 2 + 2 * (frameAt word).child.den * (frameAt word).child.num -
        (frameAt word).child.num ^ 2) + ((frameAt word).child.den + (frameAt word).child.num)) := by
    have hL : ((frameAt word).child.den + (frameAt word).child.num) % 2 = 0 := by omega
    have hdiv : 2 ∣ (frameAt word).child.periodDenominator +
        ((frameAt word).child.den + (frameAt word).child.num) :=
      Int.dvd_of_emod_eq_zero (by unfold Fraction.periodDenominator; omega)
    rw [FLatticePaper.Induction.SeedTransverse.coherentConstantV_eq _ hL hTw, mul_neg,
      Int.mul_ediv_cancel' hdiv]
    rfl
  refine ⟨fun s => by rw [hP1 s, add_zero], hP2, ?_, hcVc⟩
  rw [hcn, hcd] at hVc2
  exact hVc2

/-- The parent's `2 c_e` for the even parent (the sheet constant with `W`). -/
theorem sheetConstant_twice (word : Word) (W : ℤ) (hW : (frameAt word).phaseW = W)
    (_hW01 : W = 0 ∨ W = 1) (hodd : (frameAt word).parents.even.num % 2 = 1 ∧
      (frameAt word).parents.even.den % 2 = 1) :
    2 * (frameAt word).sheetConstant = ((frameAt word).parents.even.den * (frameAt word).parents.even.den +
        2 * (frameAt word).parents.even.den * (frameAt word).parents.even.num -
        (frameAt word).parents.even.num * (frameAt word).parents.even.num -
        (frameAt word).parents.even.den - (frameAt word).parents.even.num) + 4 * W := by
  obtain ⟨hnq, hdq⟩ := hodd
  have hT : ((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den *
      (frameAt word).parents.even.num - (frameAt word).parents.even.num ^ 2) % 2 = 0 := by
    have := FLatticePaper.CrossingLattice.parity_w1T hnq hdq
    unfold FLatticePaper.W1.w1T at this
    exact this
  have hX : (((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den *
      (frameAt word).parents.even.num - (frameAt word).parents.even.num ^ 2) -
      (frameAt word).parents.even.den - (frameAt word).parents.even.num) % 2 = 0 := by
    omega
  unfold ChildFrame.sheetConstant
  rw [hW]
  unfold Fraction.periodDenominator
  have h2 : 2 * ((((frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den *
      (frameAt word).parents.even.num - (frameAt word).parents.even.num ^ 2) -
      (frameAt word).parents.even.den - (frameAt word).parents.even.num) / 2) =
      (frameAt word).parents.even.den ^ 2 + 2 * (frameAt word).parents.even.den *
      (frameAt word).parents.even.num - (frameAt word).parents.even.num ^ 2 -
      (frameAt word).parents.even.den - (frameAt word).parents.even.num :=
    Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hX)
  linear_combination h2

/-- **The cross-branch identity for the sheet `C` at the child's transverse vector, `ε = +1`.** -/
theorem sheetC_cross_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hε : (frameAt word).eps = 1) (y : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
        (y + (frameAt word).child.modifiedDeck.transverse) =
      quarterTurnField (standardField (conjWord word)) (y - (frameAt word).child.modifiedDeck.kernel) +
        ((frameAt word).child.num * y.1 - (frameAt word).child.den * y.2) +
        (frameAt word).coherentConstantV := by
  have hn := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  have hdet : (frameAt word).parents.odd.num * (frameAt word).parents.even.den -
      (frameAt word).parents.odd.den * (frameAt word).parents.even.num = 1 := by
    have := FLatticePaper.SheetOffsets.eps_eq_det (word := word)
    rw [hε] at this
    omega
  obtain ⟨hK, hT, hVc, hcV⟩ := cross_common h hSE
  have hW : (frameAt word).phaseW = 1 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hnq : (frameAt word).parents.even.num % 2 = 1 := by
    obtain ⟨hnO, -⟩ := (frameAt word).child_odd
    omega
  have hdq : (frameAt word).parents.even.den % 2 = 1 := by
    obtain ⟨-, hdO⟩ := (frameAt word).child_odd
    omega
  have hce := sheetConstant_twice word 1 hW (Or.inr rfl) ⟨hnq, hdq⟩
  have key := core_plus (standardField (conjWord word)) (frameAt word).child.num (frameAt word).child.den
    (frameAt word).parents.even.num (frameAt word).parents.even.den
    (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (frameAt (conjWord word)).coherentConstantV (frameAt word).coherentConstantV (frameAt word).sheetConstant
    hn hd hK hT hVc (by linear_combination hcV) (by linear_combination hce) hdet y
  unfold ChildFrame.sheetC ChildFrame.sheetShift ChildFrame.sheetOffset ChildFrame.siblingSlope
    Fraction.unmodifiedDeck
  simp only [hW, hε, smul_eq_mul, Prod.smul_mk, Prod.fst_sub, Prod.snd_sub, Prod.mk_add_mk]
  rw [ChildFrame.child_modifiedDeck_transverse, ChildFrame.child_modifiedDeck_kernel]
  simp only [qtf_eq, site_sub_pair, site_add_pair]
  ring_nf at key ⊢
  linarith

/-- **The cross-branch identity for the sheet `C` at the child's transverse vector, `ε = −1`.** -/
theorem sheetC_cross_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hε : (frameAt word).eps = -1) (y : Site) :
    (frameAt word).sheetC (quarterTurnField (standardField (conjWord word)))
        (y + (frameAt word).child.modifiedDeck.transverse) =
      quarterTurnField (standardField (conjWord word))
          (y + (frameAt word).child.modifiedDeck.kernel -
            ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) +
        ((frameAt word).child.num * y.1 - (frameAt word).child.den * y.2) +
        (frameAt word).coherentConstantV := by
  have hn := FLatticePaper.Induction.ZoneI1.child_num_eq (frameAt word)
  have hd := FLatticePaper.Induction.ZoneI1.child_den_eq (frameAt word)
  obtain ⟨hK, hT, hVc, hcV⟩ := cross_common h hSE
  have hW : (frameAt word).phaseW = 0 := by
    unfold ChildFrame.phaseW
    rw [hε]
    norm_num
  have hnq : (frameAt word).parents.even.num % 2 = 1 := by
    obtain ⟨hnO, -⟩ := (frameAt word).child_odd
    omega
  have hdq : (frameAt word).parents.even.den % 2 = 1 := by
    obtain ⟨-, hdO⟩ := (frameAt word).child_odd
    omega
  have hce := sheetConstant_twice word 0 hW (Or.inl rfl) ⟨hnq, hdq⟩
  have key := core_minus (standardField (conjWord word)) (frameAt word).child.num (frameAt word).child.den
    (frameAt word).parents.even.num (frameAt word).parents.even.den
    (frameAt word).parents.odd.num (frameAt word).parents.odd.den
    (frameAt (conjWord word)).coherentConstantV (frameAt word).coherentConstantV (frameAt word).sheetConstant
    hn hd hK hT hVc (by linear_combination hcV) (by linear_combination hce) y
  unfold ChildFrame.sheetC ChildFrame.sheetShift ChildFrame.sheetOffset ChildFrame.siblingSlope
    Fraction.unmodifiedDeck
  simp only [hW, hε, smul_eq_mul, Prod.smul_mk, Prod.fst_sub, Prod.snd_sub, Prod.mk_add_mk]
  rw [ChildFrame.child_modifiedDeck_transverse, ChildFrame.child_modifiedDeck_kernel]
  simp only [qtf_eq, site_sub_pair, site_add_pair]
  ring_nf at key ⊢
  linarith

end FLatticePaper.HtopCross
