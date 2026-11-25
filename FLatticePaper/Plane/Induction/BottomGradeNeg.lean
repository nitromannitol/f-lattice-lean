import FLatticePaper.Plane.Induction.BottomGrade
import FLatticePaper.Plane.Induction.NegTieHCutFinal

/-! # The bottom face (`ε = −1`): a free H point's conjugate image is free up to a deck translate

For a physical free H point `z` with `ε = −1`, the shift is `lv = (Q, P)` (`sheetShift_eps_neg_one`: the even parent's
denominator and numerator), so the conjugate point is `zTurn u` with `u = z − lv`. Write `N, D` for the odd parent,
`P, Q` for the even parent (`N Q − P D = −1`), `L = d + n`, `T_q = D² + 2DN − N²`, `C = D L + N (d − n)`, `t = t(z)`,
`m = z₁ + z₂`, and `A = t_p(u)`, `b = s_p(u)`.

* `A = t_p(z) + 1` and `L · A = (N + D) · t + (L − m)` (the key identity with `ε = −1`);
* `b = T_q (t + 2) − C · A` (the `s`-identity at the shift);
* `C (N + D) = T_q L − 2N`.

Unlike `ε = +1` there is no exceptional site: `N ≤ A ≤ D` on odd `z`, and `1 ≤ A ≤ N + D` on even `z`, with the conjugate H
witness only at `A = N + D`. The witness rule is the `ε = +1` one (`BottomGrade`), checked numerically (eps = -1, words of length
at most 3: every free H point has a conjugate witness with translate index `0`; H iff `A = N + D` on even `z`). -/

namespace FLatticePaper.BottomGradeNeg

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CollarBottomCases
  FLatticePaper.BottomGrade

/-- The `b`-identity at the shift: `s_p(z − (Q,P)) = T_q (t + 2) − C · A`, when `N Q − P D = −1`. -/
theorem neg_b_id (N D P Q n d z1 z2 Tq : ℤ) (hPQ : N * Q - P * D = -1) (hn : n = 2 * N + P) (hd : d = 2 * D + Q)
    (hTq : Tq = D ^ 2 + 2 * D * N - N ^ 2) :
    (D + N) * (z1 - Q) + (D - N) * (z2 - P) =
      Tq * ((n * z1 - d * z2) + 2) - (D * (d + n) + N * (d - n)) * (N * (z1 - Q) - D * (z2 - P)) := by
  subst hn hd hTq
  linear_combination (-2 * D ^ 2 - 4 * D * N - D * P - D * Q + D * z1 + D * z2 + 2 * N ^ 2 + N * P - N * Q + N * z1
    - N * z2) * hPQ

/-- The identity `C (N + D) = T_q L − 2N` (`ε = −1`). -/
theorem neg_C_id (N D P Q n d Tq : ℤ) (hPQ : N * Q - P * D = -1) (hn : n = 2 * N + P) (hd : d = 2 * D + Q)
    (hTq : Tq = D ^ 2 + 2 * D * N - N ^ 2) :
    (D * (d + n) + N * (d - n)) * (N + D) = Tq * (d + n) - 2 * N := by
  subst hn hd hTq
  linear_combination (2 * N) * hPQ

/-- The key identity at the shift: `L · t_p(z − (Q,P)) = (N + D) t + (L − m)` (`ε = −1`). -/
theorem neg_key_id (N D P Q n d z1 z2 : ℤ) (hPQ : N * Q - P * D = -1)
    (key : (d + n) * (N * z1 - D * z2) = (N + D) * (n * z1 - d * z2) + (-1) * (z1 + z2)) :
    (d + n) * (N * (z1 - Q) - D * (z2 - P)) = (N + D) * (n * z1 - d * z2) + ((d + n) - (z1 + z2)) := by
  linear_combination key - (d + n) * hPQ

/-- Integer core, even sites with `ε = −1`: `a ≤ N + D` from `t ≤ L − 2` and `m ≤ L`. -/
theorem even_upper_neg {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 < N + D)
    (key : (d + n) * a = (N + D) * t + m) (ht : t ≤ d + n - 2) (hm : m ≤ d + n) : a ≤ N + D := by
  by_contra h
  rw [not_le] at h
  have h1 : (d + n) * (N + D + 1) ≤ (d + n) * a := mul_le_mul_of_nonneg_left (by omega) hL.le
  have h2 : (N + D) * t ≤ (N + D) * (d + n - 2) := mul_le_mul_of_nonneg_left ht hND.le
  nlinarith

/-- Integer core, odd sites with `ε = −1`: `N ≤ a` from `t ≥ n` and `m ≥ 0`. -/
theorem odd_lower_neg {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 ≤ N + D) (hε : N * d - D * n = -1)
    (key : (d + n) * a = (N + D) * t + m) (ht : n ≤ t) (hm : 0 ≤ m) : N ≤ a := by
  have e : (d + n) * N = (N + D) * n - 1 := by linear_combination hε
  have h3 : (N + D) * n ≤ (N + D) * t := mul_le_mul_of_nonneg_left ht hND
  have h4 : (d + n) * N ≤ (d + n) * a := by rw [key, e]; linarith
  exact le_of_mul_le_mul_left h4 hL

/-- Integer core, odd sites with `ε = −1`: `a ≤ D` (no exceptional value) from `t ≤ d` and `m ≤ L`. -/
theorem odd_upper_neg {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 ≤ N + D) (hε : N * d - D * n = -1)
    (key : (d + n) * a = (N + D) * t + m) (ht : t ≤ d) (hm : m ≤ d + n) : a ≤ D := by
  have e : (d + n) * (D + 1) = (N + D) * d + (d + n) + 1 := by linear_combination (-1 : ℤ) * hε
  have h3 : (N + D) * t ≤ (N + D) * d := mul_le_mul_of_nonneg_left ht hND
  have h4 : (d + n) * a < (d + n) * (D + 1) := by rw [key, e]; linarith
  have h5 : a < D + 1 := lt_of_mul_lt_mul_left h4 hL.le
  omega

/-- **The bottom-face conjugate image is not nonfree** (`ε = −1`, `z` a free H point; no exception). -/
theorem bottom_not_nonfree_neg (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = -1) {z : Site} (hz : z ∈ (frameAt word).freeH) :
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (z - (frameAt word).sheetShift)) := by
  rw [sheetShift_eps_neg_one (frameAt word) hε]
  intro hN
  have hgrades : ∀ X : ChildFrame, ∀ q : Site, X.tGrade q = w1t X.child.num X.child.den q ∧
      X.sGrade q = w1s X.child.num X.child.den q ∧
        X.child.periodDenominator = w1T X.child.num X.child.den := by
    intro X q
    refine ⟨rfl, rfl, ?_⟩
    unfold Fraction.periodDenominator w1T
    rfl
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  obtain ⟨hnodd, hdodd⟩ := (frameAt word).child_odd
  obtain ⟨hdL, hnL, -, -, -, -, -, -, hparL⟩ := (frameAt word).linear_facts
  have hPQ0 := (frameAt word).eps_det_even
  rw [hε] at hPQ0
  have hεN0 := (frameAt word).odd_det_child
  rw [hε] at hεN0
  obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
    (frameAt_conj_child hw)
  obtain ⟨hGpos, hGlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
  obtain ⟨hGodd, -⟩ := (frameAt (conjWord word)).child_odd
  obtain ⟨hDpos, hN0, -⟩ := (frameAt word).valid.odd_bounds
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
  set P := (frameAt word).parents.even.num with hPdef
  set Q := (frameAt word).parents.even.den with hQdef
  set n := (frameAt word).child.num with hndef
  set d := (frameAt word).child.den with hddef
  have hNpos : 0 < N := by
    rw [hGn, hGd] at hGlt
    linarith
  have hDN : 0 < D - N := by rw [← hGn]; exact hGpos
  have hNDpos : 0 < N + D := by linarith
  have hD2 : 2 ≤ D := by linarith
  have hGlt' : (0 : ℤ) < d + n := by omega
  have hGodd' : (D - N) % 2 = 1 := by rw [← hGn]; exact hGodd
  obtain ⟨Tq, hTqdef⟩ : ∃ T : ℤ, T = D ^ 2 + 2 * D * N - N ^ 2 := ⟨_, rfl⟩
  have hTq : 0 < Tq := by rw [hTqdef]; nlinarith
  have hPer : (frameAt (conjWord word)).child.periodDenominator = 2 * Tq := by
    rw [(hgrades (frameAt (conjWord word)) 0).2.2, hGn, hGd]
    unfold w1T
    rw [hTqdef]
    ring
  have hTw : w1T (D - N) (D + N) = 2 * Tq := by
    have h := (hgrades (frameAt (conjWord word)) 0).2.2
    rw [hGn, hGd] at h
    rw [← h, hPer]
  have hnL' : n = 2 * N + P := hnL
  have hdL' : d = 2 * D + Q := hdL
  have hCN : (D * (d + n) + N * (d - n)) * (N + D) = Tq * (d + n) - 2 * N :=
    neg_C_id N D P Q n d Tq hPQ0 hnL' hdL' hTqdef
  -- the key identity and the `s`-identity, at the shifted point `u = z − (Q, P)`
  have hkey0 : (d + n) * (N * z.1 - D * z.2) = (D + N) * (n * z.1 - d * z.2) + (-1) * (z.1 + z.2) := by
    have h := (frameAt word).key_identity_tp z
    rw [hε] at h
    exact h
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = N * (z.1 - Q) - D * (z.2 - P) := ⟨_, rfl⟩
  have hkeyA : (d + n) * A = (N + D) * w1t n d z + ((d + n) - (z.1 + z.2)) := by
    rw [hA]
    unfold w1t
    exact neg_key_id N D P Q n d z.1 z.2 hPQ0 (by linear_combination hkey0)
  set u : Site := z - (Q, P) with hudef
  have hu1 : u.1 = z.1 - Q := rfl
  have hu2 : u.2 = z.2 - P := rfl
  obtain ⟨bu, hbu⟩ : ∃ b : ℤ, b = (D + N) * (z.1 - Q) + (D - N) * (z.2 - P) := ⟨_, rfl⟩
  have hbI : bu = Tq * (w1t n d z + 2) - (D * (d + n) + N * (d - n)) * A := by
    rw [hbu, hA]
    unfold w1t
    exact neg_b_id N D P Q n d z.1 z.2 Tq hPQ0 hnL' hdL' hTqdef
  have hEvU : EvenSite u ↔ EvenSite z := by
    unfold EvenSite
    rw [hu1, hu2]
    constructor <;> intro h <;> omega
  -- the physical free H data of `z`
  have hpar_t : w1t n d z % 2 = (z.1 + z.2) % 2 := t_parity n d z.1 z.2 hnodd hdodd
  obtain ⟨hcl, -, hsp⟩ := (FLatticePaper.W1CollarFrame.freeH_iff (frameAt word) z).mp hz
  have hsp' := hsp
  unfold hSp at hsp'
  have hcl' := hcl
  unfold closedRect at hcl'
  -- the translates `p = zTurn u + combine 0 j` in the conjugate frame
  have hT_p : ∀ j : ℤ, w1t (D - N) (D + N) (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)
      = (D + N - bu) - j * (2 * Tq) := by
    intro j
    have hgp := (hgrades (frameAt (conjWord word))
      (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)).1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.tGrade_add_combine (frameAt (conjWord word)) (zTurn u) 0 j
    have e2 : (frameAt (conjWord word)).tGrade (zTurn u) = D + N - bu := by
      rw [hbu]
      exact conj_tGrade_zTurn hw u
    rw [← hgp, e1, e2, hPer]
  have hS_p : ∀ j : ℤ, w1s (D - N) (D + N) (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)
      = 2 * (A - N) := by
    intro j
    have hgp := (hgrades (frameAt (conjWord word))
      (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)).2.1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.sGrade_add_combine (frameAt (conjWord word)) (zTurn u) 0 j
    have e2 : (frameAt (conjWord word)).sGrade (zTurn u) = 2 * (A - N) := by
      rw [hA]
      exact conj_sGrade_zTurn hw u
    rw [← hgp, e1, e2]
    ring
  have hex : ∃ j : ℤ, zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j ∈
      (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
    by_cases he : EvenSite z
    · -- even `z`: `1 ≤ A ≤ N + D`, H witness at `A = N + D`, V witness below
      have hzE : (z.1 + z.2) % 2 = 0 := he
      have htev : w1t n d z % 2 = 0 := by omega
      have ht2 : 2 ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 := by
        rcases hsp' with ⟨-, h1, h2⟩ | ⟨h1, -⟩
        · exact ⟨h1, h2⟩
        · exact absurd (h1.symm.trans htev) (by norm_num)
      have hcle : 2 - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 ∧ 0 ≤ w1s n d z ∧
          w1s n d z ≤ w1T n d + 2 * n := by
        rw [if_pos he] at hcl'
        exact hcl'
      obtain ⟨hm0, hmU⟩ := ChildFrame.m_range_even (frameAt word) (by show 1 ≤ n; omega)
        (by show n + 2 ≤ d; omega) (by show (d + n) % 2 = 0; omega) he ht2 ⟨hcle.2.2.1, hcle.2.2.2⟩
      have hm0' : 0 ≤ z.1 + z.2 := hm0
      have hmU' : z.1 + z.2 ≤ d + n - 2 := hmU
      have ha1 : 1 ≤ A := even_lower hGlt' hNDpos hkeyA ht2.1 (by omega)
      have ha2 : A ≤ N + D := even_upper_neg hGlt' hNDpos hkeyA ht2.2 (by omega)
      by_cases hA' : A = N + D
      · -- the H witness at `A = N + D`: `s_p(u) = 2N + 2 T_q (1 − k)`, witness `j = k − 1`
        obtain ⟨kk, hkk⟩ : ∃ kk : ℤ, d + n - w1t n d z = 2 * kk := ⟨(d + n - w1t n d z) / 2, by omega⟩
        have hb2 : bu = 2 * N + 2 * Tq * (1 - kk) := by
          rw [hA'] at hbI
          linear_combination hbI - hCN - Tq * hkk
        refine ⟨kk - 1, Or.inl ?_⟩
        rw [FLatticePaper.W1CollarFrame.freeH_iff]
        unfold freeHn
        have hpO : ¬ EvenSite (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (kk - 1)) :=
          fun h => ((translate_parity_zTurn _ u _).mp h) (hEvU.mpr he)
        have hTp := hT_p (kk - 1)
        have hSp_p := hS_p (kk - 1)
        have hwp : w1t (D - N) (D + N)
            (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (kk - 1)) = D - N := by
          rw [hTp, hb2]
          ring
        have hqE : EvenSite ((zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (kk - 1)).1,
            (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (kk - 1)).2 - 1) := by
          unfold EvenSite at hpO ⊢
          simp only at hpO ⊢
          omega
        rw [hGn, hGd]
        refine ⟨?_, ?_, ?_⟩
        · unfold closedRect
          rw [if_neg hpO, hTw, hwp, hSp_p, hA']
          exact ⟨by omega, by omega, by omega, by omega⟩
        · intro hcl2
          unfold closedRect at hcl2
          rw [if_pos hqE, w1t_sub_y, hwp] at hcl2
          have := hcl2.2.1
          omega
        · unfold hSp
          right
          exact ⟨by omega, by omega, by omega⟩
      · -- the V witness at `1 ≤ A ≤ N + D − 1`
        have ha3 : A + 1 ≤ N + D := by omega
        obtain ⟨j, hj1, hj2⟩ := exists_shift (D + N - bu) (2 * Tq) (D - N - 2 * Tq) (by omega)
        refine ⟨j, Or.inr ?_⟩
        rw [FLatticePaper.W1CollarFrame.freeV_iff]
        unfold freeVn
        have hpO : ¬ EvenSite (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j) :=
          fun h => ((translate_parity_zTurn _ u _).mp h) (hEvU.mpr he)
        have hTp := hT_p j
        have hSp_p := hS_p j
        have hpE' : EvenSite ((zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).1 - 1,
            (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).2) := by
          unfold EvenSite at hpO ⊢
          simp only at hpO ⊢
          omega
        rw [hGn, hGd]
        refine ⟨?_, ?_, ?_⟩
        · unfold closedRect
          rw [if_neg hpO, hTw, hTp, hSp_p]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · intro hcl2
          unfold closedRect at hcl2
          rw [if_pos hpE', w1s_sub_x, hSp_p] at hcl2
          have := hcl2.2.2.1
          omega
        · unfold vSp
          rw [hSp_p]
          exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩
    · -- odd `z`: `N ≤ A ≤ D`
      have hzO : (z.1 + z.2) % 2 = 1 := by
        unfold EvenSite at he
        omega
      have ht12 : n ≤ w1t n d z ∧ w1t n d z ≤ d := by
        rcases hsp' with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
        · exact absurd (h1.symm.trans (hpar_t.trans hzO)) (by norm_num)
        · exact ⟨h2, h3⟩
      have hcs : 2 - d + n ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + d + n - 2 := by
        rw [if_neg he] at hcl'
        exact ⟨hcl'.2.2.1, hcl'.2.2.2⟩
      obtain ⟨hm0, hmle⟩ := ChildFrame.m_range_odd (frameAt word) (by show 1 ≤ n; omega)
        (by show n + 2 ≤ d; omega) (by show (d + n) % 2 = 0; omega) hzO ht12 hcs
      have hm0' : 0 ≤ z.1 + z.2 := hm0
      have hmle' : z.1 + z.2 ≤ d + n - 1 := hmle
      have hm'0 : 0 ≤ (d + n) - (z.1 + z.2) := by omega
      have hNlo : N ≤ A := odd_lower_neg hGlt' hNDpos.le hεN0 hkeyA ht12.1 hm'0
      have haD : A ≤ D := odd_upper_neg hGlt' hNDpos.le hεN0 hkeyA ht12.2 (by omega)
      obtain ⟨j, hj1, hj2⟩ := exists_shift (D + N - bu) (2 * Tq) (2 - 2 * Tq) (by omega)
      refine ⟨j, Or.inr ?_⟩
      rw [FLatticePaper.W1CollarFrame.freeV_iff]
      unfold freeVn
      have hpE : EvenSite (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j) :=
        (translate_parity_zTurn _ u _).mpr (fun h => he (hEvU.mp h))
      have hTp := hT_p j
      have hSp_p := hS_p j
      have hpO' : ¬ EvenSite ((zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).1 - 1,
          (zTurn u + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).2) := by
        unfold EvenSite at hpE ⊢
        simp only at hpE ⊢
        omega
      rw [hGn, hGd]
      refine ⟨?_, ?_, ?_⟩
      · unfold closedRect
        rw [if_pos hpE, hTw, hTp, hSp_p]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · intro hcl2
        unfold closedRect at hcl2
        rw [if_neg hpO', w1s_sub_x, hSp_p] at hcl2
        have := hcl2.2.2.1
        omega
      · unfold vSp
        rw [hSp_p]
        exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  obtain ⟨j, hj⟩ := hex
  exact hN _ ⟨0, j, rfl⟩ hj

end FLatticePaper.BottomGradeNeg
