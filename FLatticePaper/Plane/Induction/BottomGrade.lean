import FLatticePaper.Plane.Induction.HWeb
import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.VArcOffers
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.W1CollarFrame
import FLatticePaper.Plane.Induction.W1OffCollar
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.CollarBottomCases
import FLatticePaper.Plane.Induction.GradeTransport

/-! # The bottom face (`ε = +1`): a free H point's conjugate image is free up to a deck translate

For a physical free H point `z` (with `ε = +1`, so the shift `lv` is `0`), let `a = t_p(z)` and `b = s_p(z)` be its odd-parent grades,
`L = d + n`, `T_p = D² + 2DN − N²`, `C = D L + N (d − n)`. The identities (for `ε = 1`):

* `L · a = (N + D) · t + m` with `m = z₁ + z₂` (the key identity);
* `b = C · a − T_p · t`, and `C (N + D) = 2N + T_p L`.

The conjugate child is `(D − N, D + N)` with period `2 T_p`, and the conjugate point `zTurn z` moves by `j · (−2N, 2D)`:
`t'` shifts by `−2 T_p j`, `s'` is fixed, and `s' = 2 (a − N)`.

* odd `z`: `N ≤ a ≤ D` (the top value `a = D + 1` only at `hLast`), and a conjugate free V point `zTurn z + j·(−2N, 2D)` exists;
* even `z`: `1 ≤ a ≤ N + D`; for `a ≤ N + D − 1` a conjugate free V point exists, for `a = N + D` the conjugate free H point is at
  `j = (t − L)/2`. -/

namespace FLatticePaper.BottomGrade

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.CollarBottomCases

/-- A window for a deck shift: some `x − P j` lies in `[lo, lo + P − 1]`. -/
theorem exists_shift (x P lo : ℤ) (hP : 0 < P) : ∃ j : ℤ, lo ≤ x - P * j ∧ x - P * j ≤ lo + P - 1 := by
  have h := Int.emod_def (x - lo) P
  have h1 := Int.emod_nonneg (x - lo) hP.ne'
  have h2 := Int.emod_lt_of_pos (x - lo) hP
  refine ⟨(x - lo) / P, ?_, ?_⟩
  · linarith
  · linarith

/-- Integer core, odd sites: `N ≤ a` from `t ≥ n` and `m ≥ 1`. -/
theorem odd_lower {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 ≤ N + D) (hε : N * d - D * n = 1)
    (key : (d + n) * a = (N + D) * t + m) (ht : n ≤ t) (hm : 1 ≤ m) : N ≤ a := by
  have e : (d + n) * N = (N + D) * n + 1 := by linear_combination hε
  have h3 : (N + D) * n ≤ (N + D) * t := mul_le_mul_of_nonneg_left ht hND
  have h4 : (d + n) * N ≤ (d + n) * a := by rw [key, e]; linarith
  exact le_of_mul_le_mul_left h4 hL

/-- Integer core, odd sites: `a ≤ D + 1`, and `a = D + 1` forces `t = d`, `m = L − 1` (the point `hLast`). -/
theorem odd_upper {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 < N + D) (hε : N * d - D * n = 1)
    (key : (d + n) * a = (N + D) * t + m) (ht : t ≤ d) (hm : m ≤ d + n - 1) :
    a ≤ D + 1 ∧ (a = D + 1 → t = d ∧ m = d + n - 1) := by
  have e : (d + n) * (D + 1) = (N + D) * d + (d + n - 1) := by linear_combination (-1 : ℤ) * hε
  have h3 : (N + D) * t ≤ (N + D) * d := mul_le_mul_of_nonneg_left ht hND.le
  have h4 : (d + n) * a ≤ (d + n) * (D + 1) := by rw [key, e]; linarith
  have hle : a ≤ D + 1 := le_of_mul_le_mul_left h4 hL
  refine ⟨hle, fun hEq => ?_⟩
  subst hEq
  have h5 : (N + D) * t + m = (N + D) * d + (d + n - 1) := by linarith [key, e]
  have h6 : (N + D) * (d - t) = 0 := by linarith
  have h7 : d - t = 0 := by
    rcases mul_eq_zero.mp h6 with h | h
    · omega
    · exact h
  constructor
  · linarith
  · linarith

/-- Integer core, even sites: `1 ≤ a` from `t ≥ 2` and `m ≥ 0`. -/
theorem even_lower {N D n d t m a : ℤ} (hL : 0 < d + n) (hND : 0 < N + D) (key : (d + n) * a = (N + D) * t + m)
    (ht : 2 ≤ t) (hm : 0 ≤ m) : 1 ≤ a := by
  by_contra h
  rw [not_le] at h
  have h1 : a ≤ 0 := by omega
  have h2 : (d + n) * a ≤ 0 := by nlinarith
  have h3 : 2 * (N + D) ≤ (N + D) * t := by nlinarith
  linarith

/-- The site with `t(z) = t` and `m(z) = m` (for `L = d + n`) is `(d, n − 1)` when `t = d` and `m = L − 1`. -/
theorem site_eq_hLast {n d : ℤ} (hL : 0 < d + n) {z : Site} (ht : n * z.1 - d * z.2 = d)
    (hm : z.1 + z.2 = d + n - 1) : z = (d, n - 1) := by
  have e1 : (d + n) * z.1 = (d + n) * d := by linear_combination ht + d * hm
  have e2 : (d + n) * z.2 = (d + n) * (n - 1) := by linear_combination n * hm - ht
  have f1 : z.1 = d := mul_left_cancel₀ hL.ne' e1
  have f2 : z.2 = n - 1 := mul_left_cancel₀ hL.ne' e2
  exact Prod.ext f1 f2

/-- The bottom-face shift `w1t` of a deck-free point: `t` moves by `−n` in `x` and by `+d` in `y` (`y` down). -/
theorem w1t_sub_x (n d : ℤ) (p : Site) : w1t n d (p.1 - 1, p.2) = w1t n d p - n := by
  unfold w1t; ring

theorem w1s_sub_x (n d : ℤ) (p : Site) : w1s n d (p.1 - 1, p.2) = w1s n d p - (d + n) := by
  unfold w1s; ring

theorem w1t_sub_y (n d : ℤ) (p : Site) : w1t n d (p.1, p.2 - 1) = w1t n d p + d := by
  unfold w1t; ring

/-- The sum of the coordinates of `combine 0 j` is `2 j n`. -/
theorem combine_zero_sum (X : ChildFrame) (j : ℤ) :
    (X.child.modifiedDeck.combine 0 j).1 + (X.child.modifiedDeck.combine 0 j).2 = 2 * (j * X.child.num) := by
  unfold PeriodDeck.combine
  rw [X.child_modifiedDeck_kernel, X.child_modifiedDeck_transverse]
  simp only
  ring

/-- A translate `zTurn z + combine 0 j` (in a child frame `X`) has the opposite parity to `z`. -/
theorem translate_parity_zTurn (X : ChildFrame) (z : Site) (j : ℤ) :
    EvenSite (zTurn z + X.child.modifiedDeck.combine 0 j) ↔ ¬ EvenSite z := by
  have hs := combine_zero_sum X j
  unfold EvenSite
  simp only [zTurn, Prod.fst_add, Prod.snd_add]
  have hs' : (X.child.modifiedDeck.combine 0 j).1 + (X.child.modifiedDeck.combine 0 j).2 = 2 * (j * X.child.num) := hs
  generalize j * X.child.num = k at hs'
  generalize hc1 : (X.child.modifiedDeck.combine 0 j).1 = c1 at hs' ⊢
  generalize hc2 : (X.child.modifiedDeck.combine 0 j).2 = c2 at hs' ⊢
  omega

/-- **The bottom-face conjugate image is not nonfree** (`ε = +1`, `z` a free H point, `z ≠ hLast`). -/
theorem bottom_not_nonfree (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = 1) {z : Site} (hz : z ∈ (frameAt word).freeH)
    (hne : z ≠ (frameAt word).hLast) :
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (z - (frameAt word).sheetShift)) := by
  have hlv : (frameAt word).sheetShift = (0, 0) := by
    unfold ChildFrame.sheetShift ChildFrame.phaseW
    have h0 : (1 - (1 + (frameAt word).eps) / 2 : ℤ) = 0 := by rw [hε]; norm_num
    rw [h0, zero_smul]
    rfl
  have hzl : z - (frameAt word).sheetShift = z := by
    rw [hlv]
    ext <;> simp
  rw [hzl]
  intro hN
  -- grade data of the two frames, as `w1` functions
  have hgrades : ∀ X : ChildFrame, ∀ q : Site, X.tGrade q = w1t X.child.num X.child.den q ∧
      X.sGrade q = w1s X.child.num X.child.den q ∧
        X.child.periodDenominator = w1T X.child.num X.child.den := by
    intro X q
    refine ⟨rfl, rfl, ?_⟩
    unfold Fraction.periodDenominator w1T
    rfl
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  obtain ⟨hnodd, hdodd⟩ := (frameAt word).child_odd
  have hεN : (1 : ℤ) = (frameAt word).parents.odd.num * (frameAt word).child.den
      - (frameAt word).parents.odd.den * (frameAt word).child.num := by
    have := (frameAt word).eps_eq
    rw [hε] at this
    linarith
  obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
    (frameAt_conj_child hw)
  obtain ⟨hGpos, hGlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
  obtain ⟨hGodd, -⟩ := (frameAt (conjWord word)).child_odd
  obtain ⟨hDpos, hN0, -⟩ := (frameAt word).valid.odd_bounds
  -- abbreviations for the integers
  set N := (frameAt word).parents.odd.num with hNdef
  set D := (frameAt word).parents.odd.den with hDdef
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
  -- the two identities at `ε = 1`
  have I2 : (D * (d + n) + N * (d - n)) * (N + D) = 2 * N + Tq * (d + n) := by
    rw [hTqdef]
    linear_combination (-2 * N) * hεN
  -- the parent grades of `z`
  obtain ⟨a, ha⟩ : ∃ a, a = (frameAt word).parentTGrade z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (frameAt word).parentSGrade z := ⟨_, rfl⟩
  have haN : a = N * z.1 - D * z.2 := by rw [ha]; rfl
  have hbN : b = (D + N) * z.1 + (D - N) * z.2 := by rw [hb]; rfl
  have hI1 : b = (D * (d + n) + N * (d - n)) * a - Tq * w1t n d z := by
    rw [haN, hbN, hTqdef]
    unfold w1t
    linear_combination ((D + N) * z.1 + (D - N) * z.2) * hεN
  have hkey : (d + n) * a = (N + D) * w1t n d z + (z.1 + z.2) := by
    have h2 : (d + n) * (frameAt word).parentTGrade z = (D + N) * w1t n d z + (z.1 + z.2) := by
      have h := (frameAt word).key_identity_tp z
      rw [hε, one_mul] at h
      exact h
    rw [ha]
    linarith [h2]
  have hweb : 0 ≤ a ∧ a ≤ N + D := by
    rw [ha]
    exact (frameAt word).parentTGrade_bounds_of_freeH hz
  have hpar_t : w1t n d z % 2 = (z.1 + z.2) % 2 := t_parity n d z.1 z.2 hnodd hdodd
  obtain ⟨hcl, -, hsp⟩ := (FLatticePaper.W1CollarFrame.freeH_iff (frameAt word) z).mp hz
  have hsp' := hsp
  unfold hSp at hsp'
  have hcl' := hcl
  unfold closedRect at hcl'
  -- the translate `p = zTurn z + combine 0 j` in the conjugate frame
  have hT_p : ∀ j : ℤ, w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)
      = (D + N - b) - j * (2 * Tq) := by
    intro j
    have hgp := (hgrades (frameAt (conjWord word)) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)).1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.tGrade_add_combine (frameAt (conjWord word)) (zTurn z) 0 j
    have e2 : (frameAt (conjWord word)).tGrade (zTurn z) = D + N - b := by
      rw [hb]
      exact conj_tGrade_zTurn hw z
    rw [← hgp, e1, e2, hPer]
  have hS_p : ∀ j : ℤ, w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)
      = 2 * (a - N) := by
    intro j
    have hgp := (hgrades (frameAt (conjWord word)) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j)).2.1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.sGrade_add_combine (frameAt (conjWord word)) (zTurn z) 0 j
    have e2 : (frameAt (conjWord word)).sGrade (zTurn z) = 2 * (a - N) := by
      rw [ha]
      exact conj_sGrade_zTurn hw z
    rw [← hgp, e1, e2]
    ring
  have hex : ∃ j : ℤ, zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j ∈
      (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
    by_cases he : EvenSite z
    · -- even `z`: `1 ≤ a ≤ N + D`
      have hzE : (z.1 + z.2) % 2 = 0 := he
      have htev : w1t n d z % 2 = 0 := by omega
      have ht2 : 2 ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 := by
        rcases hsp' with ⟨-, h1, h2⟩ | ⟨h1, -⟩
        · exact ⟨h1, h2⟩
        · exact absurd (h1.symm.trans htev) (by norm_num)
      have hcle : 2 - w1T n d ≤ w1t n d z ∧ w1t n d z ≤ d + n - 2 ∧ 0 ≤ w1s n d z ∧ w1s n d z ≤ w1T n d + 2 * n := by
        rw [if_pos he] at hcl'
        exact hcl'
      obtain ⟨hm0, -⟩ := ChildFrame.m_range_even (frameAt word) (by show 1 ≤ n; omega)
        (by show n + 2 ≤ d; omega) (by show (d + n) % 2 = 0; omega) he ht2 ⟨hcle.2.2.1, hcle.2.2.2⟩
      have ha1 : 1 ≤ a := even_lower hGlt' hNDpos hkey ht2.1 hm0
      have ha2 : a ≤ N + D := hweb.2
      by_cases hA : a = N + D
      · -- the H witness at `a = N + D`
        obtain ⟨kk, hkk⟩ : ∃ kk : ℤ, d + n - w1t n d z = 2 * kk := ⟨(d + n - w1t n d z) / 2, by omega⟩
        have hb2 : b = 2 * N + 2 * Tq * kk := by
          linear_combination hI1 + (D * (d + n) + N * (d - n)) * hA + I2 + Tq * hkk
        refine ⟨-kk, Or.inl ?_⟩
        rw [FLatticePaper.W1CollarFrame.freeH_iff]
        unfold freeHn
        have hpO : ¬ EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (-kk)) :=
          fun h => ((translate_parity_zTurn _ z _).mp h) he
        have hTp := hT_p (-kk)
        have hSp_p := hS_p (-kk)
        have hwp : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (-kk)) = D - N := by
          rw [hTp, hb2]
          ring
        have hqE : EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (-kk)).1,
            (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 (-kk)).2 - 1) := by
          unfold EvenSite at hpO ⊢
          simp only at hpO ⊢
          omega
        rw [hGn, hGd]
        refine ⟨?_, ?_, ?_⟩
        · unfold closedRect
          rw [if_neg hpO, hTw, hwp, hSp_p, hA]
          exact ⟨by omega, by omega, by omega, by omega⟩
        · intro hcl2
          unfold closedRect at hcl2
          rw [if_pos hqE, w1t_sub_y, hwp] at hcl2
          have := hcl2.2.1
          omega
        · unfold hSp
          right
          exact ⟨by omega, by omega, by omega⟩
      · -- the V witness at `1 ≤ a ≤ N + D − 1`
        have ha3 : a + 1 ≤ N + D := by omega
        obtain ⟨j, hj1, hj2⟩ := exists_shift (D + N - b) (2 * Tq) (D - N - 2 * Tq) (by omega)
        refine ⟨j, Or.inr ?_⟩
        rw [FLatticePaper.W1CollarFrame.freeV_iff]
        unfold freeVn
        have hpO : ¬ EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j) :=
          fun h => ((translate_parity_zTurn _ z _).mp h) he
        have hTp := hT_p j
        have hSp_p := hS_p j
        have hpE' : EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).1 - 1,
            (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).2) := by
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
    · -- odd `z`: `N ≤ a ≤ D`
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
      have hmle' : z.1 + z.2 ≤ d + n - 1 := hmle
      have hm1 : 1 ≤ z.1 + z.2 := by omega
      have hNlo : N ≤ a := odd_lower hGlt' (by linarith) hεN.symm hkey ht12.1 hm1
      have hup := odd_upper hGlt' hNDpos hεN.symm hkey ht12.2 hmle'
      have haD : a ≤ D := by
        obtain ⟨hle, himp⟩ := hup
        by_contra hcon
        have hEq : a = D + 1 := by omega
        obtain ⟨ht_d, hm_L⟩ := himp hEq
        apply hne
        unfold w1t at ht_d
        exact site_eq_hLast hGlt' ht_d hm_L
      obtain ⟨j, hj1, hj2⟩ := exists_shift (D + N - b) (2 * Tq) (2 - 2 * Tq) (by omega)
      refine ⟨j, Or.inr ?_⟩
      rw [FLatticePaper.W1CollarFrame.freeV_iff]
      unfold freeVn
      have hpE : EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j) :=
        (translate_parity_zTurn _ z _).mpr he
      have hTp := hT_p j
      have hSp_p := hS_p j
      have hpO' : ¬ EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).1 - 1,
          (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 j).2) := by
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

end FLatticePaper.BottomGrade
