import FLatticePaper.Plane.Induction.BottomGrade
import FLatticePaper.Plane.Induction.NegTieHCutFinal

/-! # The left arc (`ε = +1`): a free V point's conjugate image is free up to a deck translate

For a physical free V point `z` with `ε = +1` (so `sheetShift = 0`), let `a = t_p(z)` and `b = s_p(z)`, with `N, D` the odd
parent and `T = D² + 2DN − N²`. The conjugate point is `zTurn z`, and its deck translates `zTurn z + combine i j` have conjugate
grades `t' = (D + N − b) − 2 T j` and `s' = 2 (a − N) + 2 T i` (the conjugate period is `2T`).

* `z` even: `j = 0`, `t' = D + N − b ∈ [D − N, D + N]` (an H cut on an odd point), and `i` puts `s'` in the H window.
* `z` odd, `N − D + 2 ≤ b`: `j = 0`, `t' ∈ [2, 2D − 2]` (an H cut on an even point), and `i` puts `s' ∈ [0, 2T)`.
* `z` odd, `b ≤ N − D + 1`: `j = 1`, `t' ∈ [2 − 2T, 2D − 2]` and `s' ∈ [0, 2(D − N)]` (a V cut on an even point); the shift `i` is
  the residue of `a` (`LeftVWeb`).

The parent-side facts on `b` and the residue of `a` are the named input `LeftVWeb`. -/

namespace FLatticePaper.LeftVGrade

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar
  FLatticePaper.CollarBottomCases FLatticePaper.BottomGrade

/-- **The left V-web input (named).** For `ε = +1`, with `N, D` the odd parent and `T = D² + 2DN − N²`, on the native free V points
(`z ∈ freeV`), with `a = t_p(z)` and `b = s_p(z)`:

* even `z`: `0 ≤ b ≤ 2N`;
* odd `z`: `−(D − N) ≤ b ≤ N + D − 2`;
* odd `z` with `b ≤ N − D + 1`: some `i` has `0 ≤ a − N + i T ≤ D − N`.

Verified numerically on all words of length ≤ 3 (even: 160/160, odd: 324/324, residue: 60/60). Sources: the windows
`FreeVWindow.freeV_even_window` and `freeV_odd_window` for `s`, `ArcRanges.arc_even_range` for the V-arc `t`-range, and the identities
`n · b = N s − m`, `T s = C b − 2a`, `(N + D) b − 2N a = T m`. The even bound (`b ≥ 0`) needs the lattice step of `t` at fixed `s` (spacing
`T` on even points), and the odd residue is the same kind of lattice step; neither is formalised yet. -/
def LeftVWeb (frame : ChildFrame) : Prop :=
  (∀ z ∈ frame.freeV, EvenSite z → 0 ≤ frame.parentSGrade z ∧ frame.parentSGrade z ≤ 2 * frame.parents.odd.num) ∧
  (∀ z ∈ frame.freeV, ¬ EvenSite z → frame.parentSGrade z ≤ frame.parents.odd.num + frame.parents.odd.den - 2 ∧
      -(frame.parents.odd.den - frame.parents.odd.num) ≤ frame.parentSGrade z) ∧
  (∀ z ∈ frame.freeV, ¬ EvenSite z → frame.parentSGrade z ≤ frame.parents.odd.num - frame.parents.odd.den + 1 →
      ∃ i : ℤ,
        0 ≤ frame.parentTGrade z - frame.parents.odd.num +
            i * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) ∧
        frame.parentTGrade z - frame.parents.odd.num +
            i * (frame.parents.odd.den ^ 2 + 2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num ^ 2) ≤
          frame.parents.odd.den - frame.parents.odd.num)

/-- The conjugate combination `i U + j V` has even coordinate sum (the child's `n + d` is even). -/
theorem combine_even_sum (X : ChildFrame) (i j : ℤ) :
    ((X.child.modifiedDeck.combine i j).1 + (X.child.modifiedDeck.combine i j).2) % 2 = 0 := by
  obtain ⟨hn, hd⟩ := X.child_odd
  have hL : (X.child.den + X.child.num) % 2 = 0 := by omega
  rw [X.child_modifiedDeck_combine]
  have hm : (i * (X.child.den + X.child.num)) % 2 = 0 := by
    rw [Int.mul_emod, hL]
    simp
  have e : (i * X.child.den + j * (X.child.num - X.child.den)) +
      (i * X.child.num + j * (X.child.num + X.child.den)) =
      i * (X.child.den + X.child.num) + 2 * (j * X.child.num) := by ring
  rw [e]
  omega

/-- A translate of `zTurn z` by an even-sum combination has the opposite parity to `z`. -/
theorem evenSite_zTurn_add (z c : Site) (hc : (c.1 + c.2) % 2 = 0) :
    EvenSite (zTurn z + c) ↔ ¬ EvenSite z := by
  unfold EvenSite
  simp only [zTurn, Prod.fst_add, Prod.snd_add]
  omega

/-- **The left-arc conjugate image is free up to a deck translate** (`ε = +1`, `z` a free V point, the left V-web input). -/
theorem left_V_not_nonfree (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = 1) (hW : LeftVWeb (frameAt word)) {z : Site} (hz : z ∈ (frameAt word).freeV) :
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (z - (frameAt word).sheetShift)) := by
  rw [sheetShift_eps_one (frameAt word) hε, sub_zero]
  intro hN
  unfold LeftVWeb at hW
  obtain ⟨hEv, hOdd, hRes⟩ := hW
  have hgrades : ∀ X : ChildFrame, ∀ q : Site, X.tGrade q = w1t X.child.num X.child.den q ∧
      X.sGrade q = w1s X.child.num X.child.den q ∧
        X.child.periodDenominator = w1T X.child.num X.child.den := by
    intro X q
    refine ⟨rfl, rfl, ?_⟩
    unfold Fraction.periodDenominator w1T
    rfl
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  obtain ⟨hnodd, hdodd⟩ := (frameAt word).child_odd
  obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
    (frameAt_conj_child hw)
  obtain ⟨hGpos, hGlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
  obtain ⟨hGodd, hGodd2⟩ := (frameAt (conjWord word)).child_odd
  obtain ⟨hDpos, hN0, -⟩ := (frameAt word).valid.odd_bounds
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
  -- the parent grades of `z`
  obtain ⟨a, ha⟩ : ∃ a, a = (frameAt word).parentTGrade z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (frameAt word).parentSGrade z := ⟨_, rfl⟩
  have hEv' : EvenSite z → 0 ≤ b ∧ b ≤ 2 * N := fun he => by
    have h := hEv z hz he
    rw [← hb] at h
    exact h
  have hOdd' : ¬ EvenSite z → b ≤ N + D - 2 ∧ -(D - N) ≤ b := fun he => by
    have h := hOdd z hz he
    rw [← hb] at h
    exact h
  have hRes' : ¬ EvenSite z → b ≤ N - D + 1 → ∃ i : ℤ, 0 ≤ a - N + i * Tq ∧ a - N + i * Tq ≤ D - N := by
    intro he hbl
    have hbl' : (frameAt word).parentSGrade z ≤ N - D + 1 := by rw [← hb]; exact hbl
    obtain ⟨i, h1, h2⟩ := hRes z hz he hbl'
    rw [← ha, ← hTqdef] at h1 h2
    exact ⟨i, h1, h2⟩
  -- the grades of the translates `zTurn z + combine i j`
  have hT_p : ∀ i j : ℤ, w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j)
      = (D + N - b) - j * (2 * Tq) := by
    intro i j
    have hgp := (hgrades (frameAt (conjWord word))
      (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j)).1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.tGrade_add_combine (frameAt (conjWord word)) (zTurn z) i j
    have e2 : (frameAt (conjWord word)).tGrade (zTurn z) = D + N - b := by
      rw [hb]
      exact conj_tGrade_zTurn hw z
    rw [← hgp, e1, e2, hPer]
  have hS_p : ∀ i j : ℤ, w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j)
      = 2 * (a - N) + i * (2 * Tq) := by
    intro i j
    have hgp := (hgrades (frameAt (conjWord word))
      (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j)).2.1
    rw [hGn, hGd] at hgp
    have e1 := FLatticePaper.Induction.ShortPassages.sGrade_add_combine (frameAt (conjWord word)) (zTurn z) i j
    have e2 : (frameAt (conjWord word)).sGrade (zTurn z) = 2 * (a - N) := by
      rw [ha]
      exact conj_sGrade_zTurn hw z
    rw [← hgp, e1, e2, hPer]
  have hpar : ∀ i j : ℤ,
      EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j) ↔ ¬ EvenSite z :=
    fun i j => evenSite_zTurn_add z _ (combine_even_sum (frameAt (conjWord word)) i j)
  have hxpar : ∀ p : Site, w1t (D - N) (D + N) p % 2 = (p.1 + p.2) % 2 := by
    intro p
    have h := (frameAt (conjWord word)).tGrade_mod_two_eq p
    rw [(hgrades (frameAt (conjWord word)) p).1, hGn, hGd] at h
    exact h
  have hex : ∃ i j : ℤ, zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j ∈
      (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
    by_cases he : EvenSite z
    · -- even `z`: `j = 0`, the H cut `t' = D + N − b ∈ [D − N, D + N]`, odd translate
      obtain ⟨hb0, hb2⟩ := hEv' he
      obtain ⟨j, hj1, hj2⟩ := exists_shift (2 * (a - N)) (2 * Tq) (2 - 2 * N) (by omega)
      refine ⟨-j, 0, Or.inl ?_⟩
      have hTp := hT_p (-j) 0
      have hSq := hS_p (-j) 0
      have hpO : ¬ EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0) := by
        rw [hpar]
        exact not_not.mpr he
      have hy : w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0)
          = 2 * (a - N) - 2 * Tq * j := by
        rw [hSq]
        ring
      have hx : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0)
          = D + N - b := by
        rw [hTp]
        ring
      have hxodd : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0) % 2 = 1 := by
        rw [hxpar]
        unfold EvenSite at hpO
        omega
      have hqE : EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0).1,
          (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0).2 - 1) := by
        unfold EvenSite at hpO ⊢
        simp only at hpO ⊢
        omega
      rw [FLatticePaper.W1CollarFrame.freeH_iff]
      unfold freeHn
      rw [hGn, hGd]
      refine ⟨?_, ?_, ?_⟩
      · unfold closedRect
        rw [if_neg hpO, hTw, hx, hy]
        exact ⟨by omega, by omega, by omega, by omega⟩
      · intro hcl
        unfold closedRect at hcl
        rw [if_pos hqE, w1t_sub_y, hx] at hcl
        omega
      · unfold hSp
        right
        exact ⟨hxodd, by omega, by omega⟩
    · -- odd `z`
      obtain ⟨hbU, hbL⟩ := hOdd' he
      by_cases hbH : N - D + 2 ≤ b
      · -- odd `z`, the H cut `t' = D + N − b ∈ [2, 2D − 2]` on an even translate
        obtain ⟨j, hj1, hj2⟩ := exists_shift (2 * (a - N)) (2 * Tq) 0 (by omega)
        refine ⟨-j, 0, Or.inl ?_⟩
        have hTp := hT_p (-j) 0
        have hSq := hS_p (-j) 0
        have hpE : EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0) :=
          (hpar (-j) 0).mpr he
        have hy : w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0)
            = 2 * (a - N) - 2 * Tq * j := by
          rw [hSq]
          ring
        have hx : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0)
            = D + N - b := by
          rw [hTp]
          ring
        have hxeven : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0) % 2 = 0 := by
          rw [hxpar]
          unfold EvenSite at hpE
          omega
        have hqO : ¬ EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0).1,
            (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine (-j) 0).2 - 1) := by
          unfold EvenSite at hpE ⊢
          simp only at hpE ⊢
          omega
        rw [FLatticePaper.W1CollarFrame.freeH_iff]
        unfold freeHn
        rw [hGn, hGd]
        refine ⟨?_, ?_, ?_⟩
        · unfold closedRect
          rw [if_pos hpE, hTw, hx, hy]
          exact ⟨by omega, by omega, by omega, by omega⟩
        · intro hcl
          unfold closedRect at hcl
          rw [if_neg hqO, w1t_sub_y, hx] at hcl
          omega
        · unfold hSp
          left
          exact ⟨hxeven, by omega, by omega⟩
      · -- odd `z`, `b ≤ N − D + 1`: the V cut `t' ∈ [2 − 2T, 2D − 2]`, `s' ∈ [0, 2(D − N)]` on an even translate (`j = 1`)
        obtain ⟨i, hi1, hi2⟩ := hRes' he (by omega)
        refine ⟨i, 1, Or.inr ?_⟩
        have hTp := hT_p i 1
        have hSq := hS_p i 1
        have hpE : EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 1) :=
          (hpar i 1).mpr he
        have hyk : w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 1)
            = 2 * ((a - N) + i * Tq) := by
          rw [hSq]
          ring
        have hx : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 1)
            = D + N - b - 2 * Tq := by
          rw [hTp]
          ring
        have hqO : ¬ EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 1).1 - 1,
            (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 1).2) := by
          unfold EvenSite at hpE ⊢
          simp only at hpE ⊢
          omega
        rw [FLatticePaper.W1CollarFrame.freeV_iff]
        unfold freeVn
        rw [hGn, hGd]
        refine ⟨?_, ?_, ?_⟩
        · unfold closedRect
          rw [if_pos hpE, hTw, hx, hyk]
          exact ⟨by omega, by omega, by omega, by omega⟩
        · intro hcl
          unfold closedRect at hcl
          rw [if_neg hqO, w1s_sub_x, hyk] at hcl
          omega
        · unfold vSp
          rw [hyk]
          exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  obtain ⟨i, j, hmem⟩ := hex
  exact hN _ ⟨i, j, rfl⟩ hmem

end FLatticePaper.LeftVGrade
