import FLatticePaper.Plane.Induction.LeftVNegProof

/-! # The eps = -1 left-arc witness: the conjugate image of a free V point is free up to a deck translate

For `ε = −1` the conjugate point of a free V point `z` is `zTurn z` (no sheet shift). The witnesses are the same as in
`LeftVGrade` (`j = 0` throughout): even `z` takes the H cut `t' = D + N − b`; odd `z` with `b ≤ N + D − 2` takes the H cut
`t' ∈ [2, 2D − 2]`; odd `z` with `b = N + D` takes the V cut `t' = 0` with the shift `i` from the residue of `a`. The parent-side
facts are `LeftVNegProof`'s (`neg_even_bounds`, `neg_odd_bounds`, `neg_residue`). -/

namespace FLatticePaper.LeftVNegGrade

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.W1OffCollar
  FLatticePaper.CollarBottomCases FLatticePaper.BottomGrade FLatticePaper.LeftVGrade FLatticePaper.LeftVNegProof

/-- **The witnesses at `ε = −1`.** Given the parent-side bounds of `z`, some deck translate of `zTurn z` is free. -/
theorem neg_witness (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    {z : Site} {a b Tq : ℤ}
    (ha : a = (frameAt word).parentTGrade z) (hb : b = (frameAt word).parentSGrade z)
    (hTqdef : Tq = (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num
      - (frameAt word).parents.odd.num ^ 2)
    (hN : 0 < (frameAt word).parents.odd.num)
    (hE : EvenSite z → 0 ≤ b ∧ b ≤ 2 * (frameAt word).parents.odd.num)
    (hO : ¬ EvenSite z → (frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 2 ≤ b ∧
      b ≤ (frameAt word).parents.odd.num + (frameAt word).parents.odd.den ∧ b % 2 = 1)
    (hR : ¬ EvenSite z → b = (frameAt word).parents.odd.num + (frameAt word).parents.odd.den →
      ∃ i : ℤ, 0 ≤ a - (frameAt word).parents.odd.num + i * Tq ∧
        a - (frameAt word).parents.odd.num + i * Tq ≤ (frameAt word).parents.odd.den - (frameAt word).parents.odd.num) :
    ∃ i j : ℤ, zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i j ∈
      (frameAt (conjWord word)).freeH ∪ (frameAt (conjWord word)).freeV := by
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
      obtain ⟨hb0, hb2⟩ := hE he
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
      obtain ⟨hbL, hbTop, hbodd⟩ := hO he
      have hbH : N - D + 2 ≤ b := hbL
      by_cases hbU : b ≤ N + D - 2
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
      · -- odd `z`, `b = N + D`: the V cut `t' = 0`, `s' ∈ [0, 2(D − N)]` (shift `i` from the residue of `a`), `j = 0`
        have hbeq : b = N + D := by omega
        obtain ⟨i, hi1, hi2⟩ := hR he hbeq
        refine ⟨i, 0, Or.inr ?_⟩
        have hTp := hT_p i 0
        have hSq := hS_p i 0
        have hpE : EvenSite (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 0) :=
          (hpar i 0).mpr he
        have hyk : w1s (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 0)
            = 2 * ((a - N) + i * Tq) := by
          rw [hSq]
          ring
        have hx : w1t (D - N) (D + N) (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 0)
            = D + N - b := by
          rw [hTp]
          ring
        have hqO : ¬ EvenSite ((zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 0).1 - 1,
            (zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine i 0).2) := by
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
          have := hcl.2.2.1
          omega
        · unfold vSp
          rw [hyk]
          exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  exact hex

/-- **Translate invariance of `Nonfree`** by the conjugate transverse vector `combine 0 1`. -/
theorem nonfree_of_add_combine01 (f : ChildFrame) (p : Site)
    (hN : Nonfree f (p + f.child.modifiedDeck.combine 0 1)) : Nonfree f p := by
  intro v hv
  obtain ⟨i, j, rfl⟩ := hv
  have h := hN (f.child.modifiedDeck.combine i (j - 1)) ⟨i, j - 1, rfl⟩
  have e : p + f.child.modifiedDeck.combine 0 1 + f.child.modifiedDeck.combine i (j - 1) =
      p + f.child.modifiedDeck.combine i j := by
    ext <;> simp only [Farey.PeriodDeck.combine, Prod.fst_add, Prod.snd_add] <;> ring
  rw [e] at h
  exact h

/-- **The left-arc conjugate freeness at `ε = −1`** (`z` a free V point other than `vLast`). -/
theorem left_V_neg_not_nonfree (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = -1) {z : Site} (hz : z ∈ (frameAt word).freeV) (hvL : z ≠ (frameAt word).vLast) :
    ¬ Nonfree (frameAt (conjWord word)) (zTurn z) := by
  have hN : 0 < (frameAt word).parents.odd.num := by
    obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
      (frameAt_conj_child hw)
    obtain ⟨-, hGlt, -, -, -⟩ := (frameAt (conjWord word)).child_facts
    rw [hGn, hGd] at hGlt
    omega
  intro hNf
  obtain ⟨i, j, hm⟩ := neg_witness word hw (a := (frameAt word).parentTGrade z)
    (b := (frameAt word).parentSGrade z)
    (Tq := (frameAt word).parents.odd.den ^ 2 + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num -
      (frameAt word).parents.odd.num ^ 2) rfl rfl rfl hN
    (fun he => neg_even_bounds (frameAt word) hε hN hz he hvL)
    (fun he => neg_odd_bounds (frameAt word) hε hN hz he)
    (fun _ hbeq => neg_residue (frameAt word) hε hN hbeq)
  exact hNf _ ⟨i, j, rfl⟩ hm

/-- **The right and up arcs at `ε = −1`.** The corner `c = z + ker` (with `ker = (d, n)`) has
`zTurn (c − sheetShift) = zTurn z + combine 0 1`, a conjugate deck translate. -/
theorem right_up_arc_not_nonfree (word : Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hε : (frameAt word).eps = -1) {z : Site} (hz : z ∈ (frameAt word).freeV) (hvL : z ≠ (frameAt word).vLast) :
    ¬ Nonfree (frameAt (conjWord word))
      (zTurn (z + ((frameAt word).child.den, (frameAt word).child.num) - (frameAt word).sheetShift)) := by
  rw [sheetShift_eps_neg_one (frameAt word) hε]
  obtain ⟨hGn, hGd⟩ := conj_child_num_den (frame := frameAt word) (conj := frameAt (conjWord word))
    (frameAt_conj_child hw)
  obtain ⟨hdL, hnL, -⟩ := (frameAt word).linear_facts
  have hc : (frameAt (conjWord word)).child.modifiedDeck.combine 0 1 =
      (-2 * (frameAt word).parents.odd.num, 2 * (frameAt word).parents.odd.den) := by
    simp only [ChildFrame.child_modifiedDeck_combine, hGn, hGd]
    ext <;> simp only <;> ring
  have key : zTurn (z + ((frameAt word).child.den, (frameAt word).child.num) -
      ((frameAt word).parents.even.den, (frameAt word).parents.even.num)) =
      zTurn z + (frameAt (conjWord word)).child.modifiedDeck.combine 0 1 := by
    rw [hc]
    ext <;> simp only [zTurn, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> omega
  rw [key]
  intro hNf
  exact left_V_neg_not_nonfree word hw hε hz hvL (nonfree_of_add_combine01 _ _ hNf)

end FLatticePaper.LeftVNegGrade
