import FLatticePaper.Plane.Induction.NegTieHCut
import FLatticePaper.Plane.Induction.Q3Para10
import FLatticePaper.Plane.Induction.OddFreeH

/-! Task Q21 (D): the reversed root lies in the free V cut of the word.

For a conjugate free H point `w` (not the corner `(1, 0)`) the reversed root is `v = (N − D + 1 + w₂, N + D − w₁)`, and
`v ∈ freeV(word)`. With `p = w₁ + w₂`, `t = (D − N) w₁ − (D + N) w₂` (the conjugate t-grade) and the determinant
identity `N d − D n = ε`, the root is a block vertex of the word's free V cut:
* `p` even: `v = (−b, 2l − 1 − b)` with `l = D − p/2`, `b = ⌊(d − n) l / d⌋` (`block_mem_freeV`);
* `p` odd, `p = 2D − 1`: `v = 0` (`origin_mem_freeV`);
* `p` odd otherwise: `v = (−b, 2l − b)` with `l = D − (p + 1)/2`, the even block (`even_block_mem_freeV`).
The floor values are the integer identities `2D·((d − n) l − b d) = (2D − t) d + 2 ε l` (even `p`) and
`2D·((d − n) l − b d) = (D + N − t) d + 2 ε l` (odd `p`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- A Bezout relation for the pair `(D + N, D − N)` from `u N + v D = 1` and `D + N` odd. -/
theorem hcut_bezout (N D : ℤ) (hu : ∃ u v : ℤ, u * N + v * D = 1) (hodd : (N + D) % 2 = 1) :
    ∃ α β : ℤ, α * (D + N) + β * (D - N) = 1 := by
  obtain ⟨u, v, huv⟩ := hu
  obtain ⟨k, hk⟩ : ∃ k : ℤ, D + N = 2 * k + 1 := ⟨(D + N - 1) / 2, by omega⟩
  exact ⟨1 - k * (u + v), -(k * (v - u)), by linear_combination hk - 2 * k * huv⟩

/-- The conjugate t-grade `t = (D − N) w₁ − (D + N) w₂` equal to `D − N` only at the corner `(1, 0)`. -/
theorem hcut_t_ne_low (N D w1 w2 : ℤ) (hu : ∃ u v : ℤ, u * N + v * D = 1) (hodd : (N + D) % 2 = 1)
    (_hND : N + 1 ≤ D) (hw1 : 1 ≤ w1) (hw1' : w1 ≤ D + N) (_hw2 : 0 ≤ w2)
    (ht : (D - N) * w1 - (D + N) * w2 = D - N) : w1 = 1 ∧ w2 = 0 := by
  obtain ⟨α, β, hbez⟩ := hcut_bezout N D hu hodd
  have hpos : 0 < D + N := by omega
  have hc : w1 - 1 = (D + N) * (α * (w1 - 1) + β * w2) := by
    linear_combination (-(w1 - 1)) * hbez + β * ht
  have hc0 : α * (w1 - 1) + β * w2 = 0 := by
    rcases lt_trichotomy (α * (w1 - 1) + β * w2) 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  rw [hc0, mul_zero] at hc
  have hw1e : w1 = 1 := by linarith
  subst hw1e
  have h2 : (D + N) * w2 = 0 := by linarith
  have hw2e : w2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · omega
    · exact h
  exact ⟨rfl, hw2e⟩

/-- The conjugate t-grade `t = (D − N) w₁ − (D + N) w₂` equal to `D + N` only at the origin corner. -/
theorem hcut_t_ne_high (N D w1 w2 : ℤ) (hu : ∃ u v : ℤ, u * N + v * D = 1) (hodd : (N + D) % 2 = 1)
    (_hND : N + 1 ≤ D) (hw1 : 1 ≤ w1) (hw1' : w1 ≤ D + N) (_hw2 : 0 ≤ w2) (_hw2' : w2 ≤ D - N - 1)
    (ht : (D - N) * w1 - (D + N) * w2 = D + N) : w1 = D + N ∧ w2 = D - N - 1 := by
  obtain ⟨α, β, hbez⟩ := hcut_bezout N D hu hodd
  have hpos : 0 < D + N := by omega
  have hc : w1 = (D + N) * (α * w1 + β * (w2 + 1)) := by
    linear_combination (-w1) * hbez + β * ht
  have hc1 : α * w1 + β * (w2 + 1) = 1 := by
    rcases lt_trichotomy (α * w1 + β * (w2 + 1)) 1 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  rw [hc1, mul_one] at hc
  subst hc
  have h3 : (D + N) * (D - N) = (D + N) * (w2 + 1) := by linarith
  have h4 : D - N = w2 + 1 := mul_left_cancel₀ (ne_of_gt hpos) h3
  exact ⟨rfl, by omega⟩

/-- The floor of the even-`p` block: `2D·((d − n) l − b d) = (2D − t) d + 2 e l` with `l = D − m`, `p = w₁ + w₂ = 2m`. -/
theorem hcut_floor_even (N D n d e w1 w2 m : ℤ) (hdet : N * d - D * n = e) (he : e = 1 ∨ e = -1)
    (hD : 0 < D) (hd : 2 * D + 1 ≤ d) (hpm : w1 + w2 = 2 * m)
    (ht1 : 1 ≤ (D - N) * w1 - (D + N) * w2) (ht2 : (D - N) * w1 - (D + N) * w2 ≤ 2 * D - 1)
    (hl0 : 0 ≤ D - m) (hlD : D - m ≤ D) :
    (D - N - 1 - w2) * d ≤ (d - n) * (D - m) ∧ (d - n) * (D - m) < (D - N - 1 - w2 + 1) * d := by
  have key : 2 * D * ((d - n) * (D - m) - (D - N - 1 - w2) * d) =
      (2 * D - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m) := by
    linear_combination (2 * (D - m)) * hdet + d * (D - N) * hpm
  have hX0 : 0 ≤ (2 * D - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m) := by
    rcases he with rfl | rfl <;> nlinarith
  have hX1 : (2 * D - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m) < 2 * D * d := by
    rcases he with rfl | rfl <;> nlinarith
  have hdiff0 : 0 ≤ (d - n) * (D - m) - (D - N - 1 - w2) * d := by
    by_contra hc
    simp only [not_le] at hc
    nlinarith
  have hdiff1 : (d - n) * (D - m) - (D - N - 1 - w2) * d < d := by
    by_contra hc
    simp only [not_lt] at hc
    nlinarith
  constructor
  · linarith
  · linarith

/-- The floor of the odd-`p` block: `2D·((d − n) l − b d) = (D + N − t) d + 2 e l` with `l = D − m − 1`,
`p = w₁ + w₂ = 2m + 1`, and `D − N + 1 ≤ t ≤ D + N − 1`. -/
theorem hcut_floor_odd (N D n d e w1 w2 m : ℤ) (hdet : N * d - D * n = e) (he : e = 1 ∨ e = -1)
    (hD : 0 < D) (hND : N ≤ D) (hd : 2 * D + 1 ≤ d) (hpm : w1 + w2 = 2 * m + 1)
    (ht1 : D - N + 1 ≤ (D - N) * w1 - (D + N) * w2) (ht2 : (D - N) * w1 - (D + N) * w2 ≤ D + N - 1)
    (hl0 : 0 ≤ D - m - 1) (hlD : D - m - 1 ≤ D) :
    (D - N - 1 - w2) * d ≤ (d - n) * (D - m - 1) ∧
      (d - n) * (D - m - 1) < (D - N - 1 - w2 + 1) * d := by
  have key : 2 * D * ((d - n) * (D - m - 1) - (D - N - 1 - w2) * d) =
      (D + N - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m - 1) := by
    linear_combination (2 * (D - m - 1)) * hdet + d * (D - N) * hpm
  have hX0 : 0 ≤ (D + N - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m - 1) := by
    rcases he with rfl | rfl <;> nlinarith
  have hpos1 : 1 ≤ D - N + ((D - N) * w1 - (D + N) * w2) := by linarith
  have hprod : 1 * d ≤ (D - N + ((D - N) * w1 - (D + N) * w2)) * d :=
    mul_le_mul_of_nonneg_right hpos1 (by omega)
  have h2l : 2 * (D - m - 1) < d := by omega
  have hX1 : (D + N - ((D - N) * w1 - (D + N) * w2)) * d + 2 * e * (D - m - 1) < 2 * D * d := by
    rcases he with rfl | rfl <;> nlinarith [hprod, h2l]
  have hdiff0 : 0 ≤ (d - n) * (D - m - 1) - (D - N - 1 - w2) * d := by
    by_contra hc
    simp only [not_le] at hc
    nlinarith
  have hdiff1 : (d - n) * (D - m - 1) - (D - N - 1 - w2) * d < d := by
    by_contra hc
    simp only [not_lt] at hc
    nlinarith
  constructor
  · linarith
  · linarith

/-- The even-block bound of the odd-`p` branch: `(d − n) l − b d ≤ n`, from `2D (n − r) = (t − (D − N)) d − 2 e (l + 1)`. -/
theorem hcut_even_block_bound (N D n d e w1 w2 m : ℤ) (hdet : N * d - D * n = e) (he : e = 1 ∨ e = -1)
    (hD : 0 < D) (hd : 2 * D + 1 ≤ d) (hpm : w1 + w2 = 2 * m + 1)
    (ht1 : D - N + 1 ≤ (D - N) * w1 - (D + N) * w2) (hlD : D - m - 1 + 1 ≤ D) (hl0 : 0 ≤ D - m - 1) :
    (d - n) * (D - m - 1) - (D - N - 1 - w2) * d ≤ n := by
  have key : 2 * D * (n - ((d - n) * (D - m - 1) - (D - N - 1 - w2) * d)) =
      ((D - N) * w1 - (D + N) * w2 - (D - N)) * d - 2 * e * (D - m - 1 + 1) := by
    linear_combination (-(2 + 2 * (D - m - 1))) * hdet + (-(d * (D - N))) * hpm
  have hZ : 0 < ((D - N) * w1 - (D + N) * w2 - (D - N)) * d - 2 * e * (D - m - 1 + 1) := by
    rcases he with rfl | rfl <;> nlinarith
  have hpos : 0 < n - ((d - n) * (D - m - 1) - (D - N - 1 - w2) * d) := by
    by_contra hc
    simp only [not_lt] at hc
    nlinarith
  linarith

/-- **The reversed root lies in the free V cut of the word.** For a conjugate free H point `w` other than the corner
`(1, 0)`, the point `(N − D + 1 + w₂, N + D − w₁)` is in `freeV(word)`. -/
theorem freeV_of_conj_freeH {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt (conjWord word)).freeH) (hne : w ≠ (1, 0)) :
    ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
      (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) ∈ (frameAt word).freeV := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hcn, hcd⟩ := conj_child_num_den hc
  have hbox := conj_freeH_box h hw
  have hpar := (frameAt (conjWord word)).tGrade_mod_two_eq w
  have htdef : (frameAt (conjWord word)).tGrade w =
      ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.1 -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.2 := by
    unfold ChildFrame.tGrade
    rw [hcn, hcd]
  have hsp := hw
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hsp
  obtain ⟨-, -, hsp⟩ := hsp
  unfold ChildFrame.hSpectrum at hsp
  rw [htdef, hcn, hcd] at hsp
  rw [htdef] at hpar
  have hdet := (frameAt word).odd_det_child
  have he := (frameAt word).eps_unit
  obtain ⟨hcdW, hcnW, hDpos, hN0, hND, hqpos, hq0, hqn, hpar2⟩ := (frameAt word).linear_facts
  have hodd : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hd : 2 * (frameAt word).parents.odd.den + 1 ≤ (frameAt word).child.den := by omega
  have hu : ∃ u v : ℤ, u * (frameAt word).parents.odd.num + v * (frameAt word).parents.odd.den = 1 := by
    rcases he with he1 | he1
    · exact ⟨(frameAt word).child.den, -(frameAt word).child.num, by rw [he1] at hdet; linarith⟩
    · exact ⟨-(frameAt word).child.den, (frameAt word).child.num, by rw [he1] at hdet; linarith⟩
  have hw1 := hbox.1
  have hw1' := hbox.2.1
  have hw2 := hbox.2.2.1
  have hw2' := hbox.2.2.2
  have hdpos : 0 < (frameAt word).child.den := by omega
  by_cases hpe : (w.1 + w.2) % 2 = 0
  · -- the even branch: `p = w₁ + w₂ = 2m`, the block vertex with `l = D − m`
    obtain ⟨m, hm⟩ : ∃ m : ℤ, w.1 + w.2 = 2 * m := ⟨(w.1 + w.2) / 2, by omega⟩
    set T : ℤ := ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.1 -
      ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.2 with hT
    have ht1 : 1 ≤ T ∧ T ≤ 2 * (frameAt word).parents.odd.den - 1 := by
      rcases hsp with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩
      · constructor <;> omega
      · omega
    have hfl := hcut_floor_even (frameAt word).parents.odd.num (frameAt word).parents.odd.den
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps w.1 w.2 m hdet he hDpos hd hm
      ht1.1 ht1.2 (by omega) (by omega)
    have hfloor : ((frameAt word).child.den - (frameAt word).child.num) *
        ((frameAt word).parents.odd.den - m) / (frameAt word).child.den =
        (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2 := by
      have h1 := (Int.le_ediv_iff_mul_le hdpos).mpr hfl.1
      have h2 := (Int.ediv_lt_iff_lt_mul hdpos).mpr hfl.2
      exact le_antisymm (Int.lt_add_one_iff.mp h2) h1
    have hb := (frameAt word).block_mem_freeV ((frameAt word).parents.odd.den - m) (by omega) (by omega)
    rw [hfloor] at hb
    have hv : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) =
        (-((frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2),
          2 * ((frameAt word).parents.odd.den - m) - 1 -
            ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2)) :=
      Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    rw [hv]
    exact hb
  · by_cases hbig : w.1 + w.2 = 2 * (frameAt word).parents.odd.den - 1
    · -- the origin corner `w = (N + D, D − N − 1)`: the reversed root is `0`
      have hv : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) = (0, 0) :=
        Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      rw [hv]
      exact origin_mem_freeV (frameAt word)
    · -- the odd branch: `p = 2m + 1`, `l = D − m − 1`, the even block
      obtain ⟨m, hm⟩ : ∃ m : ℤ, w.1 + w.2 = 2 * m + 1 := ⟨(w.1 + w.2 - 1) / 2, by omega⟩
      set T : ℤ := ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * w.1 -
        ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * w.2 with hT
      have hT1 : (frameAt word).parents.odd.den - (frameAt word).parents.odd.num ≤ T ∧
          T ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by
        rcases hsp with ⟨h3, -, -⟩ | ⟨-, h1, h2⟩
        · omega
        · constructor <;> omega
      have hTlow : (frameAt word).parents.odd.den - (frameAt word).parents.odd.num + 1 ≤ T := by
        by_contra hc'
        have heq : T = (frameAt word).parents.odd.den - (frameAt word).parents.odd.num := by omega
        obtain ⟨e1, e2⟩ := hcut_t_ne_low (frameAt word).parents.odd.num (frameAt word).parents.odd.den
          w.1 w.2 hu hodd hND hw1 hw1' hw2 heq
        exact hne (Prod.ext e1 e2)
      have hThigh : T ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1 := by
        by_contra hc'
        have heq : T = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num := by omega
        obtain ⟨e1, e2⟩ := hcut_t_ne_high (frameAt word).parents.odd.num (frameAt word).parents.odd.den
          w.1 w.2 hu hodd hND hw1 hw1' hw2 hw2' heq
        omega
      have hfl := hcut_floor_odd (frameAt word).parents.odd.num (frameAt word).parents.odd.den
        (frameAt word).child.num (frameAt word).child.den (frameAt word).eps w.1 w.2 m hdet he hDpos hND.le hd hm
        hTlow hThigh (by omega) (by omega)
      have hfloor : ((frameAt word).child.den - (frameAt word).child.num) *
          ((frameAt word).parents.odd.den - m - 1) / (frameAt word).child.den =
          (frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2 := by
        have h1 := (Int.le_ediv_iff_mul_le hdpos).mpr hfl.1
        have h2 := (Int.ediv_lt_iff_lt_mul hdpos).mpr hfl.2
        exact le_antisymm (Int.lt_add_one_iff.mp h2) h1
      have hbound := hcut_even_block_bound (frameAt word).parents.odd.num (frameAt word).parents.odd.den
        (frameAt word).child.num (frameAt word).child.den (frameAt word).eps w.1 w.2 m hdet he hDpos hd hm
        hTlow (by omega) (by omega)
      have hq : ((frameAt word).child.den - (frameAt word).child.num) * ((frameAt word).parents.odd.den - m - 1) -
          (frameAt word).child.den * ((((frameAt word).child.den - (frameAt word).child.num) *
            ((frameAt word).parents.odd.den - m - 1)) / (frameAt word).child.den) ≤ (frameAt word).child.num := by
        rw [hfloor]
        linarith [hbound]
      have hb := even_block_mem_freeV (frameAt word) ((frameAt word).parents.odd.den - m - 1) (by omega)
        (by omega) hq
      rw [hfloor] at hb
      have hv : ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1 + w.2,
          (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - w.1) =
          (-((frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2),
            2 * ((frameAt word).parents.odd.den - m - 1) -
              ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num - 1 - w.2)) :=
        Prod.ext (by dsimp only; omega) (by dsimp only; omega)
      rw [hv]
      exact hb

end FLatticePaper.Induction
