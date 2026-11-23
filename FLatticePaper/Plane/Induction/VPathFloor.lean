import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.Q3Para10

/-! Task 72 (the V-block converse, steps 1–3).

Step 1 (`even_spectrum_floor`): an even site whose `t` lies in the even H spectrum is the floor point `z₂ = ⌊2 n l / L⌋` with
`l = (z₁ + z₂)/2` and `L = d + n`; this is the identity `2 n l = t + L z₂` with `0 ≤ t < L`.

Step 2 (`conj_freeH_even_block`): an even free H point `w` of the conjugate child `(D − N, D + N)` (so `L = 2D`) has
`zTurn w = (−b', 2l − 1 − b')` with `b' = ⌊(D − N) l / D⌋` and `1 ≤ l ≤ D − 1` (`range_l`).

Step 3 (`conj_freeH_even_freeV`): `zTurn w` lies in the word frame's free V set (`parent_block_mem_freeV`, `l < D`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **Step 1: the floor point.** An even site with `t` in the even H spectrum is `z₂ = ⌊2 n l / (d + n)⌋` for `l = (z₁+z₂)/2`. -/
theorem even_spectrum_floor (frame : ChildFrame) {z : Site} (hz : EvenSite z)
    (hsp : frame.hSpectrum (frame.tGrade z)) :
    z.2 = (2 * frame.child.num * ((z.1 + z.2) / 2)) / (frame.child.den + frame.child.num) := by
  obtain ⟨c, hc⟩ := frame.tGrade_parity z
  unfold EvenSite at hz
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩
  swap
  · omega
  have hl : z.1 + z.2 = 2 * ((z.1 + z.2) / 2) := by omega
  have ht : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have e : 2 * frame.child.num * ((z.1 + z.2) / 2) =
      frame.tGrade z + (frame.child.den + frame.child.num) * z.2 := by
    rw [ht]
    linear_combination (-frame.child.num) * hl
  have hL : 0 < frame.child.den + frame.child.num := by
    have := frame.child_facts
    omega
  rw [e, Int.add_mul_ediv_left _ _ hL.ne', Int.ediv_eq_zero_of_lt (by omega) (by omega), zero_add]

/-- **The range of the block index.** With `r = (D − N) l − D b` in `[1, D − 1]` and `0 ≤ 2 D l − (D − N) b ≤ T_p + (D − N)`,
the index satisfies `1 ≤ l ≤ D − 1`, where `T_p = D² + 2DN − N²`. -/
theorem range_l (D N l b : ℤ) (hN : 1 ≤ N) (hND : N + 1 ≤ D)
    (hr1 : 1 ≤ (D - N) * l - D * b) (hr2 : (D - N) * l - D * b ≤ D - 1)
    (hs0 : 0 ≤ 2 * D * l - (D - N) * b)
    (hs1 : 2 * D * l - (D - N) * b ≤ (D ^ 2 + 2 * D * N - N ^ 2) + (D - N)) :
    1 ≤ l ∧ l ≤ D - 1 := by
  have hD : 0 < D := by omega
  have hDN : 0 ≤ D - N := by omega
  have hTp0 : 0 ≤ D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  have hTp : (D - N) * (D - 1) < D ^ 2 + 2 * D * N - N ^ 2 := by nlinarith
  -- identity: D · (2Dl − (D−N)b) = T_p · l + (D−N) · r
  have key : D * (2 * D * l - (D - N) * b) =
      (D ^ 2 + 2 * D * N - N ^ 2) * l + (D - N) * ((D - N) * l - D * b) := by ring
  constructor
  · by_contra hl
    rcases (show l = 0 ∨ l ≤ -1 by omega) with h0 | hneg
    · -- l = 0: then −D b ∈ [1, D−1], impossible
      subst h0
      have hb : b ≤ -1 := by
        by_contra hb
        have : 0 ≤ b := by omega
        nlinarith
      nlinarith
    · -- l ≤ −1: T_p l + (D−N) r ≥ 0 forces (D−N) r ≥ T_p > (D−N)(D−1)
      have h1 : (D ^ 2 + 2 * D * N - N ^ 2) * l ≤ -(D ^ 2 + 2 * D * N - N ^ 2) := by
        nlinarith
      have h2 : (D - N) * ((D - N) * l - D * b) ≤ (D - N) * (D - 1) :=
        mul_le_mul_of_nonneg_left hr2 hDN
      have h3 : 0 ≤ D * (2 * D * l - (D - N) * b) := mul_nonneg hD.le hs0
      nlinarith
  · by_contra hl
    rcases (show l = D ∨ D + 1 ≤ l by omega) with hDl | hbig
    · -- l = D: r = D (D − N − b) is a multiple of D, impossible in [1, D−1]
      have hk : (D - N) * l - D * b = D * (D - N - b) := by
        rw [hDl]
        ring
      rcases (show D - N - b ≤ 0 ∨ 1 ≤ D - N - b by omega) with hk0 | hk1
      · nlinarith
      · nlinarith
    · -- l ≥ D + 1: T_p l + (D−N) r ≤ D (T_p + (D−N)) gives T_p ≤ (D−N)(D−1)
      have h1 : (D ^ 2 + 2 * D * N - N ^ 2) * (D + 1) ≤ (D ^ 2 + 2 * D * N - N ^ 2) * l :=
        mul_le_mul_of_nonneg_left hbig hTp0
      have h2 : D * (2 * D * l - (D - N) * b) ≤ D * ((D ^ 2 + 2 * D * N - N ^ 2) + (D - N)) :=
        mul_le_mul_of_nonneg_left hs1 hD.le
      have h3 : (D - N) * 1 ≤ (D - N) * ((D - N) * l - D * b) :=
        mul_le_mul_of_nonneg_left hr1 hDN
      nlinarith

/-- **Step 2: the conjugate even free H point is a parent block vertex.** For an even free H point `w` of the conjugate child
`(D − N, D + N)`, `zTurn w = (−b', 2l − 1 − b')` with `b' = ⌊(D − N) l / D⌋` and `1 ≤ l ≤ D − 1`. -/
theorem conj_freeH_even_block {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt (conjWord word)).freeH) (hwE : EvenSite w) :
    ∃ l : ℤ, 1 ≤ l ∧ l ≤ (frameAt word).parents.odd.den - 1 ∧
      zTurn w = (-(((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * l /
          (frameAt word).parents.odd.den),
        2 * l - 1 - (((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * l /
          (frameAt word).parents.odd.den)) := by
  have hc : (frameAt (conjWord word)).child = (frameAt word).parents.odd.rotate := frameAt_conj_child h
  obtain ⟨hn, hd⟩ := conj_child_num_den hc
  have hN := frameAt_odd_num_pos h
  obtain ⟨-, -, hNle⟩ := (frameAt word).valid.odd_bounds
  have hod : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  have hND : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hw
  obtain ⟨hmem, -, hsp⟩ := hw
  have hfl := even_spectrum_floor (frameAt (conjWord word)) hwE hsp
  obtain ⟨hlo, hhi⟩ : 2 ≤ (frameAt (conjWord word)).tGrade w ∧
      (frameAt (conjWord word)).tGrade w ≤ (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 := by
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with ⟨-, h1', h2'⟩ | ⟨h3, -, -⟩
    · exact ⟨h1', h2'⟩
    · obtain ⟨c, hc⟩ := (frameAt (conjWord word)).tGrade_parity w
      unfold EvenSite at hwE
      omega
  rcases ((frameAt (conjWord word)).mem_closedPolygon_iff w).1 hmem with ⟨-, -, -, hs0, hs1⟩ | ⟨hodd, -⟩
  swap
  · exact absurd hwE hodd
  -- the conjugate period is 2 T_p
  have hT := conj_periodDenominator h
  unfold oddParentPeriod at hT
  -- abbreviations for the parent data
  set D := (frameAt word).parents.odd.den with hDd
  set N := (frameAt word).parents.odd.num with hNd
  -- the even parameter l
  obtain ⟨l, hl⟩ : ∃ l : ℤ, w.1 + w.2 = 2 * l := ⟨(w.1 + w.2) / 2, by unfold EvenSite at hwE; omega⟩
  have hdiv : (w.1 + w.2) / 2 = l := by omega
  have hw1 : w.1 = 2 * l - w.2 := by omega
  have ht_def : (frameAt (conjWord word)).tGrade w =
      (frameAt (conjWord word)).child.num * w.1 - (frameAt (conjWord word)).child.den * w.2 := rfl
  have hs_def : (frameAt (conjWord word)).sGrade w =
      ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) * w.1 +
        ((frameAt (conjWord word)).child.den - (frameAt (conjWord word)).child.num) * w.2 := rfl
  rw [ht_def, hn, hd] at hlo hhi
  rw [hs_def, hn, hd] at hs0 hs1
  rw [hT] at hs1
  have e1 : (D - N) * w.1 - (D + N) * w.2 = 2 * ((D - N) * l - D * w.2) := by
    rw [hw1]
    ring
  have e2 : (D + N + (D - N)) * w.1 + (D + N - (D - N)) * w.2 = 2 * (2 * D * l - (D - N) * w.2) := by
    rw [hw1]
    ring
  have hr1 : 1 ≤ (D - N) * l - D * w.2 := by linarith
  have hr2 : (D - N) * l - D * w.2 ≤ D - 1 := by linarith
  have hs0' : 0 ≤ 2 * D * l - (D - N) * w.2 := by linarith
  have hs1' : 2 * D * l - (D - N) * w.2 ≤ (D ^ 2 + 2 * D * N - N ^ 2) + (D - N) := by linarith
  obtain ⟨hl1, hl2⟩ := range_l D N l w.2 hN hND hr1 hr2 hs0' hs1'
  -- the floor point, with the conjugate denominator 2D
  have hfl' := hfl
  rw [hdiv, hn, hd] at hfl'
  have hLc : D + N + (D - N) = 2 * D := by ring
  rw [hLc] at hfl'
  have hnum : 2 * (D - N) * l = 2 * ((D - N) * l) := by ring
  have hcancel : 2 * ((D - N) * l) / (2 * D) = (D - N) * l / D := by
    rw [Int.mul_comm 2 ((D - N) * l), Int.mul_comm 2 D]
    exact Int.mul_ediv_mul_of_pos_left _ _ (by norm_num)
  rw [hnum, hcancel] at hfl'
  refine ⟨l, hl1, hl2, ?_⟩
  unfold zTurn
  refine Prod.ext ?_ ?_
  · show -w.2 = -(((D - N) * l) / D)
    rw [hfl']
  · show w.1 - 1 = 2 * l - 1 - ((D - N) * l) / D
    rw [hw1, hfl']
    ring

/-- **Step 3: the conjugate even free H point lies in the word frame's free V set.** -/
theorem conj_freeH_even_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {w : Site}
    (hw : w ∈ (frameAt (conjWord word)).freeH) (hwE : EvenSite w) :
    zTurn w ∈ (frameAt word).freeV := by
  obtain ⟨l, hl1, hl2, hz⟩ := conj_freeH_even_block h hw hwE
  rw [hz]
  exact (frameAt word).parent_block_mem_freeV l hl1 (by omega)

end FLatticePaper.Induction
