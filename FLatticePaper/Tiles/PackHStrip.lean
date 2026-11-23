import FLatticePaper.Tiles.PackStrips

/-! Task 50, part 2 (Q10): the H-strip of the packing.

The bottom chain `w1` of the tile, repeated with a north step, is the path `(w1 N)^∞` of period `(A, B + 1)`. Its entry column
into row `s` is `Hent w1 s`: `Hent (s + (B + 1)) = Hent s + A`, and `Hent` is nondecreasing. The rows of the tile satisfy the
two H-strip inequalities `Nrow t ≤ Hent (t + 1)` and `Srow t ≥ Hent (t + 1 - D) + (sum w2 .1 - 1)` for `0 ≤ t < B + D`; the
second one is the interface inequality `L_g2` of `w1`. With these, every translate by `i v1 + j v2` with `j ≠ 0` is row-disjoint
from the tile (`PackAssembly`). -/

namespace FLatticePaper.Tiles

/-- The entry column of the path `(w1 N)^∞` into row `s` (the north step into row `s` is at column `Hent w1 s`). -/
def Hent (w1 : F2Word) (s : ℤ) : ℤ :=
  (s - 1) / (cntI w1 + 1) * (F2Word.sum w1).1 +
    (if (s - 1) % (cntI w1 + 1) < cntI w1 then colN w1 (0, 0) ((s - 1) % (cntI w1 + 1)) else (F2Word.sum w1).1)

/-- Division with a remainder in range: the quotient and remainder of `x = r + b q`. -/
theorem ediv_emod_of_rep {b x q r : ℤ} (hb : 0 < b) (hr0 : 0 ≤ r) (hr : r < b) (h : r + b * q = x) :
    x / b = q ∧ x % b = r :=
  (Int.ediv_emod_unique hb).2 ⟨h, hr0, hr⟩

/-- The entry column of `(w1 N)^∞` into row `x + 1`, for `0 ≤ x ≤ B`. -/
theorem Hent_succ (w1 : F2Word) (_h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (x : ℤ) (h0 : 0 ≤ x) (hx : x ≤ cntI w1) :
    Hent w1 (x + 1) = (if x < cntI w1 then colN w1 (0, 0) x else (F2Word.sum w1).1) := by
  have hq := cntI_nonneg w1
  unfold Hent
  rw [show x + 1 - 1 = x by ring]
  obtain ⟨e1, e2⟩ := ediv_emod_of_rep (b := cntI w1 + 1) (x := x) (q := 0) (r := x) (by omega) h0 (by omega)
    (by ring)
  rw [e1, e2]
  simp

/-- The entry column is nonnegative on the first block (the walk has east and north steps only). -/
theorem colN_nonneg_w1 (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (s : ℤ) : 0 ≤ colN w1 (0, 0) s :=
  colN_nonneg w1 h1 s

/-- The entry column of `(w1 N)^∞` is nondecreasing from one row to the next. -/
theorem Hent_le_succ (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (s : ℤ) :
    Hent w1 s ≤ Hent w1 (s + 1) := by
  have hq := cntI_nonneg w1
  have hA := sum_fst_nonneg_of_one_i w1 h1
  have hn0 := colN_nonneg w1 h1 0
  have hrep : (s - 1) % (cntI w1 + 1) + (cntI w1 + 1) * ((s - 1) / (cntI w1 + 1)) = s - 1 :=
    by rw [Int.emod_def]; ring
  have hr0 : 0 ≤ (s - 1) % (cntI w1 + 1) := Int.emod_nonneg _ (by omega)
  have hrlt : (s - 1) % (cntI w1 + 1) < cntI w1 + 1 := Int.emod_lt_of_pos _ (by omega)
  generalize hqd : (s - 1) / (cntI w1 + 1) = q at hrep
  generalize hrd : (s - 1) % (cntI w1 + 1) = r at hrep hr0 hrlt
  have hs : Hent w1 s = q * (F2Word.sum w1).1 + (if r < cntI w1 then colN w1 (0, 0) r else (F2Word.sum w1).1) := by
    unfold Hent
    rw [hqd, hrd]
  by_cases hrB : r < cntI w1
  · -- the next column stays in the block or reaches the north step at the end of the block
    have hrep' : (r + 1) + (cntI w1 + 1) * q = s + 1 - 1 := by linarith
    obtain ⟨e1, e2⟩ := ediv_emod_of_rep (b := cntI w1 + 1) (x := s + 1 - 1) (q := q) (r := r + 1)
      (by omega) (by omega) (by omega) hrep'
    have hs1 : Hent w1 (s + 1) = q * (F2Word.sum w1).1 +
        (if r + 1 < cntI w1 then colN w1 (0, 0) (r + 1) else (F2Word.sum w1).1) := by
      unfold Hent
      rw [e1, e2]
    rw [hs, hs1, if_pos hrB]
    by_cases hr1 : r + 1 < cntI w1
    · rw [if_pos hr1]
      have := colN_mono_le' w1 h1 r (r + 1) hr0 (by omega) hr1
      linarith
    · rw [if_neg hr1]
      have := colN_le_sum w1 h1 r
      linarith
  · -- the remainder is the last one of the block, the next row starts the next period
    have hr' : r = cntI w1 := by omega
    have hrep' : 0 + (cntI w1 + 1) * (q + 1) = s + 1 - 1 := by
      rw [hr'] at hrep
      have e5 : (cntI w1 + 1) * (q + 1) = (cntI w1 + 1) * q + (cntI w1 + 1) := by ring
      rw [e5]
      linarith
    obtain ⟨e1, e2⟩ := ediv_emod_of_rep (b := cntI w1 + 1) (x := s + 1 - 1) (q := q + 1) (r := 0)
      (by omega) (le_refl 0) (by omega) hrep'
    have hs1 : Hent w1 (s + 1) = (q + 1) * (F2Word.sum w1).1 +
        (if (0 : ℤ) < cntI w1 then colN w1 (0, 0) 0 else (F2Word.sum w1).1) := by
      unfold Hent
      rw [e1, e2]
    rw [hs, hs1, if_neg hrB]
    have hv : 0 ≤ (if (0 : ℤ) < cntI w1 then colN w1 (0, 0) 0 else (F2Word.sum w1).1) := by
      split_ifs
      · exact hn0
      · exact hA
    have e3 : (q + 1) * (F2Word.sum w1).1 = q * (F2Word.sum w1).1 + (F2Word.sum w1).1 := by ring
    rw [e3]
    linarith

/-- The entry column is monotone along the rows. -/
theorem Hent_mono (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (a : ℤ) : ∀ d : ℕ, Hent w1 a ≤ Hent w1 (a + d) := by
  intro d
  induction d with
  | zero => simp
  | succ n ih =>
    have := Hent_le_succ w1 h1 (a + n)
    push_cast
    rw [← add_assoc]
    linarith

theorem Hent_mono_le (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) {a b : ℤ} (hab : a ≤ b) :
    Hent w1 a ≤ Hent w1 b := by
  have := Hent_mono w1 h1 a (b - a).toNat
  rw [show a + ((b - a).toNat : ℤ) = b by omega] at this
  exact this

/-- The period `B + 1`: the entry column rises by `A`. -/
theorem Hent_add_period (w1 : F2Word) (_h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (s : ℤ) :
    Hent w1 (s + (cntI w1 + 1)) = Hent w1 s + (F2Word.sum w1).1 := by
  have hq := cntI_nonneg w1
  have hrep : (s - 1) % (cntI w1 + 1) + (cntI w1 + 1) * ((s - 1) / (cntI w1 + 1)) = s - 1 :=
    by rw [Int.emod_def]; ring
  have hr0 : 0 ≤ (s - 1) % (cntI w1 + 1) := Int.emod_nonneg _ (by omega)
  have hrlt : (s - 1) % (cntI w1 + 1) < cntI w1 + 1 := Int.emod_lt_of_pos _ (by omega)
  have hrep' : (s - 1) % (cntI w1 + 1) + (cntI w1 + 1) * ((s - 1) / (cntI w1 + 1) + 1) = s + (cntI w1 + 1) - 1 := by
    have e5 : (cntI w1 + 1) * ((s - 1) / (cntI w1 + 1) + 1) = (cntI w1 + 1) * ((s - 1) / (cntI w1 + 1)) + (cntI w1 + 1) := by ring
    rw [e5]
    linarith
  obtain ⟨e1, e2⟩ := ediv_emod_of_rep (b := cntI w1 + 1) (x := s + (cntI w1 + 1) - 1)
    (q := (s - 1) / (cntI w1 + 1) + 1) (r := (s - 1) % (cntI w1 + 1)) (by omega) hr0 hrlt hrep'
  unfold Hent
  rw [e1, e2]
  ring

/-- The period `B + 1` iterated, for every integer multiple. -/
theorem Hent_add_mul_period (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (i : ℤ) :
    ∀ s : ℤ, Hent w1 (s + i * (cntI w1 + 1)) = Hent w1 s + i * (F2Word.sum w1).1 := by
  induction i using Int.induction_on with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    have e : s + ((n : ℤ) + 1) * (cntI w1 + 1) = (s + (n : ℤ) * (cntI w1 + 1)) + (cntI w1 + 1) := by ring
    rw [e, Hent_add_period w1 h1, ih s]
    ring
  | pred n ih =>
    intro s
    have e : s + (-(n : ℤ) - 1) * (cntI w1 + 1) + (cntI w1 + 1) = s + (-(n : ℤ)) * (cntI w1 + 1) := by ring
    have hp := Hent_add_period w1 h1 (s + (-(n : ℤ) - 1) * (cntI w1 + 1))
    rw [e, ih s] at hp
    have e4 : (-(n : ℤ) - 1) * (F2Word.sum w1).1 = (-(n : ℤ)) * (F2Word.sum w1).1 - (F2Word.sum w1).1 := by ring
    rw [e4]
    linarith

/-- The entry column at the origin is zero: `Hent 0 = 0`. -/
theorem Hent_zero (w1 : F2Word) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) : Hent w1 0 = 0 := by
  have hq := cntI_nonneg w1
  have hB : Hent w1 (cntI w1 + 1) = (F2Word.sum w1).1 := by
    have := Hent_succ w1 h1 (cntI w1) hq (le_refl _)
    rw [if_neg (lt_irrefl _)] at this
    exact this
  have h := Hent_add_period w1 h1 0
  rw [zero_add, hB] at h
  linarith


/-- The north ends are below the H-entry: `Nrow t ≤ c.1 + Hent (t + 1)` for the rows `0 ≤ t < B + D`. -/
theorem Nrow_le_H (c : GInt) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (t : ℤ) (ht0 : 0 ≤ t) :
    Nrow c w1 w2 t ≤ c.1 + Hent w1 (t + 1) := by
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  unfold Nrow
  by_cases hB : t < cntI w1
  · rw [if_pos hB, Hent_succ w1 h1 t ht0 hB.le, if_pos hB]
  · rw [if_neg hB]
    have hA1 : Hent w1 (cntI w1 + 1) = (F2Word.sum w1).1 := by
      have := Hent_succ w1 h1 (cntI w1) hq (le_refl _)
      rw [if_neg (lt_irrefl _)] at this
      exact this
    have hmono := Hent_mono_le w1 h1 (show cntI w1 + 1 ≤ t + 1 by omega)
    have hnp := colN_nonpos w2 h2 (t - cntI w1)
    linarith

/-- The south ends are above the H-entry shifted by `D` and the second coordinate sum minus one (the interface inequality
`L_g2` of `w1`): `c.1 + Hent (t + 1 - D) + (sum w2 .1 - 1) ≤ Srow c t` for the rows `0 ≤ t < B + D`. -/
theorem Srow_ge_H (c : GInt) (hA1 : Admissible w1) (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (t : ℤ) (_ht0 : 0 ≤ t) (ht1 : t < cntI w1 + cntI w2) :
    c.1 + Hent w1 (t + 1 - cntI w2) + ((F2Word.sum w2).1 - 1) ≤ Srow c w1 w2 t := by
  have hq := cntI_nonneg w1
  have hr := cntI_nonneg w2
  have hC := sum_fst_nonpos_of_i_negOne w2 h2
  unfold Srow
  by_cases htD : t < cntI w2
  · rw [if_pos htD]
    have hH : Hent w1 (t + 1 - cntI w2) ≤ 0 := by
      have := Hent_mono_le w1 h1 (show t + 1 - cntI w2 ≤ 0 by omega)
      rw [Hent_zero w1 h1] at this
      exact this
    have hnp := colN_nonpos w2 h2 (cntI w2 - 1 - t)
    linarith
  · rw [if_neg htD, sum_append_fst]
    have e : t + 1 - cntI w2 = (t - cntI w2) + 1 := by ring
    rw [e, Hent_succ w1 h1 (t - cntI w2) (by omega) (by omega), if_pos (show t - cntI w2 < cntI w1 by omega)]
    have key := L_g2 w1 hA1 (t - cntI w2) (by omega) (by omega)
    rw [show cntI w1 + cntI w2 - 1 - t = cntI w1 - 1 - (t - cntI w2) by ring]
    linarith


end FLatticePaper.Tiles
