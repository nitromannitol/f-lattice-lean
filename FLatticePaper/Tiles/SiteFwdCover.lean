import FLatticePaper.Tiles.SiteFwdLink
import FLatticePaper.Tiles.SiteBand

/-! Task 53, item 4 (the horizontal cover): the letter type of a forward index is read off from its cursor error.

For a forward word `ℓ` with cursor bounds `CursorB ℓ n d` (the ceiling bounds of slope `2n / (d + n)` up to its length), the
error `ε_k = (d+n) · qPrefix ℓ k − 2n·k` lies in `[0, d+n)`, and the error of the origin of index `k` is `e_k = ε_{k+1}`. Then
* the letter `k` is `p` exactly when `e_k < C` (`C = d − n`);
* it is a `q` not preceded by `q` exactly when `C ≤ e_k < 2C`;
* it is a `q` preceded by `q` exactly when `2C ≤ e_k < d + n`.
These are the three offset classes of `FwdOffset`. -/

namespace FLatticePaper.Tiles.SiteFwdCover

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CeilWords FLatticePaper.Tiles.SiteMarksCursor
  FLatticePaper.Tiles.SiteFwdLink FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteBand

/-- The cursor bounds of a forward word up to its length. -/
def CursorB (ℓ : BinaryWord) (n d : ℤ) : Prop :=
  ∀ j : ℕ, j ≤ ℓ.length → (d + n) * qPrefix ℓ j - (d + n) < 2 * n * (j : ℤ) ∧ 2 * n * (j : ℤ) ≤ (d + n) * qPrefix ℓ j

theorem eps_bounds (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (j : ℕ) (hj : j ≤ ℓ.length) :
    0 ≤ (d + n) * qPrefix ℓ j - 2 * n * (j : ℤ) ∧ (d + n) * qPrefix ℓ j - 2 * n * (j : ℤ) < d + n := by
  obtain ⟨h1, h2⟩ := hB j hj
  constructor <;> linarith

theorem getD_eq_getElem_p (ℓ : BinaryWord) (k : ℕ) (hk : k < ℓ.length) :
    ℓ.getD k Letter.p = ℓ[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- The error of the origin of index `k`, `e_k = ε_{k+1}`, in terms of `ε_k` and the letter `k`. -/
theorem err_step (ℓ : BinaryWord) (n d : ℤ) (k : ℕ) (hk : k < ℓ.length) :
    (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) =
      ((d + n) * qPrefix ℓ k - 2 * n * (k : ℤ)) + (if ℓ.getD k Letter.p = Letter.q then d + n else 0) - 2 * n := by
  rw [getD_eq_getElem_p ℓ k hk, qPrefix_succ ℓ k hk]
  split_ifs <;> ring

/-- The letter `k` is `q` exactly when its cursor error `ε_k` is below `2n`. -/
theorem letter_q_iff_eps (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (k : ℕ) (hk : k < ℓ.length) :
    ℓ.getD k Letter.p = Letter.q ↔ (d + n) * qPrefix ℓ k - 2 * n * (k : ℤ) < 2 * n := by
  have hs := err_step ℓ n d k hk
  obtain ⟨a1, a2⟩ := eps_bounds ℓ n d hB (k + 1) (by omega)
  obtain ⟨b1, b2⟩ := eps_bounds ℓ n d hB k (by omega)
  push_cast at a1 a2
  constructor
  · intro hq
    rw [if_pos hq] at hs
    linarith
  · intro hlt
    by_contra hne
    rw [if_neg hne] at hs
    linarith

theorem letter_eq_p_of_ne_q (x : Letter) (h : x ≠ Letter.q) : x = Letter.p := by
  cases x
  · rfl
  · exact absurd rfl h

/-- The previous letter of index `j + 1` is `q` exactly when the error `e_j` of index `j` is at least `C`. -/
theorem prev_q_iff (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (j : ℕ) (hj : j < ℓ.length) :
    ℓ.getD j Letter.p = Letter.q ↔ d - n ≤ (d + n) * qPrefix ℓ (j + 1) - 2 * n * ((j : ℤ) + 1) := by
  have herr := err_step ℓ n d j hj
  have hl := letter_q_iff_eps ℓ n d hB j hj
  obtain ⟨b1, b2⟩ := eps_bounds ℓ n d hB j (by omega)
  constructor
  · intro hq
    rw [if_pos hq] at herr
    linarith
  · intro hC
    by_contra hne
    rw [if_neg hne] at herr
    have hε : ¬ ((d + n) * qPrefix ℓ j - 2 * n * (j : ℤ) < 2 * n) := fun h => hne (hl.mpr h)
    push Not at hε
    linarith

/-- A `q` letter at index `k` has error `e_k = ε_k + C`; a `p` letter has `e_k = ε_k − N`. -/
theorem err_of_q (ℓ : BinaryWord) (n d : ℤ) (k : ℕ) (hk : k < ℓ.length) (hq : ℓ.getD k Letter.p = Letter.q) :
    (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) = ((d + n) * qPrefix ℓ k - 2 * n * (k : ℤ)) + (d - n) := by
  have herr := err_step ℓ n d k hk
  rw [if_pos hq] at herr
  linarith

theorem err_of_p (ℓ : BinaryWord) (n d : ℤ) (k : ℕ) (hk : k < ℓ.length) (hp : ℓ.getD k Letter.p ≠ Letter.q) :
    (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) = ((d + n) * qPrefix ℓ k - 2 * n * (k : ℤ)) - 2 * n := by
  have herr := err_step ℓ n d k hk
  rw [if_neg hp] at herr
  linarith

/-- The previous letter of a `q` at index `j + 1` is `q` exactly when its error `e_{j+1} − C` is at least `C`. -/
theorem flag_iff_of_q (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (j : ℕ) (hj : j + 1 < ℓ.length)
    (hq : ℓ.getD (j + 1) Letter.p = Letter.q) :
    (ℓ.getD j Letter.p = Letter.q) ↔
      2 * (d - n) ≤ (d + n) * qPrefix ℓ (j + 1 + 1) - 2 * n * ((j : ℤ) + 1 + 1) := by
  have hpq := prev_q_iff ℓ n d hB j (by omega)
  have herr := err_of_q ℓ n d (j + 1) hj hq
  push_cast at herr hpq ⊢
  rw [hpq]
  constructor <;> intro h <;> linarith

/-- **The type trichotomy of a forward index.** With `e_k` the error of the origin of index `k`, the letter `k` is `p` when
`e_k < C`, a `q` not preceded by `q` when `C ≤ e_k < 2C`, and a `q` preceded by `q` when `2C ≤ e_k < L`. -/
theorem fwd_type (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (hnd : n < d) (k : ℕ) (hk : k < ℓ.length) :
    ((d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) < d - n → ℓ.getD k Letter.p = Letter.p) ∧
    (d - n ≤ (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) →
      (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) < 2 * (d - n) →
      ℓ.getD k Letter.p = Letter.q ∧ ¬ (k ≠ 0 ∧ ℓ.getD (k - 1) Letter.p = Letter.q)) ∧
    (2 * (d - n) ≤ (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) →
      (d + n) * qPrefix ℓ (k + 1) - 2 * n * ((k : ℤ) + 1) < d + n →
      ℓ.getD k Letter.p = Letter.q ∧ (k ≠ 0 ∧ ℓ.getD (k - 1) Letter.p = Letter.q)) := by
  have hb := eps_bounds ℓ n d hB k (by omega)
  have hl := letter_q_iff_eps ℓ n d hB k hk
  have hzero : (d + n) * qPrefix ℓ 0 - 2 * n * ((0 : ℕ) : ℤ) = 0 := by simp [qPrefix]
  have hC0 : 0 < d - n := by omega
  refine ⟨fun hlt => ?_, fun hC hlt2 => ?_, fun h2C hlt3 => ?_⟩
  · -- (i) `e_k < C` forces `p`
    cases hx : ℓ.getD k Letter.p with
    | p => rfl
    | q =>
      exfalso
      have herr := err_of_q ℓ n d k hk hx
      linarith [hb.1]
  · -- (ii) `C ≤ e_k < 2C` forces `q`, not preceded by `q`
    have hq : ℓ.getD k Letter.p = Letter.q := by
      cases hx : ℓ.getD k Letter.p with
      | p =>
        exfalso
        have herr := err_of_p ℓ n d k hk (by rw [hx]; decide)
        have hεn : ¬ ((d + n) * qPrefix ℓ k - 2 * n * (k : ℤ) < 2 * n) := fun h => by
          have := hl.mpr h
          rw [hx] at this
          exact absurd this (by decide)
        push Not at hεn
        linarith [hb.2]
      | q => rfl
    refine ⟨hq, ?_⟩
    rintro ⟨hk0, hprev⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hf := (flag_iff_of_q ℓ n d hB j hk hq).mp (by simpa using hprev)
    push_cast at hlt2
    linarith
  · -- (iii) `2C ≤ e_k < L` forces `q` preceded by `q`
    have hq : ℓ.getD k Letter.p = Letter.q := by
      cases hx : ℓ.getD k Letter.p with
      | p =>
        exfalso
        have herr := err_of_p ℓ n d k hk (by rw [hx]; decide)
        have hεn : ¬ ((d + n) * qPrefix ℓ k - 2 * n * (k : ℤ) < 2 * n) := fun h => by
          have := hl.mpr h
          rw [hx] at this
          exact absurd this (by decide)
        push Not at hεn
        linarith
      | q => rfl
    have hk0 : k ≠ 0 := by
      intro h0
      subst h0
      have herr := err_of_q ℓ n d 0 hk hq
      linarith [hzero]
    refine ⟨hq, hk0, ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact (flag_iff_of_q ℓ n d hB j hk hq).mpr (by push_cast at h2C; linarith)

/-- The cursor value is the unique integer `B` with `L B − 2n j ∈ [0, L)`. -/
theorem qPrefix_eq_of_err (ℓ : BinaryWord) (n d : ℤ) (hB : CursorB ℓ n d) (hL : 0 < d + n) (j : ℕ) (hj : j ≤ ℓ.length)
    (B : ℤ) (h0 : 0 ≤ (d + n) * B - 2 * n * (j : ℤ)) (h1 : (d + n) * B - 2 * n * (j : ℤ) < d + n) :
    qPrefix ℓ j = B := by
  obtain ⟨e0, e1⟩ := eps_bounds ℓ n d hB j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (d + n) * qPrefix ℓ j ≤ (d + n) * (B - 1) :=
      mul_le_mul_of_nonneg_left (by omega) hL.le
    nlinarith
  · have : (d + n) * (B + 1) ≤ (d + n) * qPrefix ℓ j :=
      mul_le_mul_of_nonneg_left (by omega) hL.le
    nlinarith

/-- **A site of the forward string.** If the offset `b` is admissible for the error `e` of its index `k`, and the origin of `(x, y)`
is that of `b`, then `(x, y)` is a site of the forward string. -/
theorem mem_of_cursor (ℓ' : BinaryWord) (n d : ℤ) (hB : CursorB (Letter.q :: ℓ') n d) (hnd : n < d) (k : ℕ)
    (hk : k < (Letter.q :: ℓ').length) (b : ℤ × ℤ) (x y : ℤ) (hB0 : qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - b.2)
    (hbox : ((d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < d - n →
        0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 2) ∧
      (d - n ≤ (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) →
        (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < 2 * (d - n) →
        0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∧
      (2 * (d - n) ≤ (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) →
        (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < d + n →
        ((0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2 ∧ b.2 ≤ 1) ∨ b = (-1, 1) ∨ b = (1, -1))))
    (hxy : x = 2 * (k : ℤ) + 1 - (y + 1 - b.2) + b.1) :
    (x, y) ∈ stringSites false false (Letter.q :: ℓ') := by
  rw [stringSites_fwd_iff_cons]
  obtain ⟨f1, f2, f3⟩ := fwd_type (Letter.q :: ℓ') n d hB hnd k hk
  rw [hB0] at f1 f2 f3
  refine ⟨k, hk, b, ?_, ?_⟩
  · by_cases hp : (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < d - n
    · exact Or.inl ⟨f1 hp, hbox.1 hp⟩
    · by_cases hq : (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < 2 * (d - n)
      · exact Or.inr (Or.inl ⟨(f2 (not_lt.mp hp) hq).1, (f2 (not_lt.mp hp) hq).2, hbox.2.1 (not_lt.mp hp) hq⟩)
      · have hlt : (d + n) * (y + 1 - b.2) - 2 * n * ((k : ℤ) + 1) < d + n := by
          have h := (eps_bounds (Letter.q :: ℓ') n d hB (k + 1) (by omega)).2
          push_cast at h
          rw [hB0] at h
          exact h
        exact Or.inr (Or.inr ⟨(f3 (not_lt.mp hq) hlt).1, (f3 (not_lt.mp hq) hlt).2.1,
          (f3 (not_lt.mp hq) hlt).2.2, hbox.2.2 (not_lt.mp hq) hlt⟩)
  · rw [hB0, hxy]
    exact Prod.ext rfl (by ring)

/-- **The horizontal band is covered.** A site of `H` with `a ≤ t` (its `t`-coordinate in the band) is a site of the forward
horizontal string of `q :: ℓ'`. The offset is `(0,0)` on even sites with `t ≤ C`, the tip `(1,−1)` on even sites with `C < t`, and
`(1,0)` on odd sites. -/
theorem tband_stringSites (n d μ : ℤ) (ℓ' : BinaryWord) (hn : 0 < n) (hnd : n < d)
    (hB : CursorB (Letter.q :: ℓ') n d)
    (hlen : (((Letter.q :: ℓ').length : ℕ) : ℤ) * 2 = μ * (d + n))
    (hμ1 : (d + n) % 2 = 1 → μ = 2) (hμ0 : (d + n) % 2 = 0 → μ = 1)
    (x y t s a l : ℤ) (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hta : a ≤ t) (htL : t ≤ d + n - a) (hsl : l ≤ s)
    (hsu : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - l) :
    (x, y) ∈ stringSites false false (Letter.q :: ℓ') := by
  obtain ⟨hm1, hm2⟩ := tband_m_bounds n d μ x y t s a l hn hnd hμ1 hμ0 ht hs hsite hta htL hsl hsu
  have hL0 : 0 < d + n := by omega
  generalize hM : μ * (d + n) = M at hm2 hlen
  have hkn : ((Letter.q :: ℓ').length) = ℓ'.length + 1 := by simp
  rcases Int.emod_two_eq_zero_or_one (x + y) with hpar | hpar
  · -- even site: the index `k` has `2k = x + y`
    obtain ⟨ha, hl⟩ := hsite.2 hpar
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (x + y) / 2 := ⟨((x + y) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk2 : 2 * (k : ℤ) = x + y := by omega
    have hkl : k < (Letter.q :: ℓ').length := by
      have h1 : (k : ℤ) < (((Letter.q :: ℓ').length : ℕ) : ℤ) := by omega
      exact_mod_cast h1
    have ha1 : 1 ≤ a := by rw [ha]; omega
    have hkn1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    by_cases ht0 : t ≤ d - n
    · -- the offset `(0, 0)`
      have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 := by
        apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 1)
        · have e : (d + n) * (y + 1) - 2 * n * (((k + 1 : ℕ)) : ℤ) = d - n - t := by
            rw [hkn1]
            linear_combination (-(n : ℤ)) * hk2 + ht
          rw [e]
          linarith
        · have e : (d + n) * (y + 1) - 2 * n * (((k + 1 : ℕ)) : ℤ) = d - n - t := by
            rw [hkn1]
            linear_combination (-(n : ℤ)) * hk2 + ht
          rw [e]
          linarith
      refine mem_of_cursor ℓ' n d hB hnd k hkl (0, 0) x y ?_ ⟨?_, ?_, ?_⟩ ?_
      · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - 0
        rw [hcursor]
        ring
      · intro _
        dsimp only
        norm_num
      · intro _ _
        dsimp only
        norm_num
      · intro _ _
        dsimp only
        norm_num
      · dsimp only
        linarith
    · -- the tip `(1, −1)`
      have ht2n : t ≤ 2 * n := by
        rw [ha] at htL
        omega
      have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 2 := by
        apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 2)
        · have e : (d + n) * (y + 2) - 2 * n * (((k + 1 : ℕ)) : ℤ) = 2 * d - t := by
            rw [hkn1]
            linear_combination (-(n : ℤ)) * hk2 + ht
          rw [e]
          linarith
        · have e : (d + n) * (y + 2) - 2 * n * (((k + 1 : ℕ)) : ℤ) = 2 * d - t := by
            rw [hkn1]
            linear_combination (-(n : ℤ)) * hk2 + ht
          rw [e]
          linarith
      refine mem_of_cursor ℓ' n d hB hnd k hkl (1, -1) x y ?_ ⟨?_, ?_, ?_⟩ ?_
      · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - (-1)
        rw [hcursor]
        ring
      · intro h
        dsimp only at h ⊢
        exfalso
        nlinarith
      · intro h1 h2
        dsimp only at h1 h2 ⊢
        exfalso
        nlinarith
      · intro _ _
        dsimp only
        exact Or.inr (Or.inr rfl)
      · dsimp only
        linarith
  · -- odd site: the index `k` has `2k + 1 = x + y`
    obtain ⟨ha, hl⟩ := hsite.1 hpar
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = (x + y - 1) / 2 := ⟨((x + y - 1) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hk2 : 2 * (k : ℤ) + 1 = x + y := by omega
    have hkl : k < (Letter.q :: ℓ').length := by
      have h1 : (k : ℤ) < (((Letter.q :: ℓ').length : ℕ) : ℤ) := by omega
      exact_mod_cast h1
    have hkn1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
    have hE : (d + n) * (y + 1) - 2 * n * ((k : ℤ) + 1) = d - t := by
      linear_combination (-(n : ℤ)) * hk2 + ht
    have hcursor : qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 := by
      apply qPrefix_eq_of_err (Letter.q :: ℓ') n d hB hL0 (k + 1) (by omega) (y + 1)
      · rw [hkn1, hE]
        linarith
      · rw [hkn1, hE]
        linarith
    refine mem_of_cursor ℓ' n d hB hnd k hkl (1, 0) x y ?_ ⟨?_, ?_, ?_⟩ ?_
    · show qPrefix (Letter.q :: ℓ') (k + 1) = y + 1 - 0
      rw [hcursor]
      ring
    · intro h
      dsimp only
      norm_num
    · intro h1 h2
      dsimp only
      norm_num
    · intro h1 h2
      exfalso
      dsimp only at h1 h2
      linarith [hE, ha, hta]
    · dsimp only
      linarith

end FLatticePaper.Tiles.SiteFwdCover
