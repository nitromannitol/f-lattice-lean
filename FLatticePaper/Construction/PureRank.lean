import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-! # The explicit strict rank `Q_minus` of the reciprocal family (task 118, W1 base; w3's pure3 note
`UNIFORM_GLOBAL_RECIPROCAL_STRICT_RANK`, and its z3 model `prove_rank.py`).

Parameters: the odd denominator `d ≥ 3`; deck vectors `U = (d, 1)` and `V = (1 − d, d + 1)`; aliases `(i, j)` with
`i ∈ [−2, 2]`, `j ∈ [−1, 1]`; `shiftP d p i j = p + i U + j V`.

* `IsHc`, `IsVc`, `IsFreeP`: the H trace `{(j,0) : 1 ≤ j ≤ d}` and the V path `{(0,0)} ∪ {(1−j, j) : 1 ≤ j < d} ∪ {(2−d, d)}`.
* `NativeP`: the native domain `[2−d, d] × [0, d+1]` with `1 ≤ x + y ≤ d + 2`, plus the two inserted corners.
* `IsRepP`: the representative of its alias class: a free point, or a native point with no free alias translate and no lexicographically
  larger native alias translate.
* `valMinus`: the value of `Q_minus` on a representative.
* `RankOf d p r`: `r` is the rank of `p`, the value at the alias translate that is a representative, with the deck correction
  `− i·2d + j·2(d+1)`.

Proved here: the representative of a free point is unique (no nonzero alias translate of a free point is free or a representative), so the
rank of a free point is its own `valMinus`; and the two free-to-free gates `H_even` (`(x,0) → (x−1,0)`, drop 1) and `V_{d−1} → V_last`
(drop 1). The bulk gates (targets outside the free classes) are the next stage. -/

namespace FLatticePaper.PureRank

open Classical

abbrev Pt := ℤ × ℤ

/-- The alias shift `p + i U + j V`. -/
def shiftP (d : ℤ) (p : Pt) (i j : ℤ) : Pt :=
  (p.1 + i * d + j * (1 - d), p.2 + i + j * (d + 1))

/-- The aliases `(i, j)`. -/
def IsAlias (i j : ℤ) : Prop := -2 ≤ i ∧ i ≤ 2 ∧ -1 ≤ j ∧ j ≤ 1

/-- The H trace. -/
def IsHc (d : ℤ) (p : Pt) : Prop := p.2 = 0 ∧ 1 ≤ p.1 ∧ p.1 ≤ d

/-- The V path. -/
def IsVc (d : ℤ) (p : Pt) : Prop :=
  p = (0, 0) ∨ (p.1 + p.2 = 1 ∧ 1 ≤ p.2 ∧ p.2 < d) ∨ p = (2 - d, d)

/-- The free classes: the H trace and the V path. -/
def IsFreeP (d : ℤ) (p : Pt) : Prop := IsHc d p ∨ IsVc d p

/-- The native domain, with the two inserted corners. -/
def NativeP (d : ℤ) (p : Pt) : Prop :=
  (2 - d ≤ p.1 ∧ p.1 ≤ d ∧ 0 ≤ p.2 ∧ p.2 ≤ d + 1 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ d + 2) ∨
    p = (0, 0) ∨ p = (2, d + 1)

/-- `a` is lexicographically larger than `p` (first coordinate, then second). -/
def LexGt (a p : Pt) : Prop := p.1 < a.1 ∨ (a.1 = p.1 ∧ p.2 < a.2)

/-- `p` is the representative of its alias class. -/
def IsRepP (d : ℤ) (p : Pt) : Prop :=
  IsFreeP d p ∨
    (NativeP d p ∧ (∀ i j, IsAlias i j → ¬ IsFreeP d (shiftP d p i j)) ∧
      (∀ i j, IsAlias i j → NativeP d (shiftP d p i j) → ¬ LexGt (shiftP d p i j) p))

/-- The value of `Q_minus` on a representative: H `2x + p₀`, V `−2y − p₀`, the line `x + y = d + 1` (`x ≥ 1`) `2x`,
`x ≤ 0` `2x − 4 + p₀`, otherwise `4d − 4 − 2x + p₀`, with `p₀ = (x + y) mod 2`. -/
noncomputable def valMinus (d : ℤ) (p : Pt) : ℤ :=
  let p0 := (p.1 + p.2) % 2
  if IsHc d p then 2 * p.1 + p0
  else if IsVc d p then -2 * p.2 - p0
  else if p.1 + p.2 = d + 1 ∧ 1 ≤ p.1 then 2 * p.1
  else if p.1 ≤ 0 then 2 * p.1 - 4 + p0
  else 4 * d - 4 - 2 * p.1 + p0

/-- `r` is the rank of `p`: the `Q_minus` value at the alias translate that is a representative, with the deck correction. -/
def RankOf (d : ℤ) (p : Pt) (r : ℤ) : Prop :=
  ∃ i j, IsAlias i j ∧ IsRepP d (shiftP d p i j) ∧
    r = valMinus d (shiftP d p i j) - i * (2 * d) + j * (2 * (d + 1))

/-- **Free classes are alias-separated.** For a free point, a nonzero alias translate is not free. -/
theorem free_translate_not_free (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsFreeP d p) (i j : ℤ)
    (hi : IsAlias i j) (hne : ¬ (i = 0 ∧ j = 0)) : ¬ IsFreeP d (shiftP d p i j) := by
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  obtain ⟨x, y⟩ := p
  simp only [IsFreeP, IsHc, IsVc, shiftP, Prod.mk.injEq] at hp hne ⊢
  interval_cases i <;> interval_cases j <;> omega

/-- A nonzero alias translate of a free point is not a representative. -/
theorem not_rep_of_free_translate (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsFreeP d p) (i j : ℤ)
    (hi : IsAlias i j) (hne : ¬ (i = 0 ∧ j = 0)) : ¬ IsRepP d (shiftP d p i j) := by
  intro hr
  rcases hr with hf | ⟨-, hnf, -⟩
  · exact free_translate_not_free d hd p hp i j hi hne hf
  · have hinv : shiftP d (shiftP d p i j) (-i) (-j) = p := by
      obtain ⟨x, y⟩ := p
      simp only [shiftP, Prod.mk.injEq]
      constructor <;> ring
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
    exact hnf (-i) (-j) ⟨by omega, by omega, by omega, by omega⟩ (by rw [hinv]; exact hp)

/-- The rank of a free point is its own `Q_minus` value. -/
theorem rankOf_free (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsFreeP d p) (r : ℤ) (h : RankOf d p r) :
    r = valMinus d p := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := h
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [shiftP]
  · exact absurd hrep (not_rep_of_free_translate d hd p hp i j hi h0)

/-- The H trace point `(x, 0)` has the value `2x` (the parity of `x` is even). -/
theorem valMinus_H_even (d x : ℤ) (hx1 : 2 ≤ x) (hxd : x ≤ d) (hev : x % 2 = 0) :
    valMinus d (x, 0) = 2 * x := by
  unfold valMinus
  rw [if_pos (show IsHc d (x, 0) from ⟨rfl, by omega, hxd⟩)]
  simp only
  omega

/-- The H trace point `(x − 1, 0)` for even `x ≥ 2` has value `2x − 1`. -/
theorem valMinus_H_odd (d x : ℤ) (hx : 1 ≤ x) (hxd : x ≤ d) (hodd : x % 2 = 1) :
    valMinus d (x, 0) = 2 * x + 1 := by
  unfold valMinus
  rw [if_pos (show IsHc d (x, 0) from ⟨rfl, by omega, hxd⟩)]
  simp only
  omega

/-- **Gate (H, even).** For an even `x ≥ 2` on the H trace, the W-input `(x−1, 0)` (also on the H trace) drops the rank by one. -/
theorem gate_H_even (d : ℤ) (hd : 3 ≤ d) (x r r' : ℤ) (hx1 : 2 ≤ x) (hxd : x ≤ d) (hev : x % 2 = 0)
    (hr : RankOf d (x, 0) r) (hr' : RankOf d (x - 1, 0) r') : r' < r := by
  have hfree : IsFreeP d (x, 0) := Or.inl ⟨rfl, by omega, hxd⟩
  have hfree' : IsFreeP d (x - 1, 0) := Or.inl ⟨rfl, by omega, by omega⟩
  rw [rankOf_free d hd _ hfree r hr, rankOf_free d hd _ hfree' r' hr']
  have h1 := valMinus_H_even d x hx1 hxd hev
  have h2 : valMinus d (x - 1, 0) = 2 * x - 1 := by
    unfold valMinus
    rw [if_pos (show IsHc d (x - 1, 0) from ⟨rfl, by omega, by omega⟩)]
    simp only
    omega
  rw [h1, h2]
  omega

/-- **Gate (V path).** The V point `V_{d−1} = (2−d, d−1)` (odd) sends its north input to `V_last = (2−d, d)`: drop one. -/
theorem gate_V_last (d : ℤ) (hd : 3 ≤ d) (r r' : ℤ) (hr : RankOf d (2 - d, d - 1) r) (hr' : RankOf d (2 - d, d) r') :
    r' < r := by
  have hfree : IsFreeP d (2 - d, d - 1) := Or.inr (Or.inr (Or.inl ⟨by ring, by omega, by omega⟩))
  have hfree' : IsFreeP d (2 - d, d) := Or.inr (Or.inr (Or.inr rfl))
  rw [rankOf_free d hd _ hfree r hr, rankOf_free d hd _ hfree' r' hr']
  have h1 : valMinus d (2 - d, d - 1) = -2 * d + 1 := by
    unfold valMinus
    rw [if_neg (show ¬ IsHc d (2 - d, d - 1) from fun h => by have := h.1; omega)]
    rw [if_pos (show IsVc d (2 - d, d - 1) from Or.inr (Or.inl ⟨by ring, by omega, by omega⟩))]
    simp only
    omega
  have h2 : valMinus d (2 - d, d) = -2 * d := by
    unfold valMinus
    rw [if_neg (show ¬ IsHc d (2 - d, d) from fun h => by have := h.1; omega)]
    rw [if_pos (show IsVc d (2 - d, d) from Or.inr (Or.inr rfl))]
    simp only
    omega
  rw [h1, h2]
  omega

/-- The prescribed retained direction at a free point: H even `W`, H odd `S` (and `N` at the endpoint `(d,0)`), V even `W`, V odd `N`. -/
noncomputable def prescribedFree (d : ℤ) (p : Pt) : Pt :=
  if (p.1 + p.2) % 2 = 0 then (-1, 0)
  else if IsHc d p then (if p.1 = d then (0, 1) else (0, -1))
  else (0, 1)

/-- **Free-internal gates.** If a free point retains its prescribed direction and the target is free too, the rank drops. -/
theorem free_internal_gate (d : ℤ) (hd : 3 ≤ d) (hdodd : d % 2 = 1) (x y dx dy : ℤ) (hp : IsFreeP d (x, y))
    (hpres : (dx, dy) = prescribedFree d (x, y)) (hq : IsFreeP d (x + dx, y + dy))
    (r r' : ℤ) (hr : RankOf d (x, y) r) (hr' : RankOf d (x + dx, y + dy) r') : r' < r := by
  unfold prescribedFree at hpres
  by_cases hev : (x + y) % 2 = 0
  · rw [if_pos hev] at hpres
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpres
    rcases hp with ⟨hy, hx1, hxd⟩ | hV
    · subst hy
      have hxe : x % 2 = 0 := by omega
      refine gate_H_even d hd x r r' (by omega) hxd hxe hr ?_
      rw [show x + -1 = x - 1 by ring] at hr'
      exact hr'
    · exfalso
      simp only [IsFreeP, IsHc, IsVc, Prod.mk.injEq] at hq hV
      omega
  · rw [if_neg hev] at hpres
    by_cases hHc : IsHc d (x, y)
    · rw [if_pos hHc] at hpres
      obtain ⟨hy, hx1, hxd⟩ := hHc
      by_cases hxdd : x = d
      · rw [if_pos hxdd] at hpres
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpres
        exfalso
        simp only [IsFreeP, IsHc, IsVc, Prod.mk.injEq] at hq
        omega
      · rw [if_neg hxdd] at hpres
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpres
        exfalso
        simp only [IsFreeP, IsHc, IsVc, Prod.mk.injEq] at hq
        omega
    · rw [if_neg hHc] at hpres
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpres
      have hVp : IsVc d (x, y) := by
        rcases hp with h | h
        · exact absurd h hHc
        · exact h
      simp only [IsVc, IsFreeP, IsHc, Prod.mk.injEq] at hVp hq
      have hxd1 : x = 2 - d := by omega
      have hyd1 : y = d - 1 := by omega
      subst hxd1
      subst hyd1
      refine gate_V_last d hd r r' hr ?_
      rw [show 2 - d + 0 = 2 - d by ring, show d - 1 + 1 = d by ring] at hr'
      exact hr'

/-- Lexicographic order is total on pairs: two points neither lex-larger than the other are equal. -/
theorem eq_of_not_lexGt (a p : Pt) (h1 : ¬ LexGt a p) (h2 : ¬ LexGt p a) : a = p := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨p1, p2⟩ := p
  simp only [LexGt, Prod.mk.injEq] at h1 h2 ⊢
  omega

/-- The alias translation is injective: a nonzero alias moves every point. -/
theorem shiftP_ne_self (d : ℤ) (hd : 3 ≤ d) (p : Pt) (i j : ℤ) (hi : IsAlias i j) (hne : ¬ (i = 0 ∧ j = 0)) :
    shiftP d p i j ≠ p := by
  intro h
  obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
  obtain ⟨x, y⟩ := p
  simp only [shiftP, Prod.mk.injEq] at h hne
  interval_cases i <;> interval_cases j <;> omega

/-- **Bulk representatives are alias-isolated.** If `p` is a non-free representative, no nonzero alias translate is a representative. -/
theorem not_rep_of_bulk_translate (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsRepP d p) (hpf : ¬ IsFreeP d p)
    (i j : ℤ) (hi : IsAlias i j) (hne : ¬ (i = 0 ∧ j = 0)) : ¬ IsRepP d (shiftP d p i j) := by
  obtain ⟨hpn, hpfree, hplex⟩ : NativeP d p ∧ (∀ i j, IsAlias i j → ¬ IsFreeP d (shiftP d p i j)) ∧
      (∀ i j, IsAlias i j → NativeP d (shiftP d p i j) → ¬ LexGt (shiftP d p i j) p) := by
    rcases hp with hf | h
    · exact absurd hf hpf
    · exact h
  intro hq
  rcases hq with hqf | ⟨hqn, hqfree, hqlex⟩
  · exact hpfree i j hi hqf
  · -- the translate back to `p` is native and not lex-smaller than `shiftP p i j`
    have hinv : shiftP d (shiftP d p i j) (-i) (-j) = p := by
      obtain ⟨x, y⟩ := p
      simp only [shiftP, Prod.mk.injEq]
      constructor <;> ring
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hi
    have hback : ¬ LexGt p (shiftP d p i j) := by
      have := hqlex (-i) (-j) ⟨by omega, by omega, by omega, by omega⟩ (by rw [hinv]; exact hpn)
      rw [hinv] at this
      exact this
    have hfwd : ¬ LexGt (shiftP d p i j) p := hplex i j ⟨hi1, hi2, hj1, hj2⟩ hqn
    exact shiftP_ne_self d hd p i j ⟨hi1, hi2, hj1, hj2⟩ hne
      (eq_of_not_lexGt _ _ hfwd hback)

/-- A bulk representative has rank its own `valMinus`. -/
theorem rankOf_bulk (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsRepP d p) (hpf : ¬ IsFreeP d p) (r : ℤ)
    (h : RankOf d p r) : r = valMinus d p := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := h
  by_cases h0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [shiftP]
  · exact absurd hrep (not_rep_of_bulk_translate d hd p hp hpf i j hi h0)

/-- The existence half: a representative point has the rank of its own `valMinus`. -/
theorem rankOf_self (d : ℤ) (p : Pt) (hp : IsRepP d p) : RankOf d p (valMinus d p) := by
  refine ⟨0, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · simpa [shiftP] using hp
  · simp [shiftP]

/-- The rank of a translate of a representative, through the translating alias. -/
theorem rankOf_translate (d : ℤ) (p : Pt) (i j : ℤ) (hi : IsAlias i j) (hrep : IsRepP d (shiftP d p i j)) :
    RankOf d p (valMinus d (shiftP d p i j) - i * (2 * d) + j * (2 * (d + 1))) :=
  ⟨i, j, hi, hrep, rfl⟩

/-- Native points lie in the strip `2 − d ≤ x ≤ d`, `0 ≤ y ≤ d + 1`. -/
theorem nativeP_bounds (d : ℤ) (hd : 2 ≤ d) (p : Pt) (hp : NativeP d p) :
    2 - d ≤ p.1 ∧ p.1 ≤ d ∧ 0 ≤ p.2 ∧ p.2 ≤ d + 1 := by
  obtain ⟨x, y⟩ := p
  rcases hp with ⟨h1, h2, h3, h4, -, -⟩ | h | h
  · exact ⟨h1, h2, h3, h4⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, by omega, by omega⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- Free points are native. -/
theorem freeP_native (d : ℤ) (hd : 3 ≤ d) (p : Pt) (hp : IsFreeP d p) : NativeP d p := by
  obtain ⟨x, y⟩ := p
  simp only [IsFreeP, IsHc, IsVc, NativeP, Prod.mk.injEq] at hp ⊢
  omega

/-- The composition of two alias shifts is the shift by the sum. -/
theorem shiftP_shiftP (d : ℤ) (p : Pt) (i j i' j' : ℤ) :
    shiftP d (shiftP d p i j) i' j' = shiftP d p (i + i') (j + j') := by
  obtain ⟨x, y⟩ := p
  simp only [shiftP, Prod.mk.injEq]
  constructor <;> ring

/-- **The finite window (the note's complete alias window).** Two native points differ by an alias: `|i| ≤ 2`, `|j| ≤ 1`.
Proof by the deck coordinates: `i·T = (d+1)Δx + (d−1)Δy` and `j·T = dΔy − Δx` with `T = d² + 2d − 1`. -/
theorem window_alias (d : ℤ) (hd : 3 ≤ d) (p q : Pt) (hp : NativeP d p) (hq : NativeP d q) (i j : ℤ)
    (h : q = shiftP d p i j) : -2 ≤ i ∧ i ≤ 2 ∧ -1 ≤ j ∧ j ≤ 1 := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := nativeP_bounds d (by omega) p hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := nativeP_bounds d (by omega) q hq
  have hT : (0:ℤ) < d * d + 2 * d - 1 := by nlinarith
  have hi : i * (d * d + 2 * d - 1) = (d + 1) * (q.1 - p.1) + (d - 1) * (q.2 - p.2) := by
    subst h
    simp only [shiftP]
    ring
  have hj : j * (d * d + 2 * d - 1) = d * (q.2 - p.2) - (q.1 - p.1) := by
    subst h
    simp only [shiftP]
    ring
  have hdx1 : q.1 - p.1 ≤ 2 * d - 2 := by omega
  have hdx2 : -(2 * d - 2) ≤ q.1 - p.1 := by omega
  have hdy1 : q.2 - p.2 ≤ d + 1 := by omega
  have hdy2 : -(d + 1) ≤ q.2 - p.2 := by omega
  have hd1 : (0:ℤ) ≤ d + 1 := by omega
  have hd2 : (0:ℤ) ≤ d - 1 := by omega
  have hd0 : (0:ℤ) ≤ d := by omega
  have hA1 : (d + 1) * (q.1 - p.1) ≤ (d + 1) * (2 * d - 2) := mul_le_mul_of_nonneg_left hdx1 hd1
  have hA2 : -((d + 1) * (2 * d - 2)) ≤ (d + 1) * (q.1 - p.1) := by nlinarith
  have hB1 : (d - 1) * (q.2 - p.2) ≤ (d - 1) * (d + 1) := mul_le_mul_of_nonneg_left hdy1 hd2
  have hB2 : -((d - 1) * (d + 1)) ≤ (d - 1) * (q.2 - p.2) := by nlinarith
  have hC1 : d * (q.2 - p.2) ≤ d * (d + 1) := mul_le_mul_of_nonneg_left hdy1 hd0
  have hC2 : -(d * (d + 1)) ≤ d * (q.2 - p.2) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc
    have h3 : (3:ℤ) ≤ -i := by omega
    have h4 : 3 * (d * d + 2 * d - 1) ≤ -i * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (3:ℤ) ≤ i := by omega
    have h4 : 3 * (d * d + 2 * d - 1) ≤ i * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (2:ℤ) ≤ -j := by omega
    have h4 : 2 * (d * d + 2 * d - 1) ≤ -j * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith
  · by_contra hc
    have h3 : (2:ℤ) ≤ j := by omega
    have h4 : 2 * (d * d + 2 * d - 1) ≤ j * (d * d + 2 * d - 1) := mul_le_mul_of_nonneg_right h3 hT.le
    nlinarith

/-- **Rank uniqueness.** The rank of a point is determined: two alias translates that are representatives coincide,
because their difference is an alias (the window) and a nonzero alias translate of a representative is not a representative. -/
theorem rankOf_unique (d : ℤ) (hd : 3 ≤ d) (p : Pt) (r r' : ℤ) (h : RankOf d p r) (h' : RankOf d p r') : r = r' := by
  obtain ⟨i, j, hi, hrep, rfl⟩ := h
  obtain ⟨i', j', hi', hrep', rfl⟩ := h'
  have hnat : ∀ a b, IsAlias a b → IsRepP d (shiftP d p a b) → NativeP d (shiftP d p a b) := by
    intro a b _ hr
    rcases hr with hf | ⟨hn, -, -⟩
    · exact freeP_native d hd _ hf
    · exact hn
  have hnq : NativeP d (shiftP d p i j) := hnat i j hi hrep
  have hnq' : NativeP d (shiftP d p i' j') := hnat i' j' hi' hrep'
  by_cases hk : i' - i = 0 ∧ j' - j = 0
  · obtain ⟨hk1, hk2⟩ := hk
    have e1 : i' = i := by omega
    have e2 : j' = j := by omega
    subst e1; subst e2
    rfl
  · exfalso
    set q := shiftP d p i j with hqdef
    have hq' : shiftP d p i' j' = shiftP d q (i' - i) (j' - j) := by
      rw [hqdef, shiftP_shiftP]
      congr 1 <;> ring_nf
    have hwin := window_alias d hd q (shiftP d p i' j') hnq hnq' (i' - i) (j' - j) hq'
    have hki : IsAlias (i' - i) (j' - j) := by
      obtain ⟨a1, a2, a3, a4⟩ := hwin
      exact ⟨a1, a2, a3, a4⟩
    rw [hq'] at hrep'
    by_cases hqf : IsFreeP d q
    · exact not_rep_of_free_translate d hd q hqf _ _ hki hk hrep'
    · exact not_rep_of_bulk_translate d hd q hrep hqf _ _ hki hk hrep'

/-! ## The families of the native domain (step (ii))

The native domain splits into six families: free points (F0), the top row `y = d+1, x ≤ 1` (F2, represented by the H point
`(x+d−1, 0)`), the corner `(2,d+1)` (F3, represented by `(2−d, d)`), the anti-diagonal `x+y = d+2, y ≤ d` (F4, represented by
`(x−d, y−1)`), the point `(d,1)` (F5, represented by `(0,0)`), and the interior (F1, its own representative). -/

/-- An interior point is its own representative. -/
theorem rep_interior (d : ℤ) (x y : ℤ) (hn : NativeP d (x, y)) (hf : ¬ IsFreeP d (x, y))
    (hy : y ≤ d) (h4 : x + y ≠ d + 2) (h5 : ¬ (x = d ∧ y = 1)) : IsRepP d (x, y) := by
  have hn' := hn
  unfold NativeP at hn'
  simp only [Prod.mk.injEq] at hn'
  unfold IsFreeP IsHc IsVc at hf
  simp only [Prod.mk.injEq] at hf
  right
  refine ⟨hn, ?_, ?_⟩
  · intro i j hij hfree
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
    unfold IsFreeP IsHc IsVc at hfree
    simp only [shiftP, Prod.mk.injEq] at hfree
    interval_cases i <;> interval_cases j <;> omega
  · intro i j hij hnat hlex
    obtain ⟨hi1, hi2, hj1, hj2⟩ := hij
    unfold NativeP at hnat
    simp only [shiftP, Prod.mk.injEq] at hnat
    unfold LexGt at hlex
    simp only [shiftP] at hlex
    interval_cases i <;> interval_cases j <;> omega

/-- The top row point `(x, d+1)` with `x ≤ 1` is translated by `(0,−1)` onto the H point `(x+d−1, 0)`. -/
theorem rankOf_top (d : ℤ) (x : ℤ) (hx1 : 2 - d ≤ x) (hx2 : x ≤ 1) :
    RankOf d (x, d + 1) (valMinus d (x + d - 1, 0) - 2 * (d + 1)) := by
  have hs : shiftP d (x, d + 1) 0 (-1) = (x + d - 1, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨0, -1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    left
    unfold IsHc
    exact ⟨rfl, by show 1 ≤ x + d - 1; omega, by show x + d - 1 ≤ d; omega⟩
  · rw [hs]
    ring

/-- The corner `(2, d+1)` is translated by `(−1,0)` onto the V-last point `(2−d, d)`. -/
theorem rankOf_corner (d : ℤ) :
    RankOf d (2, d + 1) (valMinus d (2 - d, d) + 2 * d) := by
  have hs : shiftP d (2, d + 1) (-1) 0 = (2 - d, d) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [hs]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inr (Or.inr rfl)
  · rw [hs]
    ring

/-- The anti-diagonal point `(x, y)` with `x + y = d+2` and `y ≤ d` is translated by `(−1,0)` onto the V point `(x−d, y−1)`. -/
theorem rankOf_anti (d : ℤ) (x y : ℤ) (hs : x + y = d + 2) (hxd : x ≤ d) (hyd : y ≤ d) :
    RankOf d (x, y) (valMinus d (x - d, y - 1) + 2 * d) := by
  have e : shiftP d (x, y) (-1) 0 = (x - d, y - 1) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    simp only [Prod.mk.injEq]
    omega
  · rw [e]
    ring

/-- The point `(d,1)` is translated by `(−1,0)` onto the origin. -/
theorem rankOf_fifth (d : ℤ) :
    RankOf d (d, 1) (valMinus d (0, 0) + 2 * d) := by
  have e : shiftP d (d, 1) (-1) 0 = (0, 0) := by
    simp only [shiftP, Prod.mk.injEq]
    constructor <;> ring
  refine ⟨-1, 0, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [e]
    left
    unfold IsFreeP
    right
    unfold IsVc
    exact Or.inl rfl
  · rw [e]
    ring

/-- The rank of a native point, by family. -/
noncomputable def qRank (d : ℤ) (p : Pt) : ℤ :=
  if IsFreeP d p then valMinus d p
  else if p.2 = d + 1 ∧ p.1 ≤ 1 then valMinus d (p.1 + d - 1, 0) - 2 * (d + 1)
  else if p = (2, d + 1) then valMinus d (2 - d, d) + 2 * d
  else if p.1 + p.2 = d + 2 then valMinus d (p.1 - d, p.2 - 1) + 2 * d
  else if p = (d, 1) then valMinus d (0, 0) + 2 * d
  else valMinus d p

/-- Every native point has its family rank as a rank. -/
theorem rankOf_qRank (d : ℤ) (hd : 3 ≤ d) (x y : ℤ) (hn : NativeP d (x, y)) :
    RankOf d (x, y) (qRank d (x, y)) := by
  have hb : 2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 := nativeP_bounds d (by omega) (x, y) hn
  obtain ⟨hx1, hx2, -, hy2⟩ := hb
  have hn' := hn
  unfold NativeP at hn'
  simp only [Prod.mk.injEq] at hn'
  simp only [qRank, Prod.mk.injEq]
  split_ifs with h1 h2 h3 h4 h5
  · exact rankOf_self d (x, y) (Or.inl h1)
  · obtain ⟨rfl, h2'⟩ := h2
    exact rankOf_top d x hx1 h2'
  · obtain ⟨rfl, rfl⟩ := h3
    exact rankOf_corner d
  · have hyd : y ≤ d := by omega
    exact rankOf_anti d x y h4 hx2 hyd
  · rw [h5.1, h5.2]
    exact rankOf_fifth d
  · have hyd : y ≤ d := by omega
    exact rankOf_self d (x, y) (rep_interior d x y hn h1 hyd h4 h5)

/-- **The rank of a native point is its family rank.** Any rank of a native point equals `qRank`, by the uniqueness of the rank. -/
theorem rankOf_eq_qRank (d : ℤ) (hd : 3 ≤ d) (x y : ℤ) (hn : NativeP d (x, y)) (r : ℤ)
    (h : RankOf d (x, y) r) : r = qRank d (x, y) :=
  rankOf_unique d hd (x, y) r _ h (rankOf_qRank d hd x y hn)

end FLatticePaper.PureRank
