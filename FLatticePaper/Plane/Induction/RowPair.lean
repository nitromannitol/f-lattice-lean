import FLatticePaper.Plane.Induction.RowAt
import FLatticePaper.Plane.Induction.FreeRows
import FLatticePaper.Plane.Induction.PairTranslate
import FLatticePaper.Plane.Induction.HChain

/-! # The pairs of the V labels of the minus row (Q1 l.21–30, item (b) of task w3)

For a field `F` on a child frame with the V cut `vpath` (`J` the rounded slip at `η = −1`, `P` the price):
* `hPc`: `P = c₀` on the free V cut (`PriceDeck.price_on_freeV`);
* `hpat`: `J(vpath k) = 0` for `k ≤ r` and `−1` for `r < k < L` (`WordVPattern.roundedSlip_minus_vpath`);
* the deck drifts `P(z + V) = P z`, `J(z + V) = J z − 1`.

Then every V label `j` of the minus row window `[r + 1 − L, r]` has `P(vAt j) = c₀` and `J(vAt j) = 0`: for `j ≥ 0`, `vAt j = vpath j`;
for `j < 0`, `vAt j = vpath (j + L) − V` (`RowAt.vAt_add_len`), and the drift turns `J = −1` into `0`. -/

namespace FLatticePaper.RowPair

open Farey FLatticePaper FLatticePaper.Induction

/-- **The V labels of the minus row have the pair `(c₀, 0)`.** -/
theorem V_label_pair (frame : ChildFrame) (J P : Site → ℤ) (r c0 : ℤ)
    (hJV : ∀ z, J (z + RowAt.Vvec frame) = J z + (-1))
    (hPV : ∀ z, P (z + RowAt.Vvec frame) = P z)
    (hr0 : 0 ≤ r) (hrL : r ≤ frame.child.den + frame.child.num - 2)
    (hpat : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num →
      J (VChain.vpath frame k) = if (k : ℤ) ≤ r then 0 else -1)
    (hPc : ∀ k : ℕ, (k : ℤ) < frame.child.den + frame.child.num → P (VChain.vpath frame k) = c0)
    (j : ℤ) (hj1 : r + 1 - (frame.child.den + frame.child.num) ≤ j) (hj2 : j ≤ r) :
    P (RowAt.vAt frame j) = c0 ∧ J (RowAt.vAt frame j) = 0 := by
  have hL : (0 : ℤ) < frame.child.den + frame.child.num := RowAt.len_pos frame
  by_cases hj0 : 0 ≤ j
  · -- `j ∈ [0, r]`: the label is the free V point `vpath j`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat, by omega⟩
    have hkL : (k : ℤ) < frame.child.den + frame.child.num := by omega
    rw [← hk, RowAt.vAt_nat frame k hkL]
    refine ⟨hPc k hkL, ?_⟩
    rw [hpat k hkL, if_pos (show (k : ℤ) ≤ r by omega)]
  · -- `j ∈ [r + 1 − L, −1]`: the label is `vpath (j + L) − V`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j + (frame.child.den + frame.child.num) :=
      ⟨(j + (frame.child.den + frame.child.num)).toNat, by omega⟩
    have hkL : (k : ℤ) < frame.child.den + frame.child.num := by omega
    have e := RowAt.vAt_add_len frame j
    rw [← hk, RowAt.vAt_nat frame k hkL] at e
    -- `vAt j + V = vpath k`
    have hP1 : P (RowAt.vAt frame j) = P (VChain.vpath frame k) := by
      rw [e, hPV]
    have hJ1 : J (VChain.vpath frame k) = J (RowAt.vAt frame j) + (-1) := by
      rw [e, hJV]
    refine ⟨hP1.trans (hPc k hkL), ?_⟩
    rw [hpat k hkL, if_neg (show ¬ ((k : ℤ) ≤ r) by omega)] at hJ1
    linarith

/-- The first coordinate of the H chain: `(hpath k).1 = k + 1`. -/
theorem hpath_fst (frame : ChildFrame) : ∀ k : ℕ, (HChain.hpath frame k).1 = (k : ℤ) + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [HChain.hpath_succ]
    unfold HChain.hsucc
    split_ifs <;> simp [ih]

/-- **The H labels of the minus row have the pair `(c₀, 0)`** for `j ∈ [1 − d, 0]`: `H_0` is the zero point, and for `j < 0`,
`hAt j = hpath (j + d) − U` (`RowAt.hAt_add_den`), with `P` drifting by `−1` and `J` unchanged along `U`. -/
theorem H_label_pair (frame : ChildFrame) (P J : Site → ℤ) (c0 : ℤ)
    (hPU : ∀ z, P (z + RowAt.Uvec frame) = P z + (-1))
    (hJU : ∀ z, J (z + RowAt.Uvec frame) = J z)
    (hPH : ∀ m : ℕ, (m : ℤ) < frame.child.den → m ≠ 0 → P (HChain.hpath frame m) = c0 - 1)
    (hPF : P FLatticePaper.Induction.hFirst = c0)
    (hJH : ∀ m : ℕ, (m : ℤ) < frame.child.den → J (HChain.hpath frame m) = 0)
    (j : ℤ) (hj1 : 1 - frame.child.den ≤ j) (hj2 : j ≤ 0) :
    P (RowAt.hAt frame j) = c0 ∧ J (RowAt.hAt frame j) = 0 := by
  have hd : (0 : ℤ) < frame.child.den := RowAt.den_pos frame
  by_cases hj0 : j = 0
  · subst hj0
    rw [RowAt.hAt_zero, HChain.hpath_zero]
    have h0 := hJH 0 (by omega)
    rw [HChain.hpath_zero] at h0
    exact ⟨hPF, h0⟩
  · -- `j ∈ [1 − d, −1]`: `m = j + d ∈ [1, d − 1]`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = j + frame.child.den := ⟨(j + frame.child.den).toNat, by omega⟩
    have hmd : (m : ℤ) < frame.child.den := by omega
    have hm0 : m ≠ 0 := by
      intro h0
      omega
    have e := RowAt.hAt_add_den frame j
    rw [← hm, RowAt.hAt_nat frame m (by omega)] at e
    -- e : hpath m = hAt j + U
    have hP1 : P (HChain.hpath frame m) = P (RowAt.hAt frame j) + (-1) := by
      rw [e, hPU]
    have hJ1 : J (HChain.hpath frame m) = J (RowAt.hAt frame j) := by
      rw [e, hJU]
    refine ⟨?_, ?_⟩
    · have := hPH m hmd hm0
      linarith
    · have := hJH m hmd
      linarith

/-- **Uniqueness of the `(c₀, 0)` lift.** Along the deck (`U` drifts `P` by `−1`, `V` drifts `J` by `−1`), a site `x` at the pair
`(c₀, 0)` has no other lift at that pair in its class: `x + m U + n V` at `(c₀, 0)` forces `m = n = 0`. -/
theorem lift_pair_unique (frame : ChildFrame) (P J : Site → ℤ) (c0 : ℤ)
    (hPU : ∀ z, P (z + RowAt.Uvec frame) = P z + (-1))
    (hJU : ∀ z, J (z + RowAt.Uvec frame) = J z)
    (hPV : ∀ z, P (z + RowAt.Vvec frame) = P z)
    (hJV : ∀ z, J (z + RowAt.Vvec frame) = J z + (-1))
    (x : Site) (hx : P x = c0 ∧ J x = 0) (m n : ℤ)
    (hg : P (x + m • RowAt.Uvec frame + n • RowAt.Vvec frame) = c0 ∧
      J (x + m • RowAt.Uvec frame + n • RowAt.Vvec frame) = 0) :
    m = 0 ∧ n = 0 := by
  have h1 := PairTranslate.drift_zsmul P (RowAt.Uvec frame) (-1) hPU m x
  have hPV0 : ∀ z, P (z + RowAt.Vvec frame) = P z + 0 := fun z => by rw [hPV z, add_zero]
  have hJU0 : ∀ z, J (z + RowAt.Uvec frame) = J z + 0 := fun z => by rw [hJU z, add_zero]
  have h2 := PairTranslate.drift_zsmul P (RowAt.Vvec frame) 0 hPV0 n (x + m • RowAt.Uvec frame)
  have h3 := PairTranslate.drift_zsmul J (RowAt.Uvec frame) 0 hJU0 m x
  have h4 := PairTranslate.drift_zsmul J (RowAt.Vvec frame) (-1) hJV n (x + m • RowAt.Uvec frame)
  have hP := hg.1
  have hJ := hg.2
  rw [h2, h1, hx.1] at hP
  rw [h4, h3, hx.2] at hJ
  constructor
  · linarith
  · linarith

end FLatticePaper.RowPair
