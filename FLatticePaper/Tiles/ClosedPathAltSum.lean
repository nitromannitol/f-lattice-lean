import FLatticePaper.Tiles.ClosedPathDiagonal
import FLatticePaper.Tiles.SurgicalAltOdometers

/-! # Condition (C) for the alternate decompositions: the closed path of the six standard subtiles

The alternate children (`eq:alt_odometer_decomposition`) contain six standard subtiles: the two copies of each of the two
shifted doublings `ds(o)^±` of one parent (shift `S` of `eq:alt_doubled`, `altShifts`) and two plain copies of the other parent.
Step 1 of `lemma:weak_alternate_odometer_properties` chooses constants for them; this module contains the parts of that step that
do not depend on the tiles.

* `ClosedPathGen`: condition (C) for copies given by two lists of offsets, with the same content as `ChildGlue.ClosedPathOdd`
  and `ClosedPathEven` (`closedPathOdd_iff`, `closedPathEven_iff`): constants `κ` such that the placed subodometers agree on the
  marks of copies of different parents and on the whole overlap of the two copies of each doubled piece.
* `hex_closed`: copies `0, 1` and `2, 3` the two doubled pairs, `4, 5` the plain copies; if the pairs `(0, 5)`, `(1, 4)`, `(2, 5)`,
  `(3, 4)` never meet, the mixed pairs have constant differences on their marks, the doubled pairs constant differences `C01`,
  `C23` on their overlaps, and the offsets read at one common point of each of `(1, 5)`, `(0, 4)`, `(2, 4)`, `(3, 5)` sum to zero
  with `C23 - C01` around the closed path `5, 1, 0, 4, 2, 3`, then (C) holds.
* `dbl_const`: the second copy of a shifted doubling is the translate of the first by `S` with the affine factor `a_{p,2}`; if the
  parent is compatible along `S` (`o(x + S) - o(x) - a_{p,2}^T x = k` where both points lie in the tile), the difference of the
  two copies on their overlap is `k - a_{p,2}^T (S + c)`, `c` the offset of the first copy.
* `altEven_even_first`, `altEven_odd_first`, `altOdd_even_first`, `altOdd_odd_first`: the text's four cases (even `q_0` and odd
  `p_0`, `W_1` even and odd), each with its shift `S`. The four mixed interfaces of the closed path are translates of the four
  mandatory interfaces of the standard children, and the offsets are read at the same corner points (`ClosedPathSum`). The sum is
  zero by the two corner differences of the parents (`CornerDiffs`); the constant `k` of the doubling enters the two doubled edges
  with opposite signs, so no point of the overlaps of the doubled copies is needed (they are empty in Type 2 for the even child and
  Type 3 for the odd child).

The text proves the same sum by moving the three shifted copies by `-S` onto a pseudo-square and applying
`eq:boundary_path_difference`; here the sum is read at one point of each interface, as in the standard case
(`ClosedPathSum`, `notes/C/C_other_proof_all_cases.md`). -/

namespace FLatticePaper.Tiles.ClosedPathAltSum

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathSum

/-! ### Condition (C) for copies given by lists -/

/-- **Condition (C) for the copies of two lists of offsets**: `P` lists the copies of `T1` (marks `M1`), `Q` those of `T2`
(marks `M2`), and `Dbl` the doubled pairs. There are constants `κ` such that the subodometers `f0 i + κ i` agree on the marks of
every two copies of different parents and on the whole overlap of the two copies of each doubled pair. -/
def ClosedPathGen (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop) (f0 : ℕ → ℤ × ℤ → ℤ) :
    Prop :=
  ∃ κ : ℕ → ℤ,
    (∀ i j, i < P.length + Q.length → j < P.length + Q.length → pieceFlag P i ≠ pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j → f0 i z + κ i = f0 j z + κ j) ∧
    (∀ i j, i < P.length + Q.length → j < P.length + Q.length → i < j → pieceFlag P i = pieceFlag P j → Dbl i j →
      ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j → f0 i z + κ i = f0 j z + κ j)

/-- `ChildGlue.ClosedPathOdd` is `ClosedPathGen` for the copies of the odd standard child. -/
theorem closedPathOdd_iff (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) :
    ClosedPathOdd w u1 u2 f0 ↔
      ClosedPathGen (oddP w) (oddQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) (dblOdd w) f0 :=
  Iff.rfl

/-- `ChildGlue.ClosedPathEven` is `ClosedPathGen` for the copies of the even standard child. -/
theorem closedPathEven_iff (w u1 u2 : Word) (f0 : ℕ → ℤ × ℤ → ℤ) :
    ClosedPathEven w u1 u2 f0 ↔
      ClosedPathGen (evenP w) (evenQ w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven f0 :=
  Iff.rfl

/-! ### The closed path of six copies with two doubled pairs -/

/-- **Condition (C) from the closed path `5, 1, 0, 4, 2, 3`.** The copies `0, 1, 2, 3` of `T1` form the doubled pairs `(0, 1)`
and `(2, 3)`, the copies `4, 5` of `T2` are plain. The pairs `(0, 5)`, `(1, 4)`, `(2, 5)`, `(3, 4)` never meet; the other mixed
pairs have a constant difference on their marks and a common point `y`; the doubled pairs have the constant differences `C01`,
`C23` on their overlaps. If the offsets around the closed path sum to zero, (C) holds. -/
theorem hex_closed (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (f : ℕ → ℤ × ℤ → ℤ)
    (hP : P.length = 4) (hQ : Q.length = 2) (hM1 : M1 ⊆ T1) (hM2 : M2 ⊆ T2) (C01 C23 : ℤ)
    (h01 : ∀ z, z ∈ pieceSet P Q T1 T2 0 → z ∈ pieceSet P Q T1 T2 1 → f 0 z - f 1 z = C01)
    (h23 : ∀ z, z ∈ pieceSet P Q T1 T2 2 → z ∈ pieceSet P Q T1 T2 3 → f 2 z - f 3 z = C23)
    (hc : ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∃ C : ℤ, ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j →
      f i z - f j z = C)
    (y15 y04 y24 y35 : ℤ × ℤ)
    (m15 : y15 ∈ pieceSet P Q M1 M2 1 ∧ y15 ∈ pieceSet P Q M1 M2 5)
    (m04 : y04 ∈ pieceSet P Q M1 M2 0 ∧ y04 ∈ pieceSet P Q M1 M2 4)
    (m24 : y24 ∈ pieceSet P Q M1 M2 2 ∧ y24 ∈ pieceSet P Q M1 M2 4)
    (m35 : y35 ∈ pieceSet P Q M1 M2 3 ∧ y35 ∈ pieceSet P Q M1 M2 5)
    (x05 : ∀ z, z ∈ pieceSet P Q T1 T2 0 → z ∈ pieceSet P Q T1 T2 5 → False)
    (x14 : ∀ z, z ∈ pieceSet P Q T1 T2 1 → z ∈ pieceSet P Q T1 T2 4 → False)
    (x25 : ∀ z, z ∈ pieceSet P Q T1 T2 2 → z ∈ pieceSet P Q T1 T2 5 → False)
    (x34 : ∀ z, z ∈ pieceSet P Q T1 T2 3 → z ∈ pieceSet P Q T1 T2 4 → False)
    (hsum : (f 5 y15 - f 1 y15) - C01 + (f 0 y04 - f 4 y04) + (f 4 y24 - f 2 y24) + C23 +
      (f 3 y35 - f 5 y35) = 0) :
    ClosedPathGen P Q T1 T2 M1 M2 dblEven f := by
  have hMT : ∀ i z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q T1 T2 i := by
    intro i z hz
    unfold pieceSet at hz ⊢
    by_cases h : i < P.length
    · rw [if_pos h] at hz ⊢
      exact shift_mono _ _ hM1 _ hz
    · rw [if_neg h] at hz ⊢
      exact shift_mono _ _ hM2 _ hz
  obtain ⟨κ, k5, k1, k0, k4, k2, k3⟩ : ∃ κ : ℕ → ℤ, κ 5 = 0 ∧ κ 1 = f 5 y15 - f 1 y15 ∧ κ 0 = κ 1 - C01 ∧
      κ 4 = κ 0 + (f 0 y04 - f 4 y04) ∧ κ 2 = κ 4 + (f 4 y24 - f 2 y24) ∧ κ 3 = κ 2 + C23 := by
    refine ⟨fun i => if i = 1 then f 5 y15 - f 1 y15 else if i = 0 then f 5 y15 - f 1 y15 - C01 else
      if i = 4 then f 5 y15 - f 1 y15 - C01 + (f 0 y04 - f 4 y04) else
      if i = 2 then f 5 y15 - f 1 y15 - C01 + (f 0 y04 - f 4 y04) + (f 4 y24 - f 2 y24) else
      if i = 3 then f 5 y15 - f 1 y15 - C01 + (f 0 y04 - f 4 y04) + (f 4 y24 - f 2 y24) + C23 else 0,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  have a04 : f 0 y04 + κ 0 = f 4 y04 + κ 4 := by rw [k4]; ring
  have a15 : f 1 y15 + κ 1 = f 5 y15 + κ 5 := by rw [k1, k5]; ring
  have a24 : f 2 y24 + κ 2 = f 4 y24 + κ 4 := by rw [k2]; ring
  have a35 : f 3 y35 + κ 3 = f 5 y35 + κ 5 := by rw [k5, k3, k2, k4, k0, k1]; linarith
  have hmix : ∀ i j, i < 4 → 4 ≤ j → j < 6 → ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j →
      f i z + κ i = f j z + κ j := by
    intro i j hi hj hj6 z hzi hzj
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals obtain rfl | rfl : j = 4 ∨ j = 5 := by omega
    · exact pair_agree _ f κ 0 4 (hc 0 4 (by norm_num) (by norm_num) (by norm_num)) y04 m04.1 m04.2 a04 z hzi hzj
    · exact (x05 z (hMT 0 z hzi) (hMT 5 z hzj)).elim
    · exact (x14 z (hMT 1 z hzi) (hMT 4 z hzj)).elim
    · exact pair_agree _ f κ 1 5 (hc 1 5 (by norm_num) (by norm_num) (by norm_num)) y15 m15.1 m15.2 a15 z hzi hzj
    · exact pair_agree _ f κ 2 4 (hc 2 4 (by norm_num) (by norm_num) (by norm_num)) y24 m24.1 m24.2 a24 z hzi hzj
    · exact (x25 z (hMT 2 z hzi) (hMT 5 z hzj)).elim
    · exact (x34 z (hMT 3 z hzi) (hMT 4 z hzj)).elim
    · exact pair_agree _ f κ 3 5 (hc 3 5 (by norm_num) (by norm_num) (by norm_num)) y35 m35.1 m35.2 a35 z hzi hzj
  refine ⟨κ, ?_, ?_⟩
  · intro i j hi hj hfl z hzi hzj
    rw [hP, hQ] at hi hj
    simp only [pieceFlag, hP, ne_eq, decide_eq_decide] at hfl
    by_cases hi4 : i < 4
    · exact hmix i j hi4 (by omega) hj z hzi hzj
    · exact (hmix j i (by omega) (by omega) hi z hzj hzi).symm
  · intro i j _ _ _ _ hd z hzi hzj
    obtain ⟨rfl, hi⟩ := hd
    rcases hi with rfl | rfl
    · have := h01 z hzi hzj
      linarith
    · have := h23 z hzi hzj
      linarith

/-- **The two copies of a shifted doubling.** The second copy is the translate of the first by `S` with the extra affine
factor `a`; if the parent satisfies `o(x + S) - o(x) - a^T x = k` wherever both points lie in its tile `T`, the two copies differ
by `k - a^T (S + c)` on their overlap. -/
theorem dbl_const (o : ℤ × ℤ → ℤ) (T : Set (ℤ × ℤ)) (S a α α1 c : ℤ × ℤ) (c0 c1 k : ℤ) (f0 f1 : ℤ × ℤ → ℤ)
    (hk : ∀ x, x ∈ T → x + S ∈ T → o (x + S) - o x - dot2 a x = k)
    (h0 : IsPiece f0 o c α c0) (h1 : IsPiece f1 o (S + c) α1 c1) (hα : α1 = α + a) :
    ∀ z, z ∈ shiftS T c → z ∈ shiftS T (S + c) → f0 z - f1 z = k - dot2 a (S + c) + c0 - c1 := by
  intro z hz0 hz1
  subst hα
  have e : z - (S + c) + S = z - c := by abel
  have := hk (z - (S + c)) (sub_mem_of_shift _ _ _ hz1) (by rw [e]; exact sub_mem_of_shift _ _ _ hz0)
  rw [h0 z, h1 z, ← e, dot2_add_left]
  rw [e] at this ⊢
  rw [dot2_sub_right] at this
  linarith

/-! ### The four cycle sums (the text's four cases) -/

/-- **Even child `\hat T(q_0)`, `W_1` even**, `S = B - U`: `Q^{+,1}, Q^{+,2}` at `0, S`, `Q^{-,1}, Q^{-,2}` at `A + B`,
`S + A + B` (affine factors `0, a, a, 2a`), `P^+, P^-` at `U`, `B - U + V` (affine factors `0, a + b`). The interfaces are read at
`B - U + V + 1`, `U`, `U + A + B - i`, `B - U + V + A + B + 1 - i`. -/
theorem altEven_even_first (np dp nq dq : ℤ) (A B U V a b S : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (hS : S = -U + B) (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ) (k : ℤ)
    (h0 : IsPiece (f 0) oQ 0 0 (c 0)) (h1 : IsPiece (f 1) oQ (S + 0) a (c 1))
    (h2 : IsPiece (f 2) oQ (A + B) a (c 2)) (h3 : IsPiece (f 3) oQ (S + (A + B)) (a + a) (c 3))
    (h4 : IsPiece (f 4) oP U 0 (c 4)) (h5 : IsPiece (f 5) oP (B - U + V) (a + b) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 5 (B - U + V + e₁) - f 1 (B - U + V + e₁)) - (k - dot2 a (S + 0) + c 0 - c 1) + (f 0 U - f 4 U) +
      (f 4 (U + (A + B - e₂)) - f 2 (U + (A + B - e₂))) + (k - dot2 a (S + (A + B)) + c 2 - c 3) +
      (f 3 (B - U + V + (A + B + e₁ - e₂)) - f 5 (B - U + V + (A + B + e₁ - e₂))) = 0 := by
  subst hS
  rw [piece_val h5 (B - U + V + e₁) e₁ (by abel), piece_val h1 (B - U + V + e₁) (V + e₁) (by abel),
    piece_val h0 U U (by abel), piece_val h4 U 0 (by abel),
    piece_val h4 (U + (A + B - e₂)) (A + B - e₂) (by abel), piece_val h2 (U + (A + B - e₂)) (U - e₂) (by abel),
    piece_val h3 (B - U + V + (A + B + e₁ - e₂)) (V + e₁ - e₂) (by abel),
    piece_val h5 (B - U + V + (A + B + e₁ - e₂)) (A + B + e₁ - e₂) (by abel)]
  obtain ⟨hP1, -⟩ := hP
  obtain ⟨-, hQ2⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
    Prod.fst_zero, Prod.snd_zero] at hP1 hQ2 ⊢
  linear_combination (-1 : ℤ) * hP1 - hQ2

/-- **Even child, `W_1` odd**, `S = B + U`: `Q^{+,1}, Q^{+,2}` at `A, S + A`, `Q^{-,1}, Q^{-,2}` at `B, S + B`, `P^+, P^-` at
`0`, `B + 2U + V`. The interfaces are read at `B + 2U + V + A - i`, `A`, `B + 1`, `B + 2U + V + B + 1 - i`. -/
theorem altEven_odd_first (np dp nq dq : ℤ) (A B U V a b S : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (hS : S = U + B) (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ) (k : ℤ)
    (h0 : IsPiece (f 0) oQ A 0 (c 0)) (h1 : IsPiece (f 1) oQ (S + A) a (c 1))
    (h2 : IsPiece (f 2) oQ B a (c 2)) (h3 : IsPiece (f 3) oQ (S + B) (a + a) (c 3))
    (h4 : IsPiece (f 4) oP 0 0 (c 4)) (h5 : IsPiece (f 5) oP (B + U + U + V) (a + b) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 5 (B + U + U + V + (A - e₂)) - f 1 (B + U + U + V + (A - e₂))) - (k - dot2 a (S + A) + c 0 - c 1) +
      (f 0 A - f 4 A) + (f 4 (B + e₁) - f 2 (B + e₁)) + (k - dot2 a (S + B) + c 2 - c 3) +
      (f 3 (B + U + U + V + (B + e₁ - e₂)) - f 5 (B + U + U + V + (B + e₁ - e₂))) = 0 := by
  subst hS
  rw [piece_val h5 (B + U + U + V + (A - e₂)) (A - e₂) (by abel),
    piece_val h1 (B + U + U + V + (A - e₂)) (U + V - e₂) (by abel),
    piece_val h0 A 0 (by abel), piece_val h4 A A (by abel),
    piece_val h4 (B + e₁) (B + e₁) (by abel), piece_val h2 (B + e₁) e₁ (by abel),
    piece_val h3 (B + U + U + V + (B + e₁ - e₂)) (U + V + e₁ - e₂) (by abel),
    piece_val h5 (B + U + U + V + (B + e₁ - e₂)) (B + e₁ - e₂) (by abel)]
  obtain ⟨-, hP2⟩ := hP
  obtain ⟨hQ1, -⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero] at hP2 hQ1 ⊢
  linear_combination hP2 + hQ1

/-- **Odd child `\hat T(p_0)`, `W_1` even**, `S = B + U`: `P^{+,1}, P^{+,2}` at `U, S + U`, `P^{-,1}, P^{-,2}` at `V, S + V`
(affine factors `0, a, b, b + a`), `Q^+, Q^-` at `0`, `A + 2B + U` (affine factors `0, 2a`). The interfaces are read at
`S + U + A + B - i`, `U`, `V + 1`, `S + V + A + B + 1 - i`. -/
theorem altOdd_even_first (np dp nq dq : ℤ) (A B U V a b S : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (hS : S = U + B) (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ) (k : ℤ)
    (h0 : IsPiece (f 0) oP U 0 (c 0)) (h1 : IsPiece (f 1) oP (S + U) a (c 1))
    (h2 : IsPiece (f 2) oP V b (c 2)) (h3 : IsPiece (f 3) oP (S + V) (b + a) (c 3))
    (h4 : IsPiece (f 4) oQ 0 0 (c 4)) (h5 : IsPiece (f 5) oQ (A + B + B + U) (a + a) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 5 (S + U + (A + B - e₂)) - f 1 (S + U + (A + B - e₂))) - (k - dot2 a (S + U) + c 0 - c 1) +
      (f 0 U - f 4 U) + (f 4 (V + e₁) - f 2 (V + e₁)) + (k - dot2 a (S + V) + c 2 - c 3) +
      (f 3 (S + V + (A + B + e₁ - e₂)) - f 5 (S + V + (A + B + e₁ - e₂))) = 0 := by
  subst hS
  rw [piece_val h5 (U + B + U + (A + B - e₂)) (U - e₂) (by abel),
    piece_val h1 (U + B + U + (A + B - e₂)) (A + B - e₂) (by abel),
    piece_val h0 U 0 (by abel), piece_val h4 U U (by abel),
    piece_val h4 (V + e₁) (V + e₁) (by abel), piece_val h2 (V + e₁) e₁ (by abel),
    piece_val h3 (U + B + V + (A + B + e₁ - e₂)) (A + B + e₁ - e₂) (by abel),
    piece_val h5 (U + B + V + (A + B + e₁ - e₂)) (V + e₁ - e₂) (by abel)]
  obtain ⟨hP1, -⟩ := hP
  obtain ⟨-, hQ2⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero] at hP1 hQ2 ⊢
  linear_combination hP1 + hQ2

/-- **Odd child, `W_1` odd**, `S = B - U`: `P^{+,1}, P^{+,2}` at `0, S`, `P^{-,1}, P^{-,2}` at `U + V, S + U + V`, `Q^+, Q^-` at
`A`, `2B - U`. The interfaces are read at `S + B + 1`, `A`, `U + V + A - i`, `S + U + V + B + 1 - i`. -/
theorem altOdd_odd_first (np dp nq dq : ℤ) (A B U V a b S : ℤ × ℤ) (hv : StepVectors np dp nq dq A B U V a b)
    (hS : S = -U + B) (oP oQ : ℤ × ℤ → ℤ) (f : ℕ → ℤ × ℤ → ℤ) (c : ℕ → ℤ) (k : ℤ)
    (h0 : IsPiece (f 0) oP 0 0 (c 0)) (h1 : IsPiece (f 1) oP (S + 0) a (c 1))
    (h2 : IsPiece (f 2) oP (U + V) b (c 2)) (h3 : IsPiece (f 3) oP (S + (U + V)) (b + a) (c 3))
    (h4 : IsPiece (f 4) oQ A 0 (c 4)) (h5 : IsPiece (f 5) oQ (B + B - U) (a + a) (c 5))
    (hP : CornerDiffs oP A B np dp) (hQ : CornerDiffs oQ U V nq dq) :
    (f 5 (S + 0 + (B + e₁)) - f 1 (S + 0 + (B + e₁))) - (k - dot2 a (S + 0) + c 0 - c 1) +
      (f 0 A - f 4 A) + (f 4 (U + V + (A - e₂)) - f 2 (U + V + (A - e₂))) + (k - dot2 a (S + (U + V)) + c 2 - c 3) +
      (f 3 (S + (U + V) + (B + e₁ - e₂)) - f 5 (S + (U + V) + (B + e₁ - e₂))) = 0 := by
  subst hS
  rw [piece_val h5 (-U + B + 0 + (B + e₁)) e₁ (by abel), piece_val h1 (-U + B + 0 + (B + e₁)) (B + e₁) (by abel),
    piece_val h0 A A (by abel), piece_val h4 A 0 (by abel),
    piece_val h4 (U + V + (A - e₂)) (U + V - e₂) (by abel), piece_val h2 (U + V + (A - e₂)) (A - e₂) (by abel),
    piece_val h3 (-U + B + (U + V) + (B + e₁ - e₂)) (B + e₁ - e₂) (by abel),
    piece_val h5 (-U + B + (U + V) + (B + e₁ - e₂)) (U + V + e₁ - e₂) (by abel)]
  obtain ⟨-, hP2⟩ := hP
  obtain ⟨hQ1, -⟩ := hQ
  obtain ⟨hA, hB, hU, hV, ha, hb⟩ := hv
  subst hA hB hU hV ha hb
  simp only [dot2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
    Prod.fst_zero, Prod.snd_zero] at hP2 hQ1 ⊢
  linear_combination (-1 : ℤ) * hP2 - hQ1

end FLatticePaper.Tiles.ClosedPathAltSum
