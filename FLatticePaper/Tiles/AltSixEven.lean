import FLatticePaper.Tiles.AltParentConstants
import FLatticePaper.Tiles.ClosedPathAlt
import Mathlib.Tactic.IntervalCases

/-! # The constants of the six standard copies of the even alternate child

Condition (C) for the six standard subtiles of the even alternate child `T̂(q_0)` with **explicit** constants
(`ClosedPathAlt` gives their existence). Normalised registers (`o = o_{1/1}` at slope zero on the first tile, with constants
`β_P`, `β_Q`), the constants are `κ_i = K_i - β`, where `K` is `0` on `Q^{+,1}` and `P^+`, `c_3 = F(B) - a^T B - a^T U` on `Q^{-,1}`
(`eq:alt_c3`), and the doubled partners and `P^-` follow (`h_0 = -F`):

* a mixed pair is read at a corner point of both copies (`ClosedPathContacts`), with the corner values `eq:std_corner_values`
  of the registers (`AltParentConstants.corner_raw`);
* a doubled pair has the shift constant `k` of the doubled register on its overlap, and `2 k = b^T S + a^T S - a^T D_q` by the
  half-turn of the doubled tile (`AltParentConstants.tau_shift`);
* the pairs `(Q^{+,i}, P^∓)`, `(Q^{-,i}, P^∓)` that never meet are `ClosedPathAlt.altExclEven_ef`.

These constants are the ones the closed paths through the alternate parent piece need (Case 3 of
`lemma:tile-odometer-existence`). -/

namespace FLatticePaper.Tiles.AltSixEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathContacts FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.ClosedPathAltSum
open FLatticePaper.Tiles.AltParentConstants
open FLatticePaper.Tiles.JointFamily (h0)

/-- **Agreement of six pieces** `f` (constants included): on the marks of two copies of different parents and on the overlap
of the two copies of each doubled pair. `ClosedPathGen` is its existential form. -/
def SixAgree (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop) (f : ℕ → ℤ × ℤ → ℤ) : Prop :=
  (∀ i j, i < P.length + Q.length → j < P.length + Q.length → pieceFlag P i ≠ pieceFlag P j →
      ∀ z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q M1 M2 j → f i z = f j z) ∧
    (∀ i j, i < P.length + Q.length → j < P.length + Q.length → i < j → pieceFlag P i = pieceFlag P j → Dbl i j →
      ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j → f i z = f j z)

theorem placedAltEven_add (w : Word) (oP oQ : ℤ × ℤ → ℤ) (κ : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) :
    placedAltEven w oP oQ 0 i z + κ i = placedAltEven w oP oQ κ i z := by
  unfold placedAltEven
  split_ifs <;> simp

theorem h0_even (x : ℤ × ℤ) (hx : (x.1 + x.2) % 2 = 0) : 4 * h0 x = -x.1 ^ 2 - 2 * x.1 * x.2 + x.2 ^ 2 + 2 * x.2 := by
  have h := zoH0_four x
  have e : h0 x = zoH0 x := rfl
  rw [e, h, hx, add_zero]

/-- The explicit constants of the six copies of the even alternate child, `W_1` even. -/
def kEvenEF (np dp nq dq hB hV βP βQ : ℤ) : ℕ → ℤ
  | 0 => -βQ
  | 1 => -hB + (dp ^ 2 + 2 * dp * np - np ^ 2) - βQ
  | 2 => -hB + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) - βQ
  | 3 => (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) - βQ
  | 4 => -βP
  | 5 => -hB - hV + (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq -
      nq ^ 2) - βP
  | _ => 0

theorem eval_lt (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z off α r : ℤ × ℤ) (hi : i < 4)
    (hoff : (altEvenD w).getD i 0 = off) (haff : (altEvenAff w).getD i 0 = α) (hr : z - off = r) :
    placedAltEven w oP oQ c i z = oQ r + dot2 α z + c i := by
  simp only [placedAltEven, if_pos hi, hoff, haff, hr]

theorem eval_ge (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z off α r : ℤ × ℤ) (hi : ¬ i < 4)
    (hoff : (altEvenR w).getD (i - 4) 0 = off) (haff : (altEvenAff w).getD i 0 = α) (hr : z - off = r) :
    placedAltEven w oP oQ c i z = oP r + dot2 α z + c i := by
  simp only [placedAltEven, if_neg hi, hoff, haff, hr]

/-- **Six pieces agree** from the agreements at the four mixed contacts, the four pairs that never meet and the two
doubled pairs. -/
theorem sixAgree_of (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (f : ℕ → ℤ × ℤ → ℤ) (hP : P.length = 4)
    (hQ : Q.length = 2) (hM1 : M1 ⊆ T1) (hM2 : M2 ⊆ T2)
    (m04 : ∀ z, z ∈ pieceSet P Q M1 M2 0 → z ∈ pieceSet P Q M1 M2 4 → f 0 z = f 4 z)
    (m24 : ∀ z, z ∈ pieceSet P Q M1 M2 2 → z ∈ pieceSet P Q M1 M2 4 → f 2 z = f 4 z)
    (m15 : ∀ z, z ∈ pieceSet P Q M1 M2 1 → z ∈ pieceSet P Q M1 M2 5 → f 1 z = f 5 z)
    (m35 : ∀ z, z ∈ pieceSet P Q M1 M2 3 → z ∈ pieceSet P Q M1 M2 5 → f 3 z = f 5 z)
    (x05 : ∀ z, z ∈ pieceSet P Q T1 T2 0 → z ∈ pieceSet P Q T1 T2 5 → False)
    (x14 : ∀ z, z ∈ pieceSet P Q T1 T2 1 → z ∈ pieceSet P Q T1 T2 4 → False)
    (x25 : ∀ z, z ∈ pieceSet P Q T1 T2 2 → z ∈ pieceSet P Q T1 T2 5 → False)
    (x34 : ∀ z, z ∈ pieceSet P Q T1 T2 3 → z ∈ pieceSet P Q T1 T2 4 → False)
    (d01 : ∀ z, z ∈ pieceSet P Q T1 T2 0 → z ∈ pieceSet P Q T1 T2 1 → f 0 z = f 1 z)
    (d23 : ∀ z, z ∈ pieceSet P Q T1 T2 2 → z ∈ pieceSet P Q T1 T2 3 → f 2 z = f 3 z) :
    SixAgree P Q T1 T2 M1 M2 dblEven f := by
  have hsub : ∀ i z, z ∈ pieceSet P Q M1 M2 i → z ∈ pieceSet P Q T1 T2 i := by
    intro i z hz
    simp only [pieceSet] at hz ⊢
    split_ifs at hz ⊢
    · obtain ⟨r, hr, rfl⟩ := hz
      exact ⟨r, hM1 hr, rfl⟩
    · obtain ⟨r, hr, rfl⟩ := hz
      exact ⟨r, hM2 hr, rfl⟩
  have hfl : ∀ i, pieceFlag P i = decide (4 ≤ i) := fun i => by simp only [pieceFlag, hP]
  refine ⟨?_, ?_⟩
  · intro i j hi hj hf z hzi hzj
    rw [hP, hQ] at hi hj
    rw [hfl, hfl] at hf
    interval_cases i <;> interval_cases j <;> simp only [Nat.reduceLeDiff, decide_true, decide_false, ne_eq,
      not_true_eq_false] at hf
    all_goals first
      | exact m04 z hzi hzj | exact (m04 z hzj hzi).symm
      | exact m24 z hzi hzj | exact (m24 z hzj hzi).symm
      | exact m15 z hzi hzj | exact (m15 z hzj hzi).symm
      | exact m35 z hzi hzj | exact (m35 z hzj hzi).symm
      | exact (x05 z (hsub _ z hzi) (hsub _ z hzj)).elim | exact (x05 z (hsub _ z hzj) (hsub _ z hzi)).elim
      | exact (x14 z (hsub _ z hzi) (hsub _ z hzj)).elim | exact (x14 z (hsub _ z hzj) (hsub _ z hzi)).elim
      | exact (x25 z (hsub _ z hzi) (hsub _ z hzj)).elim | exact (x25 z (hsub _ z hzj) (hsub _ z hzi)).elim
      | exact (x34 z (hsub _ z hzi) (hsub _ z hzj)).elim | exact (x34 z (hsub _ z hzj) (hsub _ z hzi)).elim
  · intro i j _ _ _ _ hdbl z hzi hzj
    obtain ⟨rfl, h | h⟩ := hdbl
    · subst h
      exact d01 z hzi hzj
    · subst h
      exact d23 z hzi hzj

/-- The mixed pairs of the even alternate child, `W_1` even, at their corner contacts. -/
theorem sixEven_ef_mixed (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hhQ : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * (oQ.val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den)
          (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ.val (x + shiftQ w) - oQ.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP.val oQ.val 0)) :
    (∀ z, z ∈ mAE w u1 u2 0 → z ∈ mAE w u1 u2 4 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 0 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 4 z) ∧
      (∀ z, z ∈ mAE w u1 u2 2 → z ∈ mAE w u1 u2 4 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 2 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 4 z) ∧
      (∀ z, z ∈ mAE w u1 u2 1 → z ∈ mAE w u1 u2 5 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 1 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 5 z) ∧
      (∀ z, z ∈ mAE w u1 u2 3 → z ∈ mAE w u1 u2 5 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 3 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 5 z) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨cP0, cP1, -, -, -, -, cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨-, -, cQU', cQU, cQV1, cQV1', -, -⟩ := corner_marks_even u2
  rw [← hp] at cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1'
  obtain ⟨vP0, vP1, -, -, -, -, vPD, vPD'⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, -, vQU', vQU, vQV1, vQV1', -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  have hB4 := h0_even (texV2 p) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 q) (by simp only [texV2]; omega)
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  set κ := kEvenEF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltEven w oP.val oQ.val κ i z = placedAltEven w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltEven_add w _ _ κ i z).symm
  have hm0 : mAE w u1 u2 0 = shiftS (marksEven u2) 0 := by simp [mAE, pieceSet, hD]
  have hm1 : mAE w u1 u2 1 = shiftS (marksEven u2) (S + 0) := by simp [mAE, pieceSet, hD]
  have hm2 : mAE w u1 u2 2 = shiftS (marksEven u2) (A + B) := by simp [mAE, pieceSet, hD]
  have hm3 : mAE w u1 u2 3 = shiftS (marksEven u2) (S + (A + B)) := by simp [mAE, pieceSet, hD]
  have hm4 : mAE w u1 u2 4 = shiftS (marksOdd u1) U := by simp [mAE, pieceSet, hD, hR]
  have hm5 : mAE w u1 u2 5 = shiftS (marksOdd u1) (B - U + V) := by simp [mAE, pieceSet, hD, hR]
  -- the four mixed contacts
  have m04 : ∀ z, z ∈ mAE w u1 u2 0 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val κ 0 z = placedAltEven w oP.val oQ.val κ 4 z := by
    obtain ⟨C, hC⟩ := hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC U (by rw [hm0]; exact mem_shift _ _ _ U cQU (by abel)) (by rw [hm4]; exact mem_shift _ _ _ 0 cP0 (by abel))
    rw [eval_lt w _ _ 0 0 U 0 0 U (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 4 U U 0 0 (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQU, vP0] at h1
    intro z hz0 hz4
    have h2 := hC z hz0 hz4
    rw [hff, hff]
    simp only [hκ, kEvenEF, dot2, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 ⊢
    linear_combination h2 - h1
  have m24 : ∀ z, z ∈ mAE w u1 u2 2 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val κ 2 z = placedAltEven w oP.val oQ.val κ 4 z := by
    obtain ⟨C, hC⟩ := hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (A + B + (U - e₂)) (by rw [hm2]; exact mem_shift _ _ _ (U - e₂) cQU' (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (A + B - e₂) cPD' (by abel))
    have ev : A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) = A + B - e₂ := by ext <;> simp; ring
    rw [ev] at vPD'
    rw [eval_lt w _ _ 0 2 _ (A + B) (p.num, -p.den) (U - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 4 _ U 0 (A + B - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQU',
      vPD'] at h1
    intro z hz2 hz4
    have h2 := hC z hz2 hz4
    rw [hff, hff]
    simp only [hκ, kEvenEF, dot2, hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 ⊢
    linear_combination h2 - h1
  have m15 : ∀ z, z ∈ mAE w u1 u2 1 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val κ 1 z = placedAltEven w oP.val oQ.val κ 5 z := by
    obtain ⟨C, hC⟩ := hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (B - U + V + e₁) (by rw [hm1]; exact mem_shift _ _ _ (V + e₁) cQV1 (by rw [hSh]; abel))
      (by rw [hm5]; exact mem_shift _ _ _ e₁ cP1 (by abel))
    rw [eval_lt w _ _ 0 1 _ (S + 0) (p.num, -p.den) (V + e₁) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel),
      eval_ge w _ _ 0 5 _ (B - U + V) ((p.num, -p.den) + (q.num, -q.den)) e₁ (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQV1,
      vP1] at h1
    intro z hz1 hz5
    have h2 := hC z hz1 hz5
    rw [hff, hff]
    simp only [hκ, kEvenEF, dot2, hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 ⊢
    linear_combination h2 - h1
  have m35 : ∀ z, z ∈ mAE w u1 u2 3 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val κ 3 z = placedAltEven w oP.val oQ.val κ 5 z := by
    obtain ⟨C, hC⟩ := hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (B - U + V + (A + B + e₁ - e₂))
      (by rw [hm3]; exact mem_shift _ _ _ (V + e₁ - e₂) cQV1' (by rw [hSh]; abel))
      (by rw [hm5]; exact mem_shift _ _ _ (A + B + e₁ - e₂) cPD (by abel))
    have ev1 : V + ((1 : ℤ), (-1 : ℤ)) = V + e₁ - e₂ := by ext <;> simp; ring
    have ev2 : A + B + ((1 : ℤ), (-1 : ℤ)) = A + B + e₁ - e₂ := by ext <;> simp; ring
    rw [ev1] at vQV1'
    rw [ev2] at vPD
    rw [eval_lt w _ _ 0 3 _ (S + (A + B)) ((p.num, -p.den) + (p.num, -p.den)) (V + e₁ - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl)
        (by rw [hSh]; abel),
      eval_ge w _ _ 0 5 _ (B - U + V) ((p.num, -p.den) + (q.num, -q.den)) (A + B + e₁ - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel),
      vQV1', vPD] at h1
    intro z hz3 hz5
    have h2 := hC z hz3 hz5
    rw [hff, hff]
    simp only [hκ, kEvenEF, dot2, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 hB4 ⊢
    linarith
  exact ⟨m04, m24, m15, m35⟩

/-- The doubled pairs of the even alternate child, `W_1` even, by the half-turn of the doubled tiles. -/
theorem sixEven_ef_dbl (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhQ : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * (oQ.val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den)
          (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ.val (x + shiftQ w) - oQ.val x - dot2 (affS w) x = k)
    (_hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP.val oQ.val 0)) :
    (∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 1 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 0 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 1 z) ∧
      (∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 3 → (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 2 z = (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) 3 z) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_ef w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨cP0, cP1, -, -, -, -, cPD, cPD'⟩ := corner_marks_odd u1
  obtain ⟨-, -, cQU', cQU, cQV1, cQV1', -, -⟩ := corner_marks_even u2
  rw [← hp] at cPD cPD'
  rw [← hq] at cQU' cQU cQV1 cQV1'
  obtain ⟨vP0, vP1, -, -, -, -, vPD, vPD'⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, -, vQU', vQU, vQV1, vQV1', -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  have hB4 := h0_even (texV2 p) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 q) (by simp only [texV2]; omega)
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  set κ := kEvenEF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltEven w oP.val oQ.val κ i z = placedAltEven w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltEven_add w _ _ κ i z).symm
  have hm0 : mAE w u1 u2 0 = shiftS (marksEven u2) 0 := by simp [mAE, pieceSet, hD]
  have hm1 : mAE w u1 u2 1 = shiftS (marksEven u2) (S + 0) := by simp [mAE, pieceSet, hD]
  have hm2 : mAE w u1 u2 2 = shiftS (marksEven u2) (A + B) := by simp [mAE, pieceSet, hD]
  have hm3 : mAE w u1 u2 3 = shiftS (marksEven u2) (S + (A + B)) := by simp [mAE, pieceSet, hD]
  have hm4 : mAE w u1 u2 4 = shiftS (marksOdd u1) U := by simp [mAE, pieceSet, hD, hR]
  have hm5 : mAE w u1 u2 5 = shiftS (marksOdd u1) (B - U + V) := by simp [mAE, pieceSet, hD, hR]
  -- the doubled pairs
  have hd0 : dAE w u1 u2 0 = shiftS (tEvenSet u2) 0 := by simp [dAE, pieceSet, hD]
  have hd1 : dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + 0) := by simp [dAE, pieceSet, hD]
  have hd2 : dAE w u1 u2 2 = shiftS (tEvenSet u2) (A + B) := by simp [dAE, pieceSet, hD]
  have hd3 : dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + (A + B)) := by simp [dAE, pieceSet, hD]
  have hkS : ∀ x, x ∈ tEvenSet u2 → x + S ∈ tEvenSet u2 → oQ.val (x + S) - oQ.val x - dotS (affS w) x = k :=
    fun x h1 h2 => by have := hk x h1 h2; simpa [dot2, dotS] using this
  have tau : ∀ y, y ∈ tEvenSet u2 → y + S ∈ tEvenSet u2 →
      2 * k = dotS (q.num, -q.den) S + dotS (affS w) S - dotS (affS w) (U + V + ((1 : ℤ), (-1 : ℤ))) :=
    fun y h1 h2 => tau_shift oQ.val (tEvenSet u2) _ _ S (affS w) hhQ k hkS y h1 h2
  have d01 : ∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 1 → placedAltEven w oP.val oQ.val κ 0 z = placedAltEven w oP.val oQ.val κ 1 z := by
    intro z hz0 hz1
    rw [hd0] at hz0
    rw [hd1] at hz1
    have y0 := sub_mem_of_shift _ _ _ hz0
    have y1 := sub_mem_of_shift _ _ _ hz1
    have ey : z - (S + 0) + S = z - 0 := by abel
    have ht := tau (z - (S + 0)) y1 (by rw [ey]; exact y0)
    have hz := hkS (z - (S + 0)) y1 (by rw [ey]; exact y0)
    rw [ey] at hz
    rw [hff, hff, eval_lt w _ _ 0 0 z 0 0 (z - 0) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      eval_lt w _ _ 0 1 z (S + 0) (p.num, -p.den) (z - (S + 0)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kEvenEF, dot2, dotS, affS, offsetA, hSh, hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at ht hz hB4 ⊢
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.zero_apply, zero_mul, add_zero] at ht hz ⊢
    linarith
  have d23 : ∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 3 → placedAltEven w oP.val oQ.val κ 2 z = placedAltEven w oP.val oQ.val κ 3 z := by
    intro z hz2 hz3
    rw [hd2] at hz2
    rw [hd3] at hz3
    have y2 := sub_mem_of_shift _ _ _ hz2
    have y3 := sub_mem_of_shift _ _ _ hz3
    have ey : z - (S + (A + B)) + S = z - (A + B) := by abel
    have ht := tau (z - (S + (A + B))) y3 (by rw [ey]; exact y2)
    have hz := hkS (z - (S + (A + B))) y3 (by rw [ey]; exact y2)
    rw [ey] at hz
    rw [hff, hff, eval_lt w _ _ 0 2 z (A + B) (p.num, -p.den) (z - (A + B)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      eval_lt w _ _ 0 3 z (S + (A + B)) ((p.num, -p.den) + (p.num, -p.den)) (z - (S + (A + B))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kEvenEF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at ht hz hB4 ⊢
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.zero_apply, add_zero] at ht hz ⊢
    linarith
  exact ⟨d01, d23⟩

/-- **The six copies of the even alternate child, `W_1` even, agree with the explicit constants `kEvenEF`.** -/
theorem sixEven_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhQ : ∀ y ∈ tEvenSet u2,
      texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y ∈ tEvenSet u2 ∧
      2 * (oQ.val (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) =
        dotS ((parentsAt w).even.num, -(parentsAt w).even.den)
          (texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).even.num, -(parentsAt w).even.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tEvenSet u2 → x + shiftQ w ∈ tEvenSet u2 →
      oQ.val (x + shiftQ w) - oQ.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatEven w u1 u2 (placedAltEven w oP.val oQ.val 0)) :
    SixAgree (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) (marksEven u2) (marksOdd u1) dblEven
      (placedAltEven w oP.val oQ.val (kEvenEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, -, -⟩ := altEven_ef w hph
  obtain ⟨m04, m24, m15, m35⟩ := sixEven_ef_mixed w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhQ hk hcompat
  obtain ⟨d01, d23⟩ := sixEven_ef_dbl w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhQ hk hcompat
  exact sixAgree_of _ _ _ _ _ _ _ (by simp [hD]) (by simp [hR]) (MarksIn.marksEven_sub u2) (MarksIn.marksOdd_sub u1)
    m04 m24 m15 m35 x05 x14 x25 x34 d01 d23

end FLatticePaper.Tiles.AltSixEven
