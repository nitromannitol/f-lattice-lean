import FLatticePaper.Tiles.AltSixEven

/-! # The constants of the six standard copies of the odd alternate child

As `AltSixEven` for the even alternate child: the copies `P^{+,1}, P^{+,2}, P^{-,1}, P^{-,2}` of the doubled odd register (shift
`S_p`) and `Q^+, Q^-` of the even register of `tileAltOddPieces`, with explicit constants `κ_i = K_i - β` (`kOddEF`, `kOddOF`):
`0` on `P^{+,1}` and `Q^+`; the mixed pairs at corner contacts, the doubled pairs by the half-turn of the doubled tile, and the
pairs that never meet (`ClosedPathAlt.altExclOdd_ef`, `altExclOdd_of`). -/

namespace FLatticePaper.Tiles.AltSixOdd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathContacts FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.ClosedPathAltSum
open FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointFamily (h0)

theorem placedAltOdd_add (w : Word) (oP oQ : ℤ × ℤ → ℤ) (κ : ℕ → ℤ) (i : ℕ) (z : ℤ × ℤ) :
    placedAltOdd w oP oQ 0 i z + κ i = placedAltOdd w oP oQ κ i z := by
  unfold placedAltOdd
  split_ifs <;> simp

theorem evalO_lt (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z off α r : ℤ × ℤ) (hi : i < 4)
    (hoff : (altOddD w).getD i 0 = off) (haff : (altOddAff w).getD i 0 = α) (hr : z - off = r) :
    placedAltOdd w oP oQ c i z = oP r + dot2 α z + c i := by
  simp only [placedAltOdd, if_pos hi, hoff, haff, hr]

theorem evalO_ge (w : Word) (oP oQ : ℤ × ℤ → ℤ) (c : ℕ → ℤ) (i : ℕ) (z off α r : ℤ × ℤ) (hi : ¬ i < 4)
    (hoff : (altOddR w).getD (i - 4) 0 = off) (haff : (altOddAff w).getD i 0 = α) (hr : z - off = r) :
    placedAltOdd w oP oQ c i z = oQ r + dot2 α z + c i := by
  simp only [placedAltOdd, if_neg hi, hoff, haff, hr]

/-- The explicit constants of the six copies of the odd alternate child, `W_1` even. -/
def kOddEF (np dp nq dq hB hV βP βQ : ℤ) : ℕ → ℤ
  | 0 => -βP
  | 1 => -hB + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) - βP
  | 2 => -hV + (dq ^ 2 + 2 * dq * nq - nq ^ 2) - βP
  | 3 => -hB - hV + (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) - βP
  | 4 => -βQ
  | 5 => (2 * dp ^ 2 + 4 * dp * np + 3 * dp * nq - dp - 3 * dq * np - 2 * np ^ 2 - np) - βQ
  | _ => 0

/-- The explicit constants of the six copies of the odd alternate child, `W_1` odd. -/
def kOddOF (np dp nq dq hB hV βP βQ : ℤ) : ℕ → ℤ
  | 0 => -βP
  | 1 => -hB + (dp ^ 2 + 2 * dp * np - np ^ 2) - βP
  | 2 => -hV + (-2 * dp * nq + dq ^ 2 + 2 * dq * np + 2 * dq * nq - nq ^ 2) - βP
  | 3 => -hB - hV + (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) - βP
  | 4 => -βQ
  | 5 => (2 * dp ^ 2 + 4 * dp * np - dp * nq - dp + dq * np - 2 * np ^ 2 - np) - βQ
  | _ => 0

/-- The mixed pairs, odd alternate child, `W_1` even. -/
theorem sixOdd_ef_mixed (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (_hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    (∀ z, z ∈ mAO w u1 u2 0 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAO w u1 u2 2 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAO w u1 u2 1 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) ∧
      (∀ z, z ∈ mAO w u1 u2 3 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨cP0, cP1, cP2, cP3, cP4, cP5, cP6, cP7⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQ2, cQ3, cQ4, cQ5, cQ6, cQ7⟩ := corner_marks_even u2
  rw [← hp] at cP2 cP3 cP4 cP5 cP6 cP7
  rw [← hq] at cQ2 cQ3 cQ4 cQ5 cQ6 cQ7
  obtain ⟨vP0, vP1, vP2, vP3, vP4, vP5, vP6, vP7⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, vQ1, vQ2, vQ3, vQ4, vQ5, vQ6, vQ7⟩ := corner_raw oQ βQ _ _ _ hcQ
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
  set S := shiftP w with hSdef
  set κ := kOddEF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltOdd w oP.val oQ.val κ i z = placedAltOdd w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltOdd_add w _ _ κ i z).symm
  have hm0 : mAO w u1 u2 0 = shiftS (marksOdd u1) (U) := by simp [mAO, pieceSet, hD]
  have hm1 : mAO w u1 u2 1 = shiftS (marksOdd u1) (S + U) := by simp [mAO, pieceSet, hD]
  have hm2 : mAO w u1 u2 2 = shiftS (marksOdd u1) (V) := by simp [mAO, pieceSet, hD]
  have hm3 : mAO w u1 u2 3 = shiftS (marksOdd u1) (S + V) := by simp [mAO, pieceSet, hD]
  have hm4 : mAO w u1 u2 4 = shiftS (marksEven u2) (0) := by simp [mAO, pieceSet, hD, hR]
  have hm5 : mAO w u1 u2 5 = shiftS (marksEven u2) (A + B + B + U) := by simp [mAO, pieceSet, hD, hR]
  have m04 : ∀ z, z ∈ mAO w u1 u2 0 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (U + ((0 : ℤ × ℤ))) (by rw [hm0]; exact mem_shift _ _ _ ((0 : ℤ × ℤ)) cP0 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (U) cQ3 (by abel))
    rw [evalO_lt w _ _ 0 0 _ (U) 0 ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 4 _ (0) 0 (U) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP0, vQ3] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddEF, dot2, hBd, hU, hV, texV1Even, texV2,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m24 : ∀ z, z ∈ mAO w u1 u2 2 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (V + (e₁)) (by rw [hm2]; exact mem_shift _ _ _ (e₁) cP1 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (V + e₁) cQ4 (by abel))
    have evP1 : ((1 : ℤ), (0 : ℤ)) = e₁ := by ext <;> simp
    rw [evP1] at vP1
    have evQ4 : V + ((1 : ℤ), (0 : ℤ)) = V + e₁ := by ext <;> simp
    rw [evQ4] at vQ4
    rw [evalO_lt w _ _ 0 2 _ (V) (q.num, -q.den) (e₁) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 4 _ (0) 0 (V + e₁) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP1, vQ4] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddEF, dot2, hBd, hV, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m15 : ∀ z, z ∈ mAO w u1 u2 1 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + U + (A + B - e₂)) (by rw [hm1]; exact mem_shift _ _ _ (A + B - e₂) cP7 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (U - e₂) cQ2 (by rw [hSh]; abel))
    have evP7 : A + B + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) = A + B - e₂ := by ext <;> simp; ring
    rw [evP7] at vP7
    have evQ2 : U - ((0 : ℤ), (1 : ℤ)) = U - e₂ := by ext <;> simp
    rw [evQ2] at vQ2
    rw [evalO_lt w _ _ 0 1 _ (S + U) (p.num, -p.den) (A + B - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 5 _ (A + B + B + U) ((p.num, -p.den) + (p.num, -p.den)) (U - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vP7, vQ2] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddEF, dot2, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m35 : ∀ z, z ∈ mAO w u1 u2 3 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + V + (A + B + e₁ - e₂)) (by rw [hm3]; exact mem_shift _ _ _ (A + B + e₁ - e₂) cP6 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (V + e₁ - e₂) cQ5 (by rw [hSh]; abel))
    have evP6 : A + B + ((1 : ℤ), (-1 : ℤ)) = A + B + e₁ - e₂ := by ext <;> simp; ring
    rw [evP6] at vP6
    have evQ5 : V + ((1 : ℤ), (-1 : ℤ)) = V + e₁ - e₂ := by ext <;> simp; ring
    rw [evQ5] at vQ5
    rw [evalO_lt w _ _ 0 3 _ (S + V) ((q.num, -q.den) + (p.num, -p.den)) (A + B + e₁ - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 5 _ (A + B + B + U) ((p.num, -p.den) + (p.num, -p.den)) (V + e₁ - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vP6, vQ5] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddEF, dot2, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  exact ⟨m04, m24, m15, m35⟩

/-- The doubled pairs, odd alternate child, `W_1` even. -/
theorem sixOdd_ef_dbl (w u1 u2 : Word) (hph : phase w ≠ 1)
    (_hp : (parentsAt w).odd = fracOdd u1) (_hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (_hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    (∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 1 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z) ∧
      (∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 3 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨k, hk⟩ := hk
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
  set S := shiftP w with hSdef
  set κ := kOddEF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltOdd w oP.val oQ.val κ i z = placedAltOdd w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltOdd_add w _ _ κ i z).symm
  have hkS : ∀ x, x ∈ tOddSet u1 → x + S ∈ tOddSet u1 → oP.val (x + S) - oP.val x - dotS (affS w) x = k :=
    fun x h1 h2 => by have := hk x h1 h2; simpa [dot2, dotS] using this
  have tau : ∀ y, y ∈ tOddSet u1 → y + S ∈ tOddSet u1 →
      2 * k = dotS (p.num, -p.den) S + dotS (affS w) S - dotS (affS w) (A + B + ((1 : ℤ), (-1 : ℤ))) :=
    fun y h1 h2 => tau_shift oP.val (tOddSet u1) _ _ S (affS w) hhP k hkS y h1 h2
  have hd0 : dAO w u1 u2 0 = shiftS (tOddSet u1) (U) := by simp [dAO, pieceSet, hD]
  have hd1 : dAO w u1 u2 1 = shiftS (tOddSet u1) (S + U) := by simp [dAO, pieceSet, hD]
  have d01 : ∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 1 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
    intro z hzi hzj
    rw [hd0] at hzi
    rw [hd1] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + U) + S = z - (U) := by abel
    have ht := tau (z - (S + U)) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + U)) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, evalO_lt w _ _ 0 0 z (U) 0 (z - (U)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      evalO_lt w _ _ 0 1 z (S + U) (p.num, -p.den) (z - (S + U)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kOddEF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      zero_mul, add_zero] at ht hz hB4 ⊢
    linarith
  have hd2 : dAO w u1 u2 2 = shiftS (tOddSet u1) (V) := by simp [dAO, pieceSet, hD]
  have hd3 : dAO w u1 u2 3 = shiftS (tOddSet u1) (S + V) := by simp [dAO, pieceSet, hD]
  have d23 : ∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 3 → placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
    intro z hzi hzj
    rw [hd2] at hzi
    rw [hd3] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + V) + S = z - (V) := by abel
    have ht := tau (z - (S + V)) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + V)) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, evalO_lt w _ _ 0 2 z (V) (q.num, -q.den) (z - (V)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      evalO_lt w _ _ 0 3 z (S + V) ((q.num, -q.den) + (p.num, -p.den)) (z - (S + V)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kOddEF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Pi.zero_apply,
      add_zero] at ht hz hB4 ⊢
    linarith
  exact ⟨d01, d23⟩

/-- **The six copies, odd alternate child, `W_1` even, agree with the explicit constants.** -/
theorem sixOdd_ef (w u1 u2 : Word) (hph : phase w ≠ 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    SixAgree (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
      (placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclOdd_ef w u1 u2 hph hp hq
  obtain ⟨hD, hR, -, -⟩ := altOdd_ef w hph
  obtain ⟨m04, m24, m15, m35⟩ := sixOdd_ef_mixed w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhP hk hcompat
  obtain ⟨d01, d23⟩ := sixOdd_ef_dbl w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhP hk hcompat
  exact sixAgree_of _ _ _ _ _ _ _ (by simp [hD]) (by simp [hR]) (MarksIn.marksOdd_sub u1) (MarksIn.marksEven_sub u2)
    m04 m24 m15 m35 x05 x14 x25 x34 d01 d23

/-- The mixed pairs, odd alternate child, `W_1` odd. -/
theorem sixOdd_of_mixed (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (_hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    (∀ z, z ∈ mAO w u1 u2 0 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAO w u1 u2 2 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAO w u1 u2 1 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) ∧
      (∀ z, z ∈ mAO w u1 u2 3 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨cP0, cP1, cP2, cP3, cP4, cP5, cP6, cP7⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQ2, cQ3, cQ4, cQ5, cQ6, cQ7⟩ := corner_marks_even u2
  rw [← hp] at cP2 cP3 cP4 cP5 cP6 cP7
  rw [← hq] at cQ2 cQ3 cQ4 cQ5 cQ6 cQ7
  obtain ⟨vP0, vP1, vP2, vP3, vP4, vP5, vP6, vP7⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, vQ1, vQ2, vQ3, vQ4, vQ5, vQ6, vQ7⟩ := corner_raw oQ βQ _ _ _ hcQ
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
  set S := shiftP w with hSdef
  set κ := kOddOF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltOdd w oP.val oQ.val κ i z = placedAltOdd w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltOdd_add w _ _ κ i z).symm
  have hm0 : mAO w u1 u2 0 = shiftS (marksOdd u1) (0) := by simp [mAO, pieceSet, hD]
  have hm1 : mAO w u1 u2 1 = shiftS (marksOdd u1) (S + 0) := by simp [mAO, pieceSet, hD]
  have hm2 : mAO w u1 u2 2 = shiftS (marksOdd u1) (U + V) := by simp [mAO, pieceSet, hD]
  have hm3 : mAO w u1 u2 3 = shiftS (marksOdd u1) (S + (U + V)) := by simp [mAO, pieceSet, hD]
  have hm4 : mAO w u1 u2 4 = shiftS (marksEven u2) (A) := by simp [mAO, pieceSet, hD, hR]
  have hm5 : mAO w u1 u2 5 = shiftS (marksEven u2) (B + B - U) := by simp [mAO, pieceSet, hD, hR]
  have m04 : ∀ z, z ∈ mAO w u1 u2 0 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (0 + (A)) (by rw [hm0]; exact mem_shift _ _ _ (A) cP3 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ ((0 : ℤ × ℤ)) cQ0 (by abel))
    rw [evalO_lt w _ _ 0 0 _ (0) 0 (A) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 4 _ (A) 0 ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP3, vQ0] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddOF, dot2, hA, hBd, hV, texV1Odd, texV2,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero, zero_add] at h1 h2 hB4 hV4 ⊢
    linarith
  have m24 : ∀ z, z ∈ mAO w u1 u2 2 → z ∈ mAO w u1 u2 4 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (U + V + (A - e₂)) (by rw [hm2]; exact mem_shift _ _ _ (A - e₂) cP2 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (U + V - e₂) cQ7 (by abel))
    have evP2 : A - ((0 : ℤ), (1 : ℤ)) = A - e₂ := by ext <;> simp
    rw [evP2] at vP2
    have evQ7 : U + V + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) = U + V - e₂ := by ext <;> simp; ring
    rw [evQ7] at vQ7
    rw [evalO_lt w _ _ 0 2 _ (U + V) (q.num, -q.den) (A - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 4 _ (A) 0 (U + V - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP2, vQ7] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddOF, dot2, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m15 : ∀ z, z ∈ mAO w u1 u2 1 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + 0 + (B + e₁)) (by rw [hm1]; exact mem_shift _ _ _ (B + e₁) cP4 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (e₁) cQ1 (by rw [hSh]; abel))
    have evP4 : B + ((1 : ℤ), (0 : ℤ)) = B + e₁ := by ext <;> simp
    rw [evP4] at vP4
    have evQ1 : ((1 : ℤ), (0 : ℤ)) = e₁ := by ext <;> simp
    rw [evQ1] at vQ1
    rw [evalO_lt w _ _ 0 1 _ (S + 0) (p.num, -p.den) (B + e₁) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 5 _ (B + B - U) ((p.num, -p.den) + (p.num, -p.den)) (e₁) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vP4, vQ1] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddOF, dot2, hSh, hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m35 : ∀ z, z ∈ mAO w u1 u2 3 → z ∈ mAO w u1 u2 5 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + (U + V) + (B + e₁ - e₂)) (by rw [hm3]; exact mem_shift _ _ _ (B + e₁ - e₂) cP5 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (U + V + e₁ - e₂) cQ6 (by rw [hSh]; abel))
    have evP5 : B + ((1 : ℤ), (-1 : ℤ)) = B + e₁ - e₂ := by ext <;> simp; ring
    rw [evP5] at vP5
    have evQ6 : U + V + ((1 : ℤ), (-1 : ℤ)) = U + V + e₁ - e₂ := by ext <;> simp; ring
    rw [evQ6] at vQ6
    rw [evalO_lt w _ _ 0 3 _ (S + (U + V)) ((q.num, -q.den) + (p.num, -p.den)) (B + e₁ - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      evalO_ge w _ _ 0 5 _ (B + B - U) ((p.num, -p.den) + (p.num, -p.den)) (U + V + e₁ - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vP5, vQ6] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kOddOF, dot2, hSh, hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  exact ⟨m04, m24, m15, m35⟩

/-- The doubled pairs, odd alternate child, `W_1` odd. -/
theorem sixOdd_of_dbl (w u1 u2 : Word) (hph : phase w = 1)
    (_hp : (parentsAt w).odd = fracOdd u1) (_hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (_hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    (∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 1 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z) ∧
      (∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 3 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_of w hph
  obtain ⟨k, hk⟩ := hk
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
  set S := shiftP w with hSdef
  set κ := kOddOF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltOdd w oP.val oQ.val κ i z = placedAltOdd w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltOdd_add w _ _ κ i z).symm
  have hkS : ∀ x, x ∈ tOddSet u1 → x + S ∈ tOddSet u1 → oP.val (x + S) - oP.val x - dotS (affS w) x = k :=
    fun x h1 h2 => by have := hk x h1 h2; simpa [dot2, dotS] using this
  have tau : ∀ y, y ∈ tOddSet u1 → y + S ∈ tOddSet u1 →
      2 * k = dotS (p.num, -p.den) S + dotS (affS w) S - dotS (affS w) (A + B + ((1 : ℤ), (-1 : ℤ))) :=
    fun y h1 h2 => tau_shift oP.val (tOddSet u1) _ _ S (affS w) hhP k hkS y h1 h2
  have hd0 : dAO w u1 u2 0 = shiftS (tOddSet u1) (0) := by simp [dAO, pieceSet, hD]
  have hd1 : dAO w u1 u2 1 = shiftS (tOddSet u1) (S + 0) := by simp [dAO, pieceSet, hD]
  have d01 : ∀ z, z ∈ dAO w u1 u2 0 → z ∈ dAO w u1 u2 1 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
    intro z hzi hzj
    rw [hd0] at hzi
    rw [hd1] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + 0) + S = z - (0) := by abel
    have ht := tau (z - (S + 0)) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + 0)) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, evalO_lt w _ _ 0 0 z (0) 0 (z - (0)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      evalO_lt w _ _ 0 1 z (S + 0) (p.num, -p.den) (z - (S + 0)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kOddOF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Pi.zero_apply,
      zero_mul, add_zero] at ht hz hB4 ⊢
    linarith
  have hd2 : dAO w u1 u2 2 = shiftS (tOddSet u1) (U + V) := by simp [dAO, pieceSet, hD]
  have hd3 : dAO w u1 u2 3 = shiftS (tOddSet u1) (S + (U + V)) := by simp [dAO, pieceSet, hD]
  have d23 : ∀ z, z ∈ dAO w u1 u2 2 → z ∈ dAO w u1 u2 3 → placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
    intro z hzi hzj
    rw [hd2] at hzi
    rw [hd3] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + (U + V)) + S = z - (U + V) := by abel
    have ht := tau (z - (S + (U + V))) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + (U + V))) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, evalO_lt w _ _ 0 2 z (U + V) (q.num, -q.den) (z - (U + V)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      evalO_lt w _ _ 0 3 z (S + (U + V)) ((q.num, -q.den) + (p.num, -p.den)) (z - (S + (U + V))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kOddOF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, Pi.zero_apply,
      add_zero] at ht hz hB4 ⊢
    linarith
  exact ⟨d01, d23⟩

/-- **The six copies, odd alternate child, `W_1` odd, agree with the explicit constants.** -/
theorem sixOdd_of (w u1 u2 : Word) (hph : phase w = 1)
    (hp : (parentsAt w).odd = fracOdd u1) (hq : (parentsAt w).even = fracEven u2)
    (oP oQ : PartialOdometer) (βP βQ : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hhP : ∀ y ∈ tOddSet u1,
      texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y ∈ tOddSet u1 ∧
      2 * (oP.val (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den)
          (texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))) -
          2 * dotS ((parentsAt w).odd.num, -(parentsAt w).odd.den) y)
    (hk : ∃ k : ℤ, ∀ x, x ∈ tOddSet u1 → x + shiftP w ∈ tOddSet u1 →
      oP.val (x + shiftP w) - oP.val x - dot2 (affS w) x = k)
    (hcompat : AltMixedCompatOdd w u1 u2 (placedAltOdd w oP.val oQ.val 0)) :
    SixAgree (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) (marksOdd u1) (marksEven u2) dblEven
      (placedAltOdd w oP.val oQ.val (kOddOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclOdd_of w u1 u2 hph hp hq
  obtain ⟨hD, hR, -, -⟩ := altOdd_of w hph
  obtain ⟨m04, m24, m15, m35⟩ := sixOdd_of_mixed w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhP hk hcompat
  obtain ⟨d01, d23⟩ := sixOdd_of_dbl w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhP hk hcompat
  exact sixAgree_of _ _ _ _ _ _ _ (by simp [hD]) (by simp [hR]) (MarksIn.marksOdd_sub u1) (MarksIn.marksEven_sub u2)
    m04 m24 m15 m35 x05 x14 x25 x34 d01 d23

end FLatticePaper.Tiles.AltSixOdd
