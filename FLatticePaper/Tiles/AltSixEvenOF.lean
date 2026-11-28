import FLatticePaper.Tiles.AltSixEven

/-! # The constants of the six standard copies of the even alternate child, `W_1` odd

As `AltSixEven` for `W_1` even: `Q^{+,1}, Q^{+,2}, Q^{-,1}, Q^{-,2}` at `A, S + A, B, S + B` and `P^+, P^-` at `0, B + 2U + V`,
`S = U + B`; the mixed pairs at corner contacts, the doubled pairs by the half-turn of the doubled tile. -/

namespace FLatticePaper.Tiles.AltSixEvenOF

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.ClosedPathContacts FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.ClosedPathAltSum
open FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointFamily (h0)

/-- The explicit constants of the six copies of the even alternate child, `W_1` odd. -/
def kEvenOF (np dp nq dq hB hV βP βQ : ℤ) : ℕ → ℤ
  | 0 => -βQ
  | 1 => -hB + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) - βQ
  | 2 => -hB + (dp ^ 2 + 2 * dp * np - np ^ 2) - βQ
  | 3 => (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) - βQ
  | 4 => -βP
  | 5 => -hB - hV + (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) - βP
  | _ => 0

/-- The mixed pairs, even alternate child, `W_1` odd. -/
theorem sixEven_of_mixed (w u1 u2 : Word) (hph : phase w = 1)
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
    (∀ z, z ∈ mAE w u1 u2 0 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAE w u1 u2 2 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z) ∧
      (∀ z, z ∈ mAE w u1 u2 1 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) ∧
      (∀ z, z ∈ mAE w u1 u2 3 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨k, hk⟩ := hk
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
  set S := shiftQ w with hSdef
  set κ := kEvenOF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltEven w oP.val oQ.val κ i z = placedAltEven w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltEven_add w _ _ κ i z).symm
  have hm0 : mAE w u1 u2 0 = shiftS (marksEven u2) A := by simp [mAE, pieceSet, hD]
  have hm1 : mAE w u1 u2 1 = shiftS (marksEven u2) (S + A) := by simp [mAE, pieceSet, hD]
  have hm2 : mAE w u1 u2 2 = shiftS (marksEven u2) B := by simp [mAE, pieceSet, hD]
  have hm3 : mAE w u1 u2 3 = shiftS (marksEven u2) (S + B) := by simp [mAE, pieceSet, hD]
  have hm4 : mAE w u1 u2 4 = shiftS (marksOdd u1) 0 := by simp [mAE, pieceSet, hD, hR]
  have hm5 : mAE w u1 u2 5 = shiftS (marksOdd u1) (B + U + U + V) := by simp [mAE, pieceSet, hD, hR]
  have m04 : ∀ z, z ∈ mAE w u1 u2 0 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 0 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (A + ((0 : ℤ × ℤ))) (by rw [hm0]; exact mem_shift _ _ _ ((0 : ℤ × ℤ)) cQ0 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (A) cP3 (by abel))
    rw [eval_lt w _ _ 0 0 _ (A) 0 ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 4 _ (0) 0 (A) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ0, vP3] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kEvenOF, dot2, hA, hBd, hV, texV1Odd, texV2,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m24 : ∀ z, z ∈ mAE w u1 u2 2 → z ∈ mAE w u1 u2 4 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
    obtain ⟨C, hC⟩ := hcompat 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (B + (e₁)) (by rw [hm2]; exact mem_shift _ _ _ (e₁) cQ1 (by abel))
      (by rw [hm4]; exact mem_shift _ _ _ (B + e₁) cP4 (by abel))
    have evQ1 : ((1 : ℤ), (0 : ℤ)) = e₁ := by ext <;> simp
    rw [evQ1] at vQ1
    have evP4 : B + ((1 : ℤ), (0 : ℤ)) = B + e₁ := by ext <;> simp
    rw [evP4] at vP4
    rw [eval_lt w _ _ 0 2 _ (B) (p.num, -p.den) (e₁) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 4 _ (0) 0 (B + e₁) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ1, vP4] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kEvenOF, dot2, hBd, hV, texV2, Prod.fst_add, Prod.snd_add,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_mul, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m15 : ∀ z, z ∈ mAE w u1 u2 1 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 1 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + A + (U + V - e₂)) (by rw [hm1]; exact mem_shift _ _ _ (U + V - e₂) cQ7 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (A - e₂) cP2 (by rw [hSh]; abel))
    have evQ7 : U + V + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) = U + V - e₂ := by ext <;> simp; ring
    rw [evQ7] at vQ7
    have evP2 : A - ((0 : ℤ), (1 : ℤ)) = A - e₂ := by ext <;> simp
    rw [evP2] at vP2
    rw [eval_lt w _ _ 0 1 _ (S + A) (p.num, -p.den) (U + V - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 5 _ (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) (A - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vQ7, vP2] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kEvenOF, dot2, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  have m35 : ∀ z, z ∈ mAE w u1 u2 3 → z ∈ mAE w u1 u2 5 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
    obtain ⟨C, hC⟩ := hcompat 3 5 (by norm_num) (by norm_num) (by norm_num)
    have h1 := hC (S + B + (U + V + e₁ - e₂)) (by rw [hm3]; exact mem_shift _ _ _ (U + V + e₁ - e₂) cQ6 (by abel))
      (by rw [hm5]; exact mem_shift _ _ _ (B + e₁ - e₂) cP5 (by rw [hSh]; abel))
    have evQ6 : U + V + ((1 : ℤ), (-1 : ℤ)) = U + V + e₁ - e₂ := by ext <;> simp; ring
    rw [evQ6] at vQ6
    have evP5 : B + ((1 : ℤ), (-1 : ℤ)) = B + e₁ - e₂ := by ext <;> simp; ring
    rw [evP5] at vP5
    rw [eval_lt w _ _ 0 3 _ (S + B) ((p.num, -p.den) + (p.num, -p.den)) (U + V + e₁ - e₂) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel),
      eval_ge w _ _ 0 5 _ (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) (B + e₁ - e₂) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by rw [hSh]; abel), vQ6, vP5] at h1
    intro z hzi hzj
    have h2 := hC z hzi hzj
    rw [hff, hff]
    simp only [hκ, kEvenOF, dot2, hSh, hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, Pi.zero_apply, add_zero] at h1 h2 hB4 hV4 ⊢
    linarith
  exact ⟨m04, m24, m15, m35⟩

/-- The doubled pairs, even alternate child, `W_1` odd. -/
theorem sixEven_of_dbl (w u1 u2 : Word) (hph : phase w = 1)
    (_hp : (parentsAt w).odd = fracOdd u1) (_hq : (parentsAt w).even = fracEven u2)
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
    (∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 1 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z) ∧
      (∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 3 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z) := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
  obtain ⟨k, hk⟩ := hk
  obtain ⟨cP0, cP1, cP2, cP3, cP4, cP5, cP6, cP7⟩ := corner_marks_odd u1
  obtain ⟨cQ0, cQ1, cQ2, cQ3, cQ4, cQ5, cQ6, cQ7⟩ := corner_marks_even u2
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
  set S := shiftQ w with hSdef
  set κ := kEvenOF p.num p.den q.num q.den (h0 B) (h0 V) βP βQ with hκ
  have hff : ∀ i z, placedAltEven w oP.val oQ.val κ i z = placedAltEven w oP.val oQ.val 0 i z + κ i :=
    fun i z => (placedAltEven_add w _ _ κ i z).symm
  have hm0 : mAE w u1 u2 0 = shiftS (marksEven u2) A := by simp [mAE, pieceSet, hD]
  have hm1 : mAE w u1 u2 1 = shiftS (marksEven u2) (S + A) := by simp [mAE, pieceSet, hD]
  have hm2 : mAE w u1 u2 2 = shiftS (marksEven u2) B := by simp [mAE, pieceSet, hD]
  have hm3 : mAE w u1 u2 3 = shiftS (marksEven u2) (S + B) := by simp [mAE, pieceSet, hD]
  have hm4 : mAE w u1 u2 4 = shiftS (marksOdd u1) 0 := by simp [mAE, pieceSet, hD, hR]
  have hm5 : mAE w u1 u2 5 = shiftS (marksOdd u1) (B + U + U + V) := by simp [mAE, pieceSet, hD, hR]
  have hkS : ∀ x, x ∈ tEvenSet u2 → x + S ∈ tEvenSet u2 → oQ.val (x + S) - oQ.val x - dotS (affS w) x = k :=
    fun x h1 h2 => by have := hk x h1 h2; simpa [dot2, dotS] using this
  have tau : ∀ y, y ∈ tEvenSet u2 → y + S ∈ tEvenSet u2 →
      2 * k = dotS (q.num, -q.den) S + dotS (affS w) S - dotS (affS w) (U + V + ((1 : ℤ), (-1 : ℤ))) :=
    fun y h1 h2 => tau_shift oQ.val (tEvenSet u2) _ _ S (affS w) hhQ k hkS y h1 h2
  have hd0 : dAE w u1 u2 0 = shiftS (tEvenSet u2) (A) := by simp [dAE, pieceSet, hD]
  have hd1 : dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + A) := by simp [dAE, pieceSet, hD]
  have d01 : ∀ z, z ∈ dAE w u1 u2 0 → z ∈ dAE w u1 u2 1 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
    intro z hzi hzj
    rw [hd0] at hzi
    rw [hd1] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + A) + S = z - (A) := by abel
    have ht := tau (z - (S + A)) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + A)) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, eval_lt w _ _ 0 0 z (A) 0 (z - (A)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      eval_lt w _ _ 0 1 z (S + A) (p.num, -p.den) (z - (S + A)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kEvenOF, dot2, dotS, affS, offsetA, hSh, hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
      zero_mul, add_zero] at ht hz hB4 ⊢
    linarith
  have hd2 : dAE w u1 u2 2 = shiftS (tEvenSet u2) (B) := by simp [dAE, pieceSet, hD]
  have hd3 : dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + B) := by simp [dAE, pieceSet, hD]
  have d23 : ∀ z, z ∈ dAE w u1 u2 2 → z ∈ dAE w u1 u2 3 → placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z = placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
    intro z hzi hzj
    rw [hd2] at hzi
    rw [hd3] at hzj
    have yi := sub_mem_of_shift _ _ _ hzi
    have yj := sub_mem_of_shift _ _ _ hzj
    have ey : z - (S + B) + S = z - (B) := by abel
    have ht := tau (z - (S + B)) yj (by rw [ey]; exact yi)
    have hz := hkS (z - (S + B)) yj (by rw [ey]; exact yi)
    rw [ey] at hz
    rw [hff, hff, eval_lt w _ _ 0 2 z (B) (p.num, -p.den) (z - (B)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl,
      eval_lt w _ _ 0 3 z (S + B) ((p.num, -p.den) + (p.num, -p.den)) (z - (S + B)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) rfl]
    simp only [hκ, kEvenOF, dot2, dotS, affS, offsetA, hSh, hBd, hU, hV, texV1Even, texV2, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Pi.zero_apply,
      add_zero] at ht hz hB4 ⊢
    linarith
  exact ⟨d01, d23⟩

/-- **The six copies, even alternate child, `W_1` odd, agree with the explicit constants.** -/
theorem sixEven_of (w u1 u2 : Word) (hph : phase w = 1)
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
      (placedAltEven w oP.val oQ.val (kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
        (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ)) := by
  obtain ⟨x05, x14, x25, x34⟩ := altExclEven_of w u1 u2 hph hp hq
  obtain ⟨hD, hR, -, -⟩ := altEven_of w hph
  obtain ⟨m04, m24, m15, m35⟩ := sixEven_of_mixed w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhQ hk hcompat
  obtain ⟨d01, d23⟩ := sixEven_of_dbl w u1 u2 hph hp hq oP oQ βP βQ hcP hcQ hhQ hk hcompat
  exact sixAgree_of _ _ _ _ _ _ _ (by simp [hD]) (by simp [hR]) (MarksIn.marksEven_sub u2) (MarksIn.marksOdd_sub u1)
    m04 m24 m15 m35 x05 x14 x25 x34 d01 d23

end FLatticePaper.Tiles.AltSixEvenOF
