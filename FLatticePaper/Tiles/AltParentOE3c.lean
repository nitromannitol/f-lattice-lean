import FLatticePaper.Tiles.AltEvenTilePieces
import FLatticePaper.Tiles.AltSixOdd

/-! # Case 3 at a corrected parent, odd child, `W_1` even, type 3: the copies meeting only the L-entries of the parent -/

namespace FLatticePaper.Tiles.AltParentOE3c

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly FLatticePaper.Tiles.ClosedPathSum
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven FLatticePaper.Tiles.AltParentEven
open FLatticePaper.Tiles.AltSixOdd
open FLatticePaper.Tiles.JointFamily (h0)

theorem parent_oe3c_0 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (S : Set (ℤ × ℤ)) (hmL : ((1 : ℤ), (0 : ℤ)) ∈ S)
    (hd0 : ∀ x, x - 0 ∈ S → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - 0 ∈ S →
      oH.val x = oQ2.val (x - 0) + dotS 0 x + (βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 0 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  have mQ2 := corner_mem _ _ _ _ _ _ hcQ2
  have vQ2 := corner_raw _ _ _ _ _ hcQ2
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : U + (B + ((1 : ℤ), (0 : ℤ))) - (B + U) = 0 + (((1 : ℤ), (0 : ℤ))) := by
    ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : 0 + (((1 : ℤ), (0 : ℤ))) - 0 = ((1 : ℤ), (0 : ℤ)) := by abel
  have m1 : U + (B + ((1 : ℤ), (0 : ℤ))) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd0 _ (by rw [eg]; exact hmL)
  have m2 : U + (B + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 0 = shiftS (tOddSet u1) (U) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (B + ((1 : ℤ), (0 : ℤ))) mP.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h0p _ (by rw [eg]; exact hmL), eg, vQ2.2.1] at h1
  rw [evalO_lt w _ _ 0 0 _ (U) 0 (B + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dotS, dot2, kOddEF, Pi.zero_apply, zero_mul, mul_zero, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_oe3c_1 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hd4 : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h4p : ∀ x, x - (dq2, nq2) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - (dq2, nq2)) + dotS 0 x + (βH - βP2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 1 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  have mP2 := corner_mem _ _ _ _ _ _ hcP2
  have vP2 := corner_raw _ _ _ _ _ hcP2
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + U + ((0 : ℤ × ℤ)) - (B + U) = (dq2, nq2) + ((2 * dp2, 2 * np2)) := by
    rw [hSh]; ext <;> simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : (dq2, nq2) + ((2 * dp2, 2 * np2)) - (dq2, nq2) = (2 * dp2, 2 * np2) := by abel
  have m1 : S + U + ((0 : ℤ × ℤ)) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd4 _ (by rw [eg]; exact mP2.2.2.2.1)
  have m2 : S + U + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 1 = shiftS (tOddSet u1) (S + U) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h4p _ (by rw [eg]; exact mP2.2.2.2.1), eg, vP2.2.2.2.1] at h1
  rw [evalO_lt w _ _ 0 1 _ (S + U) (p.num, -p.den) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dotS, dot2, kOddEF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_oe3c_2 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hd5 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h5p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) -h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dp2 * nq2 + dq2 ^ 2 + dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 2 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  have mP2 := corner_mem _ _ _ _ _ _ hcP2
  have vP2 := corner_raw _ _ _ _ _ hcP2
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : V + (A) - (B + U) = ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) + ((0 : ℤ × ℤ)) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) + ((0 : ℤ × ℤ)) - ((np2 - dp2, np2 + dp2) - (dq2, nq2) + (nq2 - dq2, nq2 + dq2)) = (0 : ℤ × ℤ) := by abel
  have m1 : V + (A) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd5 _ (by rw [eg]; exact mP2.1)
  have m2 : V + (A) ∈ ClosedPathAlt.dAO w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 2 = shiftS (tOddSet u1) (V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A) mP.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h5p _ (by rw [eg]; exact mP2.1), eg, vP2.1] at h1
  rw [evalO_lt w _ _ 0 2 _ (V) (q.num, -q.den) (A) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dotS, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_oe3c_3 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (S : Set (ℤ × ℤ)) (hmL : (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ S)
    (hd3 : ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ S → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h3p : ∀ x, x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ S →
      oH.val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 + dp2 * nq2 - dp2 - dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 3 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mP := corner_mem _ _ _ _ _ _ hcP
  have vP := corner_raw _ _ _ _ _ hcP
  have mQ2 := corner_mem _ _ _ _ _ _ hcQ2
  have vQ2 := corner_raw _ _ _ _ _ hcQ2
  rw [hdP] at mP
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : S + V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) = ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - ((2 * dp2, 2 * np2) + (2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) = (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by abel
  have m1 : S + V + (A - ((0 : ℤ), (1 : ℤ))) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd3 _ (by rw [eg]; exact hmL)
  have m2 : S + V + (A - ((0 : ℤ), (1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 3 = shiftS (tOddSet u1) (S + V) := by simp [ClosedPathAlt.dAO, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (A - ((0 : ℤ), (1 : ℤ))) mP.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h3p _ (by rw [eg]; exact hmL), eg, vQ2.2.2.2.2.2.2.2] at h1
  rw [evalO_lt w _ _ 0 3 _ (S + V) ((q.num, -q.den) + (p.num, -p.den)) (A - ((0 : ℤ), (1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_oe3c_4 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 4 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  have mQ2 := corner_mem _ _ _ _ _ _ hcQ2
  have vQ2 := corner_raw _ _ _ _ _ hcQ2
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (B + U) = ((np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ))) - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) = (dq2, nq2) + (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (-1 : ℤ)) := by abel
  have m1 : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd1 _ (by rw [eg]; exact mQ2.2.2.2.2.2.2.1)
  have m2 : 0 + (U + V + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAO w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 4 = shiftS (tEvenSet u2) (0) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (U + V + ((1 : ℤ), (-1 : ℤ))) mQ.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h1p _ (by rw [eg]; exact mQ2.2.2.2.2.2.2.1), eg, vQ2.2.2.2.2.2.2.1] at h1
  rw [evalO_ge w _ _ 0 4 _ (0) 0 (U + V + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, dotS, dot2, kOddEF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_oe3c_5 (w u1 u2 : Word) (hph : phase w ≠ 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 ∧ (parentsAt w).odd.den = dp2 ∧
      (parentsAt w).even.num = 2 * np2 + nq2 ∧ (parentsAt w).even.den = 2 * dp2 + dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hd2 : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h2p : ∀ x, x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 + dp2 * nq2 - dq2 * np2 - np2 ^ 2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z - placedAltOdd w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAO w u1 u2 5 →
      oH.val (z - (texV2 (parentsAt w).odd + texV1Even (parentsAt w).even)) + dot2 ((parentsAt w).odd.num, -(parentsAt w).odd.den) z + (-h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num + (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2) - βH) = placedAltOdd w oP.val oQ.val (kOddEF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altOdd_ef w hph
  obtain ⟨C, hC⟩ := hpc
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hrel
  have hpar := (parentsAt_valid w).odd_parity
  have hpe := (parentsAt_valid w).even_parity
  unfold Fraction.Odd at hpar
  unfold Fraction.Even at hpe
  have hB4 := h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  have hV4 := h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  have hB24 := h0_even (np2 - dp2, np2 + dp2) (by simp only; omega)
  have hV24 := h0_even (nq2 - dq2, nq2 + dq2) (by simp only; omega)
  have mQ := corner_mem _ _ _ _ _ _ hcQ
  have vQ := corner_raw _ _ _ _ _ hcQ
  have mQ2 := corner_mem _ _ _ _ _ _ hcQ2
  have vQ2 := corner_raw _ _ _ _ _ hcQ2
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftP w with hSdef
  have ez : A + B + B + U + ((0 : ℤ × ℤ)) - (B + U) = ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) + ((0 : ℤ × ℤ)) := by
    ext <;> simp only [hA, hBd, hU, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) + ((0 : ℤ × ℤ)) - ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2)) = (0 : ℤ × ℤ) := by abel
  have m1 : A + B + B + U + ((0 : ℤ × ℤ)) - (B + U) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd2 _ (by rw [eg]; exact mQ2.1)
  have m2 : A + B + B + U + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAO w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAO w u1 u2 5 = shiftS (tEvenSet u2) (A + B + B + U) := by simp [ClosedPathAlt.dAO, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mQ.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h2p _ (by rw [eg]; exact mQ2.1), eg, vQ2.1] at h1
  rw [evalO_ge w _ _ 0 5 _ (A + B + B + U) ((p.num, -p.den) + (p.num, -p.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vQ.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltOdd_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dotS, dot2, kOddEF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, kOddEF, hr1, hr2, hr3, hr4] at h1
  linarith

end FLatticePaper.Tiles.AltParentOE3c

