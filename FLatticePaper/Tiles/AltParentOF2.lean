import FLatticePaper.Tiles.AltParentEven
import FLatticePaper.Tiles.AltSixEvenOF

/-! # Case 3, even alternate child, `W_1` odd, type 2: the six parent contacts -/

namespace FLatticePaper.Tiles.AltParentOF2

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly FLatticePaper.Tiles.ClosedPathSum
open FLatticePaper.Tiles.ClosedPathAlt FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven FLatticePaper.Tiles.AltParentEven
open FLatticePaper.Tiles.JointFamily (h0)

theorem parent_of2_0 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (_hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (_hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (_hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (_hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 0 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 0 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 0 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  set S := shiftQ w with hSdef
  have ez : A + (V + ((1 : ℤ), (0 : ℤ))) - (U + U + V) = (2 * dp2, 2 * np2) + (((1 : ℤ), (0 : ℤ))) := by
    ext <;> simp only [hA, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have eg : (2 * dp2, 2 * np2) + (((1 : ℤ), (0 : ℤ))) - (2 * dp2, 2 * np2) = ((1 : ℤ), (0 : ℤ)) := by abel
  have m1 : A + (V + ((1 : ℤ), (0 : ℤ))) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd4 _ (by rw [eg]; exact mQ2.2.1)
  have m2 : A + (V + ((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 0 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 0 = shiftS (tEvenSet u2) (A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (0 : ℤ))) mQ.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h4p _ (by rw [eg]; exact mQ2.2.1), eg, vQ2.2.1] at h1
  rw [eval_lt w _ _ 0 0 _ (A) 0 (V + ((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_of2_1 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (_hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (_hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (_hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 1 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 1 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 1 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  have mP2 := corner_mem _ _ _ _ _ _ hcP2
  have vP2 := corner_raw _ _ _ _ _ hcP2
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (U + U + V) = ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) + ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) := by
    rw [hSh]; ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) + ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) = (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) := by abel
  have m1 : S + A + (V + ((1 : ℤ), (-1 : ℤ))) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd2 _ (by rw [eg]; exact mP2.2.2.2.2.2.2.1)
  have m2 : S + A + (V + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 1 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 1 = shiftS (tEvenSet u2) (S + A) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (V + ((1 : ℤ), (-1 : ℤ))) mQ.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h2p _ (by rw [eg]; exact mP2.2.2.2.2.2.2.1), eg, vP2.2.2.2.2.2.2.1] at h1
  rw [eval_lt w _ _ 0 1 _ (S + A) (p.num, -p.den) (V + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_of2_2 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (_hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (_hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (_hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 2 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 2 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 2 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  have mP2 := corner_mem _ _ _ _ _ _ hcP2
  have vP2 := corner_raw _ _ _ _ _ hcP2
  rw [hdQ] at mQ
  set p := (parentsAt w).odd with hpdef
  set q := (parentsAt w).even with hqdef
  set A := texV1Odd p with hA
  set B := texV2 p with hBd
  set U := texV1Even q with hU
  set V := texV2 q with hV
  set S := shiftQ w with hSdef
  have ez : B + (U) - (U + U + V) = ((np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((0 : ℤ × ℤ)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((0 : ℤ × ℤ)) - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) = (0 : ℤ × ℤ) := by abel
  have m1 : B + (U) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd1 _ (by rw [eg]; exact mP2.1)
  have m2 : B + (U) ∈ ClosedPathAlt.dAE w u1 u2 2 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 2 = shiftS (tEvenSet u2) (B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (U) mQ.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h1p _ (by rw [eg]; exact mP2.1), eg, vP2.1] at h1
  rw [eval_lt w _ _ 0 2 _ (B) (p.num, -p.den) (U) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_of2_3 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (_hdP : oP.dom = Standard.oddTile u1) (hdQ : oQ.dom = Standard.evenTile u2)
    (_hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (_hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (_hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (_hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (_hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 3 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 3 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 3 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  set S := shiftQ w with hSdef
  have ez : S + B + (((1 : ℤ), (0 : ℤ))) - (U + U + V) = ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (0 : ℤ))) := by
    rw [hSh]; ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) + ((nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (0 : ℤ))) - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) = (nq2 - dq2, nq2 + dq2) + ((1 : ℤ), (0 : ℤ)) := by abel
  have m1 : S + B + (((1 : ℤ), (0 : ℤ))) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd5 _ (by rw [eg]; exact mQ2.2.2.2.2.1)
  have m2 : S + B + (((1 : ℤ), (0 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 3 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 3 = shiftS (tEvenSet u2) (S + B) := by simp [ClosedPathAlt.dAE, pieceSet, hD]
    rw [hdj]
    exact mem_shift _ _ _ (((1 : ℤ), (0 : ℤ))) mQ.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h5p _ (by rw [eg]; exact mQ2.2.2.2.2.1), eg, vQ2.2.2.2.2.1] at h1
  rw [eval_lt w _ _ 0 3 _ (S + B) ((p.num, -p.den) + (p.num, -p.den)) (((1 : ℤ), (0 : ℤ))) (by norm_num) (by rw [hD]; rfl) (by rw [hAf]; rfl) (by abel), vQ.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  rw [hSh] at h1
  try simp only [hBd, hU, texV1Even, texV2, Prod.fst_add, Prod.snd_add, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_of2_4 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (_hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (_hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (_hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 4 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 4 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 4 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  set S := shiftQ w with hSdef
  have ez : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (U + U + V) = 0 + ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) := by
    ext <;> simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : 0 + ((2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ))) - 0 = (2 * dp2, 2 * np2) + (np2 - dp2, np2 + dp2) + ((1 : ℤ), (-1 : ℤ)) := by abel
  have m1 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd0 _ (by rw [eg]; exact mP2.2.2.2.2.2.2.1)
  have m2 : 0 + (A + B + ((1 : ℤ), (-1 : ℤ))) ∈ ClosedPathAlt.dAE w u1 u2 4 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 4 = shiftS (tOddSet u1) (0) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ (A + B + ((1 : ℤ), (-1 : ℤ))) mP.2.2.2.2.2.2.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h0p _ (by rw [eg]; exact mP2.2.2.2.2.2.2.1), eg, vP2.2.2.2.2.2.2.1] at h1
  rw [eval_ge w _ _ 0 4 _ (0) 0 (A + B + ((1 : ℤ), (-1 : ℤ))) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.2.2.2.2.2.2.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, zero_mul, add_zero, zero_add, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

theorem parent_of2_5 (w u1 u2 : Word) (hph : phase w = 1)
    (np2 dp2 nq2 dq2 : ℤ) (hpar2 : (np2 + dp2) % 2 = 1) (hqe2 : (nq2 + dq2) % 2 = 0)
    (hrel : (parentsAt w).odd.num = np2 + nq2 ∧ (parentsAt w).odd.den = dp2 + dq2 ∧
      (parentsAt w).even.num = nq2 ∧ (parentsAt w).even.den = dq2)
    (oP oQ oH oP2 oQ2 : PartialOdometer) (βP βQ βH βP2 βQ2 : ℤ)
    (hdP : oP.dom = Standard.oddTile u1) (_hdQ : oQ.dom = Standard.evenTile u2)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
      ((parentsAt w).odd.num, -(parentsAt w).odd.den))
    (_hcQ : TileTranslation.StdCornerValues oQ 0 βQ (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
      ((parentsAt w).even.num, -(parentsAt w).even.den))
    (hcP2 : TileTranslation.StdCornerValues oP2 0 βP2 (2 * dp2, 2 * np2) (np2 - dp2, np2 + dp2) (np2, -dp2))
    (_hcQ2 : TileTranslation.StdCornerValues oQ2 0 βQ2 (dq2, nq2) (nq2 - dq2, nq2 + dq2) (nq2, -dq2))
    (_hd0 : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h0p : ∀ x, x - 0 ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - 0) + dotS 0 x + (βH - βP2))
    (_hd1 : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h1p : ∀ x, x - ((np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS (np2, -dp2) x + (-h0 (np2 - dp2, np2 + dp2) + (dp2 ^ 2 + 2 * dp2 * np2 - np2 ^ 2) + βH - βP2))
    (_hd2 : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h2p : ∀ x, x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((dq2, nq2) + (nq2 - dq2, nq2 + dq2))) + dotS (nq2, -dq2) x + (-h0 (nq2 - dq2, nq2 + dq2) + (-2 * dp2 * nq2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - nq2 ^ 2) + βH - βP2))
    (hd3 : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h3p : ∀ x, x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) ∈ (↑oP2.dom : Set (ℤ × ℤ)) →
      oH.val x = oP2.val (x - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2))) + dotS ((np2, -dp2) + (nq2, -dq2)) x + (-h0 (np2 - dp2, np2 + dp2) - h0 (nq2 - dq2, nq2 + dq2) + (dp2 ^ 2 + dp2 * dq2 + 2 * dp2 * np2 + dq2 ^ 2 + 2 * dq2 * np2 + 2 * dq2 * nq2 - np2 ^ 2 - np2 * nq2 - nq2 ^ 2) + βH - βP2))
    (_hd4 : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h4p : ∀ x, x - (2 * dp2, 2 * np2) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - (2 * dp2, 2 * np2)) + dotS 0 x + (βH - βQ2))
    (_hd5 : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (_h5p : ∀ x, x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2)) ∈ (↑oQ2.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ2.val (x - ((2 : ℤ) • (np2 - dp2, np2 + dp2) - (dq2, nq2))) + dotS ((2 : ℤ) • (np2, -dp2)) x + ((2 * dp2 ^ 2 + 4 * dp2 * np2 - dp2 * nq2 - dp2 + dq2 * np2 - 2 * np2 ^ 2 - np2) + βH - βQ2))
    (hpc : ∃ C : ℤ, ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z - placedAltEven w oP.val oQ.val 0 5 z = C) :
    ∀ z, z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even) ∈ (↑oH.dom : Set (ℤ × ℤ)) → z ∈ ClosedPathAlt.dAE w u1 u2 5 →
      oH.val (z - (texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even)) + dot2 ((parentsAt w).even.num, -(parentsAt w).even.den) z + (-h0 (texV2 (parentsAt w).even) + ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).odd.num - 2 * (parentsAt w).odd.den * (parentsAt w).even.num) - βH) = placedAltEven w oP.val oQ.val (AltSixEvenOF.kEvenOF (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den (h0 (texV2 (parentsAt w).odd)) (h0 (texV2 (parentsAt w).even)) βP βQ) 5 z := by
  obtain ⟨hD, hR, hAf, hSh⟩ := altEven_of w hph
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
  set S := shiftQ w with hSdef
  have ez : B + U + U + V + ((0 : ℤ × ℤ)) - (U + U + V) = ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) + ((0 : ℤ × ℤ)) := by
    ext <;> simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, hr1, hr2, hr3, hr4] <;> ring
  have eg : ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) + ((0 : ℤ × ℤ)) - ((np2 - dp2, np2 + dp2) + (nq2 - dq2, nq2 + dq2)) = (0 : ℤ × ℤ) := by abel
  have m1 : B + U + U + V + ((0 : ℤ × ℤ)) - (U + U + V) ∈ (↑oH.dom : Set (ℤ × ℤ)) := by
    rw [ez]; exact hd3 _ (by rw [eg]; exact mP2.1)
  have m2 : B + U + U + V + ((0 : ℤ × ℤ)) ∈ ClosedPathAlt.dAE w u1 u2 5 := by
    have hdj : ClosedPathAlt.dAE w u1 u2 5 = shiftS (tOddSet u1) (B + U + U + V) := by simp [ClosedPathAlt.dAE, pieceSet, hD, hR]
    rw [hdj]
    exact mem_shift _ _ _ ((0 : ℤ × ℤ)) mP.1 (by abel)
  have h1 := hC _ m1 m2
  rw [ez, h3p _ (by rw [eg]; exact mP2.1), eg, vP2.1] at h1
  rw [eval_ge w _ _ 0 5 _ (B + U + U + V) ((p.num, -p.den) + (q.num, -q.den)) ((0 : ℤ × ℤ)) (by norm_num) (by rw [hR]; rfl) (by rw [hAf]; rfl) (by abel), vP.1] at h1
  intro z hz1 hz2
  have h2 := hC z hz1 hz2
  rw [← placedAltEven_add]
  simp only [hBd, hU, hV, texV1Even, texV2, Prod.fst_add, Prod.snd_add, dotS, dot2, AltSixEvenOF.kEvenOF, Pi.zero_apply, add_zero, hr1, hr2, hr3, hr4] at h1 h2 hB4 hV4 ⊢
  try simp only [hA, hBd, hU, hV, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, dotS, dot2, AltSixEvenOF.kEvenOF, hr1, hr2, hr3, hr4] at h1
  linarith

end FLatticePaper.Tiles.AltParentOF2
