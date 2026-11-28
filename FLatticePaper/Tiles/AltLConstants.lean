import FLatticePaper.Tiles.AltLSides
import FLatticePaper.Tiles.AltEvenTilePieces

/-! # The constants of the L-entries of a corrected parent piece

At a corrected parent word, two entries of the parent's decomposition are L-corrections, and on their kept sides the parent equals
the standard register up to one constant (`AltLSides.L_identity`). Each L-entry meets a standard subtile (`4` or `5`) at a corner
on a kept side; this contact gives its constant, which is the constant of the standard entry it replaces (`AltParentEven`,
`AltEvenTilePieces`). -/

namespace FLatticePaper.Tiles.AltLConstants

open FLatticePaper.Tiles FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointFamily (h0)

/-- **The constants of the L-entries `1`, `2` of a corrected odd alternate tile, `W_1` odd**, from their corner contacts with the
standard subtiles, the L-entries known only on sets `S1`, `S2` containing the contact corners. -/
theorem L12_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (S1 S2 : Set (ℤ × ℤ))
    (hm1 : (np - dp, np + dp) + ((1 : ℤ), (0 : ℤ)) ∈ S1)
    (h1p : ∀ x, x - ((np - dp, np + dp) - (dq, nq)) ∈ S1 → oH.val x = oP.val (x - ((np - dp, np + dp) - (dq, nq))) + dotS (np, -dp) x + b1)
    (hm2 : (2 * dp, 2 * np) - ((0 : ℤ), (1 : ℤ)) ∈ S2)
    (h2p : ∀ x, x - ((dq, nq) + (nq - dq, nq + dq)) ∈ S2 → oH.val x = oP.val (x - ((dq, nq) + (nq - dq, nq + dq))) + dotS (nq, -dq) x + b2)
    (h4p : ∀ x, x - (2 * dp, 2 * np) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - (2 * dp, 2 * np)) + dotS 0 x + (βH - βQ))
    (h5p : ∀ x, x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + ((2 * dp ^ 2 + 4 * dp * np - dp * nq - dp + dq * np - 2 * np ^ 2 - np) + βH - βQ)) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βP ∧ b2 = -h0 (nq - dq, nq + dq) + (-2 * dp * nq + dq ^ 2 + 2 * dq * np + 2 * dq * nq - nq ^ 2) + βH - βP := by
  have mP := AltParentEven.corner_mem _ _ _ _ _ _ hcP
  have mQ := AltParentEven.corner_mem _ _ _ _ _ _ hcQ
  have vP := corner_raw oP βP _ _ _ hcP
  have vQ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z1l : ((np - dp, np + dp) - (dq, nq)) + ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) - ((np - dp, np + dp) - (dq, nq)) = (np - dp, np + dp) + ((1 : ℤ), (0 : ℤ)) := by abel
  have z1k : ((np - dp, np + dp) - (dq, nq)) + ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq)) = ((1 : ℤ), (0 : ℤ)) := by ext <;> simp <;> ring
  have e1a := h1p _ (by rw [z1l]; exact hm1)
  have e1b := h5p _ (by rw [z1k]; exact mQ.2.1)
  rw [z1l, vP.2.2.2.2.1] at e1a
  rw [z1k, vQ.2.1] at e1b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1a e1b
  have z2l : ((dq, nq) + (nq - dq, nq + dq)) + ((2 * dp, 2 * np) - ((0 : ℤ), (1 : ℤ))) - ((dq, nq) + (nq - dq, nq + dq)) = (2 * dp, 2 * np) - ((0 : ℤ), (1 : ℤ)) := by abel
  have z2k : ((dq, nq) + (nq - dq, nq + dq)) + ((2 * dp, 2 * np) - ((0 : ℤ), (1 : ℤ))) - (2 * dp, 2 * np) = (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by ext <;> simp; ring
  have e2a := h2p _ (by rw [z2l]; exact hm2)
  have e2b := h4p _ (by rw [z2k]; exact mQ.2.2.2.2.2.2.2)
  rw [z2l, vP.2.2.1] at e2a
  rw [z2k, vQ.2.2.2.2.2.2.2] at e2b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at e2a e2b
  exact ⟨by linarith, by linarith⟩

/-- **The constants of the L-entries `1`, `2` of a corrected odd alternate tile, `W_1` even**, from their corner contacts with the
standard subtiles, the L-entries known only on sets `S1`, `S2` containing the contact corners. -/
theorem L12EF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (S1 S2 : Set (ℤ × ℤ))
    (hm1 : (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ S1)
    (h1p : ∀ x, x - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) ∈ S1 → oH.val x = oP.val (x - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp))) + dotS (np, -dp) x + b1)
    (hm2 : ((1 : ℤ), (0 : ℤ)) ∈ S2)
    (h2p : ∀ x, x - (nq - dq, nq + dq) ∈ S2 → oH.val x = oP.val (x - (nq - dq, nq + dq)) + dotS (nq, -dq) x + b2)
    (h4p : ∀ x, x - 0 ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - 0) + dotS 0 x + (βH - βQ))
    (h5p : ∀ x, x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + ((2 * dp ^ 2 + 4 * dp * np + 3 * dp * nq - dp - 3 * dq * np - 2 * np ^ 2 - np) + βH - βQ)) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βP ∧ b2 = -h0 (nq - dq, nq + dq) + (dq ^ 2 + 2 * dq * nq - nq ^ 2) + βH - βP := by
  have mP := AltParentEven.corner_mem _ _ _ _ _ _ hcP
  have mQ := AltParentEven.corner_mem _ _ _ _ _ _ hcQ
  have vP := corner_raw oP βP _ _ _ hcP
  have vQ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z1l : ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) + ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) = (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by abel
  have z1k : ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) + ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ))) - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq)) = (dq, nq) - ((0 : ℤ), (1 : ℤ)) := by ext <;> simp <;> ring
  have e1a := h1p _ (by rw [z1l]; exact hm1)
  have e1b := h5p _ (by rw [z1k]; exact mQ.2.2.1)
  rw [z1l, vP.2.2.2.2.2.2.2] at e1a
  rw [z1k, vQ.2.2.1] at e1b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1a e1b
  have z2l : (nq - dq, nq + dq) + (((1 : ℤ), (0 : ℤ))) - (nq - dq, nq + dq) = ((1 : ℤ), (0 : ℤ)) := by abel
  have z2k : (nq - dq, nq + dq) + (((1 : ℤ), (0 : ℤ))) - 0 = (nq - dq, nq + dq) + ((1 : ℤ), (0 : ℤ)) := by ext <;> simp
  have e2a := h2p _ (by rw [z2l]; exact hm2)
  have e2b := h4p _ (by rw [z2k]; exact mQ.2.2.2.2.1)
  rw [z2l, vP.2.1] at e2a
  rw [z2k, vQ.2.2.2.2.1] at e2b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e2a e2b
  exact ⟨by linarith, by linarith⟩

/-- **The constants of the L-entries `0`, `3` of a corrected even alternate tile, `W_1` even**, from their corner contacts with the
standard subtiles, the L-entries known only on sets `S1`, `S2` containing the contact corners. -/
theorem L03EF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b3 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (S1 S2 : Set (ℤ × ℤ))
    (hm0 : (dq, nq) ∈ S1)
    (h0p : ∀ x, x - 0 ∈ S1 → oH.val x = oQ.val (x - 0) + dotS 0 x + b0)
    (hm3 : (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) ∈ S2)
    (h3p : ∀ x, x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) ∈ S2 → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b3)
    (h4p : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - (dq, nq)) + dotS 0 x + (βH - βP))
    (h5p : ∀ x, x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + (-h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP)) :
    b0 = βH - βQ ∧ b3 = (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) + βH - βQ := by
  have mP := AltParentEven.corner_mem _ _ _ _ _ _ hcP
  have mQ := AltParentEven.corner_mem _ _ _ _ _ _ hcQ
  have vP := corner_raw oP βP _ _ _ hcP
  have vQ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z0l : 0 + ((dq, nq)) - 0 = (dq, nq) := by abel
  have z0k : 0 + ((dq, nq)) - (dq, nq) = (0 : ℤ × ℤ) := by ext <;> simp
  have e0a := h0p _ (by rw [z0l]; exact hm0)
  have e0b := h4p _ (by rw [z0k]; exact mP.1)
  rw [z0l, vQ.2.2.2.1] at e0a
  rw [z0k, vP.1] at e0b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e0a e0b
  have z3l : ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) + ((nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) = (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) := by abel
  have z3k : ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) + ((nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) = (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp <;> ring
  have e3a := h3p _ (by rw [z3l]; exact hm3)
  have e3b := h5p _ (by rw [z3k]; exact mP.2.2.2.2.2.2.1)
  rw [z3l, vQ.2.2.2.2.2.1] at e3a
  rw [z3k, vP.2.2.2.2.2.2.1] at e3b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e3a e3b
  exact ⟨by linarith, by linarith⟩

/-- **The constants of the L-entries `0`, `3` of a corrected even alternate tile, `W_1` odd**, from their corner contacts with the
standard subtiles, the L-entries known only on sets `S1`, `S2` containing the contact corners. -/
theorem L03_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b3 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (S1 S2 : Set (ℤ × ℤ))
    (hm0 : (0 : ℤ × ℤ) ∈ S1)
    (h0p : ∀ x, x - (2 * dp, 2 * np) ∈ S1 → oH.val x = oQ.val (x - (2 * dp, 2 * np)) + dotS 0 x + b0)
    (hm3 : (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) ∈ S2)
    (h3p : ∀ x, x - ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) ∈ S2 → oH.val x = oQ.val (x - ((2 : ℤ) • (np - dp, np + dp) + (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b3)
    (h4p : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - 0) + dotS 0 x + (βH - βP))
    (h5p : ∀ x, x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + (-h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP)) :
    b0 = βH - βQ ∧ b3 = (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) + βH - βQ := by
  have mP := AltParentEven.corner_mem _ _ _ _ _ _ hcP
  have mQ := AltParentEven.corner_mem _ _ _ _ _ _ hcQ
  have vP := corner_raw oP βP _ _ _ hcP
  have vQ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z0l : (2 * dp, 2 * np) + ((0 : ℤ × ℤ)) - (2 * dp, 2 * np) = (0 : ℤ × ℤ) := by abel
  have z0k : (2 * dp, 2 * np) + ((0 : ℤ × ℤ)) - 0 = (2 * dp, 2 * np) := by ext <;> simp
  have e0a := h0p _ (by rw [z0l]; exact hm0)
  have e0b := h4p _ (by rw [z0k]; exact mP.2.2.2.1)
  rw [z0l, vQ.1] at e0a
  rw [z0k, vP.2.2.2.1] at e0b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e0a e0b
  have z3l : ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) + ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) = (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) := by abel
  have z3k : ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) + ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) = (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) := by ext <;> simp <;> ring
  have e3a := h3p _ (by rw [z3l]; exact hm3)
  have e3b := h5p _ (by rw [z3k]; exact mP.2.2.2.2.2.1)
  rw [z3l, vQ.2.2.2.2.2.2.1] at e3a
  rw [z3k, vP.2.2.2.2.2.1] at e3b
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e3a e3b
  exact ⟨by linarith, by linarith⟩

end FLatticePaper.Tiles.AltLConstants

