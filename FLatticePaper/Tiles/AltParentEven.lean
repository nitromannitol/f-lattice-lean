import FLatticePaper.Tiles.AltSixEven

/-! # Case 3 of `lemma:tile-odometer-existence`: the alternate parent piece of the even alternate child

The even alternate child `T̂(q_0)` of `w` contains the odd alternate tile `T̂(p_1)` of its register (entry `6` of
`tileAltEvenPieces`). Its constant is read at one corner contact with each of the six standard copies: a corner of a standard
subtile of `T̂(p_1)` (its decomposition at the register's word) that is a corner of the copy's register tile.

The constants of those subtiles of `T̂(p_1)` are explicit (`oddPieces_of`): `0` on the subtiles `P^{+,1}` at the origin and `Q^+`
(the normalisation and a corner contact), and the half-turn partners `P^{-,2}`, `Q^-` by the half-turn of the odd alternate
tile (`AltParentConstants.sigma_pair`). -/

namespace FLatticePaper.Tiles.AltParentEven

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointFamily (h0)

/-- **The constants of four standard subtiles of an odd alternate tile odometer, `W_1` odd.** The subtiles `P^{+,1}`, `P^{-,2}`
at `0`, `B + V` (affine factors `0`, `a + b`) of the odd register and `Q^+`, `Q^-` at `A`, `2B - U` (affine factors `0`, `2a`) of
the even register; the tile odometer `oH` has the half-turn about `D̂ = A + 2B + V + 1 - i` with `Ê = 2a + b`. -/
theorem oddPieces_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b3 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) =
        dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)),
      2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - x) -
        oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq))
          ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) -
        2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hN : oH.val 0 = βH)
    (hd0 : ∀ x, x ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (2 * dp, 2 * np) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - 0) + dotS 0 x + b0)
    (h3p : ∀ x, x - ((np - dp, np + dp) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((np - dp, np + dp) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b3)
    (h4p : ∀ x, x - (2 * dp, 2 * np) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - (2 * dp, 2 * np)) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b5) :
    b0 = βH - βP ∧ b4 = βH - βQ ∧
      b3 = -h0 (np - dp, np + dp) - h0 (nq - dq, nq + dq) +
        (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP ∧
      b5 = (2 * dp ^ 2 + 4 * dp * np - dp * nq - dp + dq * np - 2 * np ^ 2 - np) + βH - βQ := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, ⟨mX, -⟩, -, -, -, -⟩ := hcP'
  obtain ⟨⟨n0, -⟩, -, -, -, -, -, -, -⟩ := hcQ'
  obtain ⟨vP0, -, -, vPX, -, -, -, -⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, -, -, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  -- the origin piece
  have e0 := h0p 0 (by simpa using m0)
  have hb0 : b0 = βH - βP := by
    rw [hN, sub_zero, vP0] at e0
    simp [dotS] at e0
    linarith
  -- the contact of P^{+,1} and Q^+ at A
  have hb4 : b4 = βH - βQ := by
    have e1 := h0p (2 * dp, 2 * np) (by simpa using mX)
    have e2 := h4p (2 * dp, 2 * np) (by simpa using n0)
    rw [sub_zero, vPX] at e1
    rw [sub_self, vQ0] at e2
    simp [dotS] at e1 e2
    linarith
  -- the half-turn partners
  have hs3 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ 0 0 ((np, -dp) + (nq, -dq)) b0 b3
    (fun x hx => hhH x (hd0 x (by simpa using hx))) hhP h0p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) -
        ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 0 = (np - dp, np + dp) + (nq - dq, nq + dq) by
          ext <;> simp <;> ring] at hx ⊢; exact h3p x hx)
    (by ext <;> simp <;> ring) 0 (by simpa using m0)
  have hs5 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ (2 * dp, 2 * np) 0 ((2 : ℤ) • (np, -dp)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhQ h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) -
        ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - (2 * dp, 2 * np) = (2 : ℤ) • (np - dp, np + dp) - (dq, nq) by
          ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) (2 * dp, 2 * np) (by simpa using n0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at hs3 hs5
  refine ⟨hb0, hb4, ?_, ?_⟩
  · linarith
  · linarith

/-- **The constants of four standard subtiles of an odd alternate tile odometer, `W_1` even.** The subtiles `P^{+,1}`, `P^{-,2}`
at `U`, `B + U + V` (affine factors `0`, `a + b`) of the odd register and `Q^+`, `Q^-` at `0`, `A + 2B + U` (affine factors `0`,
`2a`) of the even register; the half-turn is about `D̂ = A + 2B + 2U + V + 1 - i` with `Ê = 2a + b`. -/
theorem oddPiecesEF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b3 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) =
        dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)),
      2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) +
          ((1 : ℤ), (-1 : ℤ)) - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq))
          ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) -
        2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hN : oH.val 0 = βH)
    (hd0 : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - (dq, nq)) + dotS 0 x + b0)
    (h3p : ∀ x, x - ((np - dp, np + dp) + (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((np - dp, np + dp) + (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b3)
    (h4p : ∀ x, x - 0 ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - 0) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b5) :
    b4 = βH - βQ ∧ b0 = βH - βP ∧
      b3 = -h0 (np - dp, np + dp) - h0 (nq - dq, nq + dq) +
        (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP ∧
      b5 = (2 * dp ^ 2 + 4 * dp * np + 3 * dp * nq - dp - 3 * dq * np - 2 * np ^ 2 - np) + βH - βQ := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, -, -, -, -⟩ := hcP'
  obtain ⟨⟨n0, -⟩, -, -, ⟨nX, -⟩, -, -, -, -⟩ := hcQ'
  obtain ⟨vP0, -, -, -, -, -, -, -⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, -, -, vQX, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  -- the origin piece
  have e0 := h4p 0 (by simpa using n0)
  have hb4 : b4 = βH - βQ := by
    rw [hN, sub_zero, vQ0] at e0
    simp [dotS] at e0
    linarith
  -- the contact of Q^+ and P^{+,1} at U
  have hb0 : b0 = βH - βP := by
    have e1 := h4p (dq, nq) (by simpa using nX)
    have e2 := h0p (dq, nq) (by simpa using m0)
    rw [sub_zero, vQX] at e1
    rw [sub_self, vP0] at e2
    simp [dotS] at e1 e2
    linarith
  -- the half-turn partners
  have hs3 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ (dq, nq) 0 ((np, -dp) + (nq, -dq)) b0 b3
    (fun x hx => hhH x (hd0 x hx)) hhP h0p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) +
        ((1 : ℤ), (-1 : ℤ)) - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - (dq, nq) =
          (np - dp, np + dp) + (dq, nq) + (nq - dq, nq + dq) by ext <;> simp <;> ring] at hx ⊢; exact h3p x hx)
    (by ext <;> simp <;> ring) (dq, nq) (by simpa using m0)
  have hs5 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ 0 0 ((2 : ℤ) • (np, -dp)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhQ h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) +
        ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 0 =
          (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq) by ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) 0 (by simpa using n0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at hs3 hs5
  refine ⟨hb4, hb0, ?_, ?_⟩
  · linarith
  · linarith

/-- **The subtiles `P^{+,2}`, `P^{-,1}` of an odd alternate tile odometer, `W_1` odd**, at `B - U`, `U + V` (affine factors `a`,
`b`), from the contact of `P^{+,2}` with `Q^-` and the half-turn. -/
theorem oddPieces12_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (DH : ℤ × ℤ)
    (hDH : DH = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)))
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val (DH - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) DH - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hd1 : ∀ x, x - ((np - dp, np + dp) - (dq, nq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((np - dp, np + dp) - (dq, nq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((np - dp, np + dp) - (dq, nq))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - ((dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((dq, nq) + (nq - dq, nq + dq))) + dotS (nq, -dq) x + b2)
    (h5p : ∀ x, x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 : ℤ) • (np - dp, np + dp) - (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b5)
    (hb5 : b5 = (2 * dp ^ 2 + 4 * dp * np - dp * nq - dp + dq * np - 2 * np ^ 2 - np) + βH - βQ) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βP ∧
      b2 = -h0 (nq - dq, nq + dq) + (-2 * dp * nq + dq ^ 2 + 2 * dq * np + 2 * dq * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, ⟨mY1, -⟩, -, -, -⟩ := hcP'
  obtain ⟨-, ⟨n1, -⟩, -, -, -, -, -, -⟩ := hcQ'
  obtain ⟨-, -, -, -, vPY1, -, -, -⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, vQ1, -, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z1 : (np - dp, np + dp) - (dq, nq) + ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) - ((np - dp, np + dp) - (dq, nq)) =
      (np - dp, np + dp) + ((1 : ℤ), (0 : ℤ)) := by abel
  have z5 : (np - dp, np + dp) - (dq, nq) + ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) -
      ((2 : ℤ) • (np - dp, np + dp) - (dq, nq)) = ((1 : ℤ), (0 : ℤ)) := by ext <;> simp <;> ring
  have e1 := h1p _ (by rw [z1]; exact mY1)
  have e5 := h5p _ (by rw [z5]; exact n1)
  rw [z1, vPY1] at e1
  rw [z5, vQ1] at e5
  have hb1 : b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βP := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e5
    rw [hb5] at e5
    linarith
  have hs2 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ ((np - dp, np + dp) - (dq, nq)) (np, -dp) (nq, -dq) b1 b2
    (fun x hx => hhH x (hd1 x hx)) hhP h1p
    (by intro x hx; rw [show DH - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - ((np - dp, np + dp) - (dq, nq)) =
        (dq, nq) + (nq - dq, nq + dq) by rw [hDH]; ext <;> simp <;> ring] at hx ⊢; exact h2p x hx)
    (by ext <;> simp <;> ring) ((np - dp, np + dp) - (dq, nq)) (by simpa using m0)
  rw [hDH] at hs2
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hs2
  exact ⟨hb1, by linarith⟩

/-- **The subtiles `P^{+,2}`, `P^{-,1}` of an odd alternate tile odometer, `W_1` even**, at `2U + B`, `V` (affine factors `a`,
`b`), from the contact of `P^{+,2}` with `Q^-` and the half-turn. -/
theorem oddPieces12EF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (DH : ℤ × ℤ)
    (hDH : DH = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) +
      ((1 : ℤ), (-1 : ℤ)))
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) =
        dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val (DH - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) DH - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hd1 : ∀ x, x - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp)) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - ((2 : ℤ) • (dq, nq) + (np - dp, np + dp))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - (nq - dq, nq + dq) ∈ (↑oP.dom : Set (ℤ × ℤ)) →
      oH.val x = oP.val (x - (nq - dq, nq + dq)) + dotS (nq, -dq) x + b2)
    (h5p : ∀ x, x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) →
      oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b5)
    (hb5 : b5 = (2 * dp ^ 2 + 4 * dp * np + 3 * dp * nq - dp - 3 * dq * np - 2 * np ^ 2 - np) + βH - βQ) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βP ∧
      b2 = -h0 (nq - dq, nq + dq) + (dq ^ 2 + 2 * dq * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, -, -, -, ⟨mD1, -⟩⟩ := hcP'
  obtain ⟨-, -, ⟨nXi, -⟩, -, -, -, -, -⟩ := hcQ'
  obtain ⟨-, -, -, -, -, -, -, vPD1⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, -, vQXi, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  set P1 := (2 : ℤ) • (dq, nq) + (np - dp, np + dp) with hP1
  set c1 := (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) with hc1
  have z1 : P1 + c1 - P1 = c1 := by abel
  have z5 : P1 + c1 - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (dq, nq)) = (dq, nq) - ((0 : ℤ), (1 : ℤ)) := by
    rw [hP1, hc1]; ext <;> simp <;> ring
  have e1 := h1p _ (by rw [z1]; exact mD1)
  have e5 := h5p _ (by rw [z5]; exact nXi)
  rw [z1, vPD1] at e1
  rw [z5, vQXi] at e5
  have hb1 : b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βP := by
    simp only [hP1, hc1, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at e1 e5
    rw [hb5] at e5
    linarith
  have hs2 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ P1 (np, -dp) (nq, -dq) b1 b2
    (fun x hx => hhH x (hd1 x hx)) hhP h1p
    (by intro x hx; rw [show DH - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - P1 =
        (nq - dq, nq + dq) by rw [hDH, hP1]; ext <;> simp <;> ring] at hx ⊢; exact h2p x hx)
    (by ext <;> simp <;> ring) P1 (by simpa using m0)
  rw [hDH, hP1] at hs2
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hs2
  exact ⟨hb1, by linarith⟩

/-- The corner points of `StdCornerValues` lie in the domain. -/
theorem corner_mem (o : PartialOdometer) (α : Site) (β : ℤ) (X Y e : Site) (h : TileTranslation.StdCornerValues o α β X Y e) :
    (0 : Site) ∈ (↑o.dom : Set Site) ∧ ((1 : ℤ), (0 : ℤ)) ∈ (↑o.dom : Set Site) ∧ X - ((0 : ℤ), (1 : ℤ)) ∈ (↑o.dom : Set Site) ∧
      X ∈ (↑o.dom : Set Site) ∧ Y + ((1 : ℤ), (0 : ℤ)) ∈ (↑o.dom : Set Site) ∧ Y + ((1 : ℤ), (-1 : ℤ)) ∈ (↑o.dom : Set Site) ∧
      X + Y + ((1 : ℤ), (-1 : ℤ)) ∈ (↑o.dom : Set Site) ∧
      X + Y + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) ∈ (↑o.dom : Set Site) := by
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩, ⟨h4, -⟩, ⟨h5, -⟩, ⟨h6, -⟩, ⟨h7, -⟩, ⟨h8, -⟩⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end FLatticePaper.Tiles.AltParentEven
