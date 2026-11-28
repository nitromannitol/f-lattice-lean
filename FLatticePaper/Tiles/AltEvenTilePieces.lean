import FLatticePaper.Tiles.AltParentEven

/-! # The constants of the standard subtiles of an even alternate tile odometer

The parent piece of the odd alternate child is an even alternate tile odometer one level up (`tileAltOddPieces`, entry `6`). On
its six standard subtiles (the decomposition of `tileAltEvenPieces`, copies of the even register at `Q^{+,1}, Q^{+,2}, Q^{-,1},
Q^{-,2}` and of the odd register at `P^+, P^-`) it equals the placed register odometers plus constants. With the normalisation at
the origin these constants are explicit: two of them from the origin piece and a corner contact, one more from a second corner
contact, and the other three from the half-turn of the tile (`AltParentConstants.sigma_pair`). They are the constants `kEvenEF`,
`kEvenOF` of the six copies at the level of the tile. -/

namespace FLatticePaper.Tiles.AltEvenTilePieces

open FLatticePaper.Tiles FLatticePaper.Tiles.AltParentConstants FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointFamily (h0)

/-- **The constants of the six standard subtiles of an even alternate tile odometer, `W_1` even.** The even register `Q` at
`0, ((np - dp, np + dp) - (dq, nq)), ((2 * dp, 2 * np) + (np - dp, np + dp)), ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq))` and the odd register `P` at `(dq, nq), ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq))`, affine factors `0, a, a, 2a, 0, a + b`; the half-turn is
about `D̂ = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))` with `Ê = 2a + b`. From the origin piece, two corner contacts and the half-turn. -/
theorem evenPiecesEF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b1 b2 b3 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) = dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) = dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hN : oH.val 0 = βH)
    (hd0 : ∀ x, x - 0 ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - 0 ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - 0) + dotS 0 x + b0)
    (h1p : ∀ x, x - ((np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((np - dp, np + dp) - (dq, nq))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (np - dp, np + dp))) + dotS (np, -dp) x + b2)
    (h3p : ∀ x, x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b3)
    (h4p : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - (dq, nq)) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b5) :
    b0 = βH - βQ ∧
      b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ ∧
      b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ ∧
      b3 = (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) + βH - βQ ∧
      b4 = βH - βP ∧
      b5 = -h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, -, -, -, ⟨mD1, -⟩⟩ := hcP'
  obtain ⟨⟨n0, -⟩, -, ⟨nXi, -⟩, ⟨nX, -⟩, -, -, -, -⟩ := hcQ'
  obtain ⟨vP0, -, -, -, -, -, -, vPD1⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, -, vQXi, vQX, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  -- the origin piece `Q^{+,1}`
  have e0 := h0p 0 (by simpa using n0)
  rw [hN, sub_zero, vQ0] at e0
  have hb0 : b0 = βH - βQ := by simp [dotS] at e0; linarith
  -- the contact of `Q^{+,1}` and `P^+` at `U`
  have e1 := h0p (dq, nq) (by simpa using nX)
  have e2 := h4p (dq, nq) (by simpa using m0)
  rw [sub_zero, vQX] at e1
  rw [sub_self, vP0] at e2
  have hb4 : b4 = βH - βP := by simp [dotS] at e1 e2; linarith
  -- the contact of `Q^{-,1}` and `P^+` at `A + B + U - i`
  have z3 : (2 * dp, 2 * np) + (np - dp, np + dp) + ((dq, nq) - ((0 : ℤ), (1 : ℤ))) - ((2 * dp, 2 * np) + (np - dp, np + dp)) =
      (dq, nq) - ((0 : ℤ), (1 : ℤ)) := by abel
  have z4 : (2 * dp, 2 * np) + (np - dp, np + dp) + ((dq, nq) - ((0 : ℤ), (1 : ℤ))) - (dq, nq) =
      (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by ext <;> simp; ring
  have e3 := h2p _ (by rw [z3]; exact nXi)
  have e4 := h4p _ (by rw [z4]; exact mD1)
  rw [z3, vQXi] at e3
  rw [z4, vPD1] at e4
  have hb2 : b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at e3 e4
    linarith
  -- the half-turn partners
  have hs3 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ 0 0 ((2 : ℤ) • (np, -dp)) b0 b3
    (fun x hx => hhH x (hd0 x hx)) hhQ h0p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 0 = ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq)) by ext <;> simp; ring] at hx ⊢; exact h3p x hx)
    (by ext <;> simp <;> ring) 0 (by simpa using n0)
  have hs1 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ ((2 * dp, 2 * np) + (np - dp, np + dp)) (np, -dp) (np, -dp) b2 b1
    (fun x hx => hhH x (hd2 x hx)) hhQ h2p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((2 * dp, 2 * np) + (np - dp, np + dp)) = ((np - dp, np + dp) - (dq, nq)) by ext <;> simp <;> ring] at hx ⊢; exact h1p x hx)
    (by ext <;> simp <;> ring) ((2 * dp, 2 * np) + (np - dp, np + dp)) (by simpa using n0)
  have hs5 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ (dq, nq) 0 ((np, -dp) + (nq, -dq)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhP h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - (dq, nq) = ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) by ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) (dq, nq) (by simpa using m0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hs3 hs1 hs5
  refine ⟨hb0, ?_, hb2, ?_, hb4, ?_⟩ <;> linarith

/-- **The constants of the six standard subtiles of an even alternate tile odometer, `W_1` odd.** The even register `Q` at
`(2 * dp, 2 * np), ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)), (np - dp, np + dp), ((2 : ℤ) • (np - dp, np + dp) + (dq, nq))` and the odd register `P` at `0, ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq))`, affine factors `0, a, a, 2a, 0, a + b`; the half-turn is
about `D̂ = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))` with `Ê = 2a + b`. From the origin piece, two corner contacts and the half-turn. -/
theorem evenPieces_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b0 b1 b2 b3 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) = dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) = dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hN : oH.val 0 = βH)
    (hd0 : ∀ x, x - (2 * dp, 2 * np) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd2 : ∀ x, x - (np - dp, np + dp) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h0p : ∀ x, x - (2 * dp, 2 * np) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - (2 * dp, 2 * np)) + dotS 0 x + b0)
    (h1p : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - (np - dp, np + dp) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - (np - dp, np + dp)) + dotS (np, -dp) x + b2)
    (h3p : ∀ x, x - ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 : ℤ) • (np - dp, np + dp) + (dq, nq))) + dotS ((2 : ℤ) • (np, -dp)) x + b3)
    (h4p : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - 0) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b5) :
    b0 = βH - βQ ∧
      b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ ∧
      b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ ∧
      b3 = (2 * dp ^ 2 + 4 * dp * np + dp * nq - dp - dq * np - 2 * np ^ 2 - np) + βH - βQ ∧
      b4 = βH - βP ∧
      b5 = -h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, ⟨mX, -⟩, ⟨mY1, -⟩, -, -, -⟩ := hcP'
  obtain ⟨⟨n0, -⟩, ⟨n1, -⟩, -, -, -, -, -, -⟩ := hcQ'
  obtain ⟨vP0, -, -, vPX, vPY1, -, -, -⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨vQ0, vQ1, -, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  -- the origin piece `P^+`
  have e0 := h4p 0 (by simpa using m0)
  rw [hN, sub_zero, vP0] at e0
  have hb4 : b4 = βH - βP := by simp [dotS] at e0; linarith
  -- the contact of `Q^{+,1}` and `P^+` at `A`
  have e1 := h0p (2 * dp, 2 * np) (by simpa using n0)
  have e2 := h4p (2 * dp, 2 * np) (by simpa using mX)
  rw [sub_self, vQ0] at e1
  rw [sub_zero, vPX] at e2
  have hb0 : b0 = βH - βQ := by simp [dotS] at e1 e2; linarith
  -- the contact of `Q^{-,1}` and `P^+` at `B + 1`
  have z3 : (np - dp, np + dp) + ((1 : ℤ), (0 : ℤ)) - (np - dp, np + dp) = ((1 : ℤ), (0 : ℤ)) := by abel
  have e3 := h2p _ (by rw [z3]; exact n1)
  have e4 := h4p ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) (by simpa using mY1)
  rw [z3, vQ1] at e3
  rw [sub_zero, vPY1] at e4
  have hb2 : b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e3 e4
    linarith
  -- the half-turn partners
  have hs3 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ (2 * dp, 2 * np) 0 ((2 : ℤ) • (np, -dp)) b0 b3
    (fun x hx => hhH x (hd0 x hx)) hhQ h0p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - (2 * dp, 2 * np) = ((2 : ℤ) • (np - dp, np + dp) + (dq, nq)) by ext <;> simp <;> ring] at hx ⊢; exact h3p x hx)
    (by ext <;> simp <;> ring) (2 * dp, 2 * np) (by simpa using n0)
  have hs1 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ (np - dp, np + dp) (np, -dp) (np, -dp) b2 b1
    (fun x hx => hhH x (hd2 x hx)) hhQ h2p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - (np - dp, np + dp) = ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)) by ext <;> simp <;> ring] at hx ⊢; exact h1p x hx)
    (by ext <;> simp <;> ring) (np - dp, np + dp) (by simpa using n0)
  have hs5 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ 0 0 ((np, -dp) + (nq, -dq)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhP h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 0 = ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) by ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) 0 (by simpa using m0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hs3 hs1 hs5
  refine ⟨hb0, ?_, hb2, ?_, hb4, ?_⟩ <;> linarith

/-- **The constants of the subtiles `1, 2, 4, 5` of an even alternate tile odometer, `W_1` even.** The even register `Q` at
`0, ((np - dp, np + dp) - (dq, nq)), ((2 * dp, 2 * np) + (np - dp, np + dp)), ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) - (dq, nq))` and the odd register `P` at `(dq, nq), ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq))`, affine factors `0, a, a, 2a, 0, a + b`; the half-turn is
about `D̂ = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))` with `Ê = 2a + b`. From the origin piece, two corner contacts and the half-turn. -/
theorem evenPieces1245EF_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) = dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) = dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hd2 : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((np - dp, np + dp) - (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((np - dp, np + dp) - (dq, nq))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (np - dp, np + dp))) + dotS (np, -dp) x + b2)
    (h4p : ∀ x, x - (dq, nq) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - (dq, nq)) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b5)
    (hb4 : b4 = βH - βP) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ ∧ b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ ∧
      b5 = -h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dp * nq + dq ^ 2 + dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, -, -, -, ⟨mD1, -⟩⟩ := hcP'
  obtain ⟨⟨n0, -⟩, -, ⟨nXi, -⟩, -, -, -, -, -⟩ := hcQ'
  obtain ⟨-, -, -, -, -, -, -, vPD1⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, -, vQXi, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z3 : (2 * dp, 2 * np) + (np - dp, np + dp) + ((dq, nq) - ((0 : ℤ), (1 : ℤ))) - ((2 * dp, 2 * np) + (np - dp, np + dp)) =
      (dq, nq) - ((0 : ℤ), (1 : ℤ)) := by abel
  have z4 : (2 * dp, 2 * np) + (np - dp, np + dp) + ((dq, nq) - ((0 : ℤ), (1 : ℤ))) - (dq, nq) =
      (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) := by ext <;> simp; ring
  have e3 := h2p _ (by rw [z3]; exact nXi)
  have e4 := h4p _ (by rw [z4]; exact mD1)
  rw [z3, vQXi] at e3
  rw [z4, vPD1] at e4
  have hb2 : b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at e3 e4
    linarith
  have hs1 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ ((2 * dp, 2 * np) + (np - dp, np + dp)) (np, -dp) (np, -dp) b2 b1
    (fun x hx => hhH x (hd2 x hx)) hhQ h2p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - ((2 * dp, 2 * np) + (np - dp, np + dp)) = ((np - dp, np + dp) - (dq, nq)) by ext <;> simp <;> ring] at hx ⊢; exact h1p x hx)
    (by ext <;> simp <;> ring) ((2 * dp, 2 * np) + (np - dp, np + dp)) (by simpa using n0)
  have hs5 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ (dq, nq) 0 ((np, -dp) + (nq, -dq)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhP h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - (dq, nq) = ((np - dp, np + dp) - (dq, nq) + (nq - dq, nq + dq)) by ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) (dq, nq) (by simpa using m0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hs1 hs5
  refine ⟨?_, hb2, ?_⟩ <;> linarith

/-- **The constants of the subtiles `1, 2, 4, 5` of an even alternate tile odometer, `W_1` odd.** The even register `Q` at
`(2 * dp, 2 * np), ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)), (np - dp, np + dp), ((2 : ℤ) • (np - dp, np + dp) + (dq, nq))` and the odd register `P` at `0, ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq))`, affine factors `0, a, a, 2a, 0, a + b`; the half-turn is
about `D̂ = (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))` with `Ê = 2a + b`. From the origin piece, two corner contacts and the half-turn. -/
theorem evenPieces1245_of (np dp nq dq : ℤ) (hpar : (np + dp) % 2 = 1) (hqe : (nq + dq) % 2 = 0)
    (oH oP oQ : PartialOdometer) (βH βP βQ b1 b2 b4 b5 : ℤ)
    (hcP : TileTranslation.StdCornerValues oP 0 βP (2 * dp, 2 * np) (np - dp, np + dp) (np, -dp))
    (hcQ : TileTranslation.StdCornerValues oQ 0 βQ (dq, nq) (nq - dq, nq + dq) (nq, -dq))
    (hhP : ∀ y ∈ (↑oP.dom : Set (ℤ × ℤ)), (2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oP.dom : Set _) ∧
      2 * (oP.val ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ)) - y) - oP.val y) = dotS (np, -dp) ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (np, -dp) y)
    (hhQ : ∀ y ∈ (↑oQ.dom : Set (ℤ × ℤ)), (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y ∈ (↑oQ.dom : Set _) ∧
      2 * (oQ.val ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - y) - oQ.val y) = dotS (nq, -dq) ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS (nq, -dq) y)
    (hhH : ∀ x ∈ (↑oH.dom : Set (ℤ × ℤ)), 2 * (oH.val ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - x) - oH.val x) =
      dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) ((2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS ((2 : ℤ) • (np, -dp) + (nq, -dq)) x)
    (hd2 : ∀ x, x - (np - dp, np + dp) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (hd4 : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) → x ∈ (↑oH.dom : Set (ℤ × ℤ)))
    (h1p : ∀ x, x - ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq))) + dotS (np, -dp) x + b1)
    (h2p : ∀ x, x - (np - dp, np + dp) ∈ (↑oQ.dom : Set (ℤ × ℤ)) → oH.val x = oQ.val (x - (np - dp, np + dp)) + dotS (np, -dp) x + b2)
    (h4p : ∀ x, x - 0 ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - 0) + dotS 0 x + b4)
    (h5p : ∀ x, x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) ∈ (↑oP.dom : Set (ℤ × ℤ)) → oH.val x = oP.val (x - ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq))) + dotS ((np, -dp) + (nq, -dq)) x + b5)
    (hb4 : b4 = βH - βP) :
    b1 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np + dp * nq - dq * np - np ^ 2) + βH - βQ ∧ b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ ∧
      b5 = -h0 (np - dp, np + dp) -h0 (nq - dq, nq + dq) + (dp ^ 2 + dp * dq + 2 * dp * np + dq ^ 2 + 2 * dq * np + 2 * dq * nq - np ^ 2 - np * nq - nq ^ 2) + βH - βP := by
  have hcP' := hcP
  have hcQ' := hcQ
  obtain ⟨⟨m0, -⟩, -, -, -, ⟨mY1, -⟩, -, -, -⟩ := hcP'
  obtain ⟨⟨n0, -⟩, ⟨n1, -⟩, -, -, -, -, -, -⟩ := hcQ'
  obtain ⟨-, -, -, -, vPY1, -, -, -⟩ := corner_raw oP βP _ _ _ hcP
  obtain ⟨-, vQ1, -, -, -, -, -, -⟩ := corner_raw oQ βQ _ _ _ hcQ
  have hB4 := h0_even (np - dp, np + dp) (by simp only; omega)
  have hV4 := h0_even (nq - dq, nq + dq) (by simp only; omega)
  have z3 : (np - dp, np + dp) + ((1 : ℤ), (0 : ℤ)) - (np - dp, np + dp) = ((1 : ℤ), (0 : ℤ)) := by abel
  have e3 := h2p _ (by rw [z3]; exact n1)
  have e4 := h4p ((np - dp, np + dp) + ((1 : ℤ), (0 : ℤ))) (by simpa using mY1)
  rw [z3, vQ1] at e3
  rw [sub_zero, vPY1] at e4
  have hb2 : b2 = -h0 (np - dp, np + dp) + (dp ^ 2 + 2 * dp * np - np ^ 2) + βH - βQ := by
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e3 e4
    linarith
  have hs1 := sigma_pair oH.val oQ.val (↑oQ.dom) _ _ _ _ (np - dp, np + dp) (np, -dp) (np, -dp) b2 b1
    (fun x hx => hhH x (hd2 x hx)) hhQ h2p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ))) - (np - dp, np + dp) = ((2 * dp, 2 * np) + (np - dp, np + dp) + (dq, nq)) by ext <;> simp <;> ring] at hx ⊢; exact h1p x hx)
    (by ext <;> simp <;> ring) (np - dp, np + dp) (by simpa using n0)
  have hs5 := sigma_pair oH.val oP.val (↑oP.dom) _ _ _ _ 0 0 ((np, -dp) + (nq, -dq)) b4 b5
    (fun x hx => hhH x (hd4 x hx)) hhP h4p
    (by intro x hx; rw [show (2 * dp, 2 * np) + (2 : ℤ) • (np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq) + ((1 : ℤ), (-1 : ℤ)) - ((2 * dp, 2 * np) + (np - dp, np + dp) + ((1 : ℤ), (-1 : ℤ))) - 0 = ((np - dp, np + dp) + (2 : ℤ) • (dq, nq) + (nq - dq, nq + dq)) by ext <;> simp <;> ring] at hx ⊢; exact h5p x hx)
    (by ext <;> simp <;> ring) 0 (by simpa using m0)
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hs1 hs5
  refine ⟨?_, hb2, ?_⟩ <;> linarith

end FLatticePaper.Tiles.AltEvenTilePieces
