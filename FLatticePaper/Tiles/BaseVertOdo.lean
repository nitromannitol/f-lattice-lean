import FLatticePaper.Tiles.VerticalFamily
import FLatticePaper.Tiles.ZeroOneGeneral

/-! # Closed forms of the reversed vertical family on the word `q p^m`

For a letter sequence `ℓ` with `ℓ 0 = q` and `ℓ (i+1) = p` for all `i` (the reversed vertical word of the odd `3^k` child is
`q p^(2k+1)`), the affine factor of `vtM` is `(1, -j)` for `j ≥ 1`, the position of the `j`-th tile is `(-(j-1), j)`, and the
centred constant satisfies `2 vtCM j = -j(j+1)` for `j ≥ 1`. These are the inputs of the per-tile identities of
`BaseVertPilot`. -/

namespace FLatticePaper.Tiles.BaseVertOdo

open FLatticePaper.Tiles

/-- The count of `q` before position `j+1` is `1` when `ℓ` is `q p p p ...`. -/
theorem vtCnt_succ_one (ℓ : ℕ → Letter) (h0 : ℓ 0 = Letter.q) (hs : ∀ i, ℓ (i + 1) = Letter.p) :
    ∀ j : ℕ, vtCnt ℓ (j + 1) = 1 := by
  intro j
  induction j with
  | zero => simp [vtCnt, h0]
  | succ n ih =>
    rw [show vtCnt ℓ (n + 1 + 1) = vtCnt ℓ (n + 1) + (if ℓ (n + 1) = Letter.q then 1 else 0) from rfl, ih,
      hs n]
    simp

/-- The lower-left positions of the reversed vertical string of `q p p p ...`: `posF (j+1) = (-j, j+1)`. -/
theorem posF_vert_succ (ℓ : ℕ → Letter) (h0 : ℓ 0 = Letter.q) (hs : ∀ i, ℓ (i + 1) = Letter.p) :
    ∀ j : ℕ, posF .vertical true ℓ (j + 1) = (-(j : ℤ), (j : ℤ) + 1) := by
  intro j
  induction j with
  | zero =>
    have hs0 : ℓ 1 = Letter.p := hs 0
    simp [posF, stepOf, zeroOneVerticalReversedStep, h0, hs0]
  | succ n ih =>
    rw [show posF .vertical true ℓ (n + 1 + 1) = posF .vertical true ℓ (n + 1)
      + stepOf .vertical true (ℓ (n + 1)) (ℓ (n + 1 + 1)) from rfl, ih]
    simp only [stepOf, zeroOneVerticalReversedStep, hs n, hs (n + 1)]
    ext
    all_goals simp
    all_goals ring

/-- The centred constant of the reversed family on `q p p p ...`: `2 vtCM (j+1) = -(j+1)(j+2)`. -/
theorem vtCM_closed (ℓ : ℕ → Letter) (h0 : ℓ 0 = Letter.q) (hs : ∀ i, ℓ (i + 1) = Letter.p) :
    ∀ j : ℕ, 2 * vtCM ℓ (j + 1) = -(((j : ℤ) + 1) * ((j : ℤ) + 2)) := by
  intro j
  induction j with
  | zero =>
    have hs0 : ℓ 1 = Letter.p := hs 0
    simp [vtCM, vtAff, vtCnt, vtBetaM, ptDot, zeroOneVerticalReversedStep, h0, hs0]
  | succ n ih =>
    have h1 : vtCM ℓ (n + 1 + 1) = vtCM ℓ (n + 1) + vtBetaM (ℓ (n + 1)) (ℓ (n + 1 + 1))
        + ptDot (vtAff ℓ (n + 1)) (zeroOneVerticalReversedStep (ℓ (n + 1)) (ℓ (n + 1 + 1))) := by
      simp only [vtCM]
    have h2 := vtCnt_succ_one ℓ h0 hs n
    rw [h1, hs n, hs (n + 1)]
    simp only [vtBetaM, zeroOneVerticalReversedStep, vtAff, ptDot, h2]
    push_cast
    linarith

/-- The letters of `replicate m p ++ [q]` read backwards: `q` first, then `p` forever. -/
theorem lettersOf_rev_lv (m : ℕ) :
    lettersOf (List.replicate m Letter.p ++ [Letter.q]) true 0 = Letter.q ∧
      ∀ i : ℕ, lettersOf (List.replicate m Letter.p ++ [Letter.q]) true (i + 1) = Letter.p := by
  constructor
  · simp [lettersOf, List.reverse_append]
  · intro i
    simp [lettersOf, List.reverse_append, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp

end FLatticePaper.Tiles.BaseVertOdo
