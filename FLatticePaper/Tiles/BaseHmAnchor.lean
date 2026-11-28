import FLatticePaper.Tiles.BaseVertPiece
import FLatticePaper.Tiles.BaseCasePseudoSquares
import FLatticePaper.Tiles.BaseHmOdd
import FLatticePaper.Tiles.VerticalRevBridge

/-! # The anchor of the reversed horizontal piece of the odd `3^k` odometer

The anchor of `Hm` in `RespectsAnchored` is `lastPosOf (vRevStringAt wv.reverse (0,0))`. For the odd `3^k` word, `wv.reverse` is
`q p^{2k+1}`, and the reversed vertical string of `q p^m` has last point `(1-m, m)` (each `p` step is `(-1,1)`). With `m = 2k+1`
this is `(-2k, 2k+1)`, which is the first point of `posHm k` (the start of the reversed horizontal string). -/

namespace FLatticePaper.Tiles.BaseHmAnchor

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.VerticalRevBridge

theorem lastPosOf_cons_of_ne (a : ZTile × GInt) (l : List (ZTile × GInt)) (hl : l ≠ []) :
    lastPosOf (a :: l) = lastPosOf l := by
  unfold lastPosOf
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [List.getLast?_cons_cons]

/-- The last point of the reversed vertical string of `p^{m+1}` from `c`: `c + (-m, m)`. -/
theorem lastPos_vRev_p_rep (m : ℕ) (c : GInt) :
    lastPosOf (vRevStringAt (Letter.p :: List.replicate m Letter.p) c) = c + (-(m : ℤ), (m : ℤ)) := by
  induction m generalizing c with
  | zero =>
    simp only [List.replicate_zero]
    rw [vRevStringAt_single_p]
    simp [lastPosOf]
  | succ m ih =>
    rw [List.replicate_succ, vRevStringAt_cons Letter.p Letter.p (List.replicate m Letter.p) c]
    have hne : vRevStringAt (Letter.p :: List.replicate m Letter.p) (c + vRevOffset Letter.p Letter.p) ≠ [] := by
      simp [vRevStringAt]
    rw [lastPosOf_cons_of_ne _ _ hne, ih]
    simp [vRevOffset]
    ext <;> simp <;> ring

/-- The last point of the reversed vertical string of `q p^m` (for `m ≥ 1`) from `c`: `c + (1-m, m)`. -/
theorem lastPos_vRev_q_rep (m : ℕ) (hm : 1 ≤ m) (c : GInt) :
    lastPosOf (vRevStringAt (Letter.q :: List.replicate m Letter.p) c) = c + (1 - (m : ℤ), (m : ℤ)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.replicate_succ, vRevStringAt_cons2 Letter.q Letter.p (List.replicate m' Letter.p) c]
  have hne : vRevStringAt (Letter.p :: List.replicate m' Letter.p) (c + vRevOffset Letter.q Letter.p) ≠ [] := by
    simp [vRevStringAt]
  rw [lastPosOf_cons_of_ne _ _ hne]
  rw [show Letter.p :: List.replicate m' Letter.p = Letter.p :: List.replicate m' Letter.p from rfl]
  rw [lastPos_vRev_p_rep m' (c + vRevOffset Letter.q Letter.p)]
  simp [vRevOffset]
  ext <;> (simp; try ring)

/-- The anchor of the reversed horizontal piece of the odd `3^k` odometer, `k ≥ 1`. -/
theorem anchor_hm_odd (k : ℕ) (hk : 1 ≤ k) :
    lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.three) false).reverse (0, 0)) = posHm k 0 := by
  rw [BaseVertPiece.vWordOf_three_false]
  have hrev : (List.replicate (2 * k + 1) Letter.p ++ [Letter.q]).reverse
      = Letter.q :: List.replicate (2 * k + 1) Letter.p := by
    simp [List.reverse_append]
  rw [hrev, lastPos_vRev_q_rep (2 * k + 1) (by omega)]
  simp [posHm]

end FLatticePaper.Tiles.BaseHmAnchor
