import FLatticePaper.Tiles.BaseHmTwoOdd
import FLatticePaper.Tiles.BaseTwoOdd
import FLatticePaper.Tiles.BaseHmAnchor

/-! # The anchor of the reversed horizontal piece of the odd `2^k` odometer

The vertical word of the odd child of `2^k` is `p q^{k+1}` (`BaseTwoOdd.wv_two`), so its reverse is `q^{k+1} p`. The reversed
vertical string of `q^{n+1} p` from `c` has last point `c + (0, 2n+1)`: each `qq` step is `(0,2)` and the last `qp` step is
`(0,1)`. With `n = k` this is `(0, 2k+1)`, which is `posH2 k 0`, the anchor of the reversed horizontal piece. -/

namespace FLatticePaper.Tiles.BaseHmTwoAnchor

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.VerticalRevBridge
open FLatticePaper.Tiles.BaseHmAnchor FLatticePaper.Tiles.BaseHmTwoOdd

/-- The last point of the reversed vertical string of `q^{n+1} p` from `c`: `c + (0, 2n+1)`. -/
theorem lastPos_vRev_qq_p (n : ℕ) (c : GInt) :
    lastPosOf (vRevStringAt (List.replicate (n + 1) Letter.q ++ [Letter.p]) c) = c + (0, 2 * (n : ℤ) + 1) := by
  induction n generalizing c with
  | zero =>
    show lastPosOf (vRevStringAt [Letter.q, Letter.p] c) = _
    rw [vRevStringAt_cons2, vRevStringAt_single_p]
    simp [lastPosOf, vRevOffset]
  | succ n ih =>
    have h1 : List.replicate (n + 1 + 1) Letter.q ++ [Letter.p] =
        Letter.q :: Letter.q :: (List.replicate n Letter.q ++ [Letter.p]) := by
      simp [List.replicate_succ]
    have h2 : Letter.q :: (List.replicate n Letter.q ++ [Letter.p]) =
        List.replicate (n + 1) Letter.q ++ [Letter.p] := by
      simp [List.replicate_succ]
    rw [h1, vRevStringAt_cons2 Letter.q Letter.q, h2]
    have hne : vRevStringAt (List.replicate (n + 1) Letter.q ++ [Letter.p]) (c + vRevOffset Letter.q Letter.q) ≠ [] := by
      simp [vRevStringAt]
    rw [lastPosOf_cons_of_ne _ _ hne, ih]
    ext <;> (simp [vRevOffset]; try ring)

/-- The anchor of the reversed horizontal piece of the odd `2^k` odometer: `lastPosOf` of the reversed vertical string of
`vWordOf (2^k) false` is `posH2 k 0 = (0, 2k+1)`. -/
theorem anchor_hm_two (k : ℕ) :
    lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.two) false).reverse (0, 0)) = posH2 k 0 := by
  rw [BaseTwoOdd.wv_two]
  simp only [BaseTwoOdd.W2]
  have hrev : (Letter.p :: List.replicate (k + 1) Letter.q).reverse =
      List.replicate (k + 1) Letter.q ++ [Letter.p] := by
    simp [List.reverse_cons]
  rw [hrev, lastPos_vRev_qq_p k]
  simp [posH2]

end FLatticePaper.Tiles.BaseHmTwoAnchor
