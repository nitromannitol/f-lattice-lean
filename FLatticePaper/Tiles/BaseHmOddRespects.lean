import FLatticePaper.Tiles.BaseHmOddLast
import FLatticePaper.Tiles.HorizontalEnlarged
import FLatticePaper.Tiles.RevStringList

/-! # The explicit reversed family of the odd `3^k` piece and its respect

The family `HmOddF k` has tile list `posHm k` with the enlarged types of the reversed word, affine factors `aHm k` and constants
`cHm k - ptDot (aHm k) (posHm k)`. Its respect is `PTFamily.respects_of_triples` exactly as in `HME_respects`, with the closed
forms: `posHm_succ` (the positions), `aHm` (the factors, letter-determined up to the shift), `cHm_succ` (the constants, `β = 0`). -/

namespace FLatticePaper.Tiles.BaseHmOddRespects

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BaseHmOdd FLatticePaper.Construction
open FLatticePaper.Tiles.BaseHmOddValues FLatticePaper.Tiles.BaseTileProps
open FLatticePaper.Tiles.BaseHpLadder (wL)

/-- The explicit reversed family of the odd `3^k` piece. -/
def HmOddF (k : ℕ) : PTFamily :=
  { ts := (List.range (2 * k + 3)).map (fun j => (hTileAt (lettersOf (wL k) true) j, posHm k j)),
    a := fun j => aHm k j,
    b := fun j => cHm k j - ptDot (aHm k j) (posHm k j) }

theorem HmOddF_n (k : ℕ) : (HmOddF k).n = 2 * k + 3 := by
  simp [HmOddF, PTFamily.n]

theorem HmOddF_tile (k j : ℕ) (hj : j < 2 * k + 3) :
    (HmOddF k).tile j = (hTileAt (lettersOf (wL k) true) j, posHm k j) := by
  unfold PTFamily.tile HmOddF
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem HmOddF_respects (k : ℕ) (hk : 1 ≤ k) :
    (HmOddF k).Respects .horizontal true :=
  PTFamily.respects_of_triples (HmOddF k) .horizontal true (lettersOf (wL k) true) (hPrev (lettersOf (wL k) true))
    (fun j => posHm k j) hTt
    (fun y z => zeroOneHorizontalReversedStep y z) (fun _ y z => alphaH z - alphaH y)
    (fun j => cHm k j) (fun _ _ _ => (0 : ℤ)) (fun _ _ _ => True)
    (fun j hj => by
      rw [HmOddF_n] at hj
      rw [HmOddF_tile k j hj]
      rfl)
    (fun j _ => hPrev_succ _ j)
    (fun j hj => by
      rw [HmOddF_n] at hj
      exact posHm_succ k j hk (by omega))
    (fun j hj => by
      rw [HmOddF_n] at hj
      show aHm k (j + 1) = aHm k j + (alphaH (lettersOf (wL k) true (j + 1)) - alphaH (lettersOf (wL k) true j))
      unfold aHm
      abel)
    (fun j _ => rfl)
    (fun j hj => by
      rw [HmOddF_n] at hj
      show cHm k (j + 1) = cHm k j + (0 : ℤ) +
        ptDot (aHm k j) (zeroOneHorizontalReversedStep (lettersOf (wL k) true j) (lettersOf (wL k) true (j + 1)))
      rw [cHm_succ k j hk (by omega)]
      ring)
    (fun _ _ => trivial)
    (fun x y => hTt_letter x y)
    (fun x y z _ => by
      cases y <;> cases z <;> simp [hTt_base_p, hTt_base_q, surgicalSlopeDiff, alphaH, Prod.ext_iff] <;> norm_num)
    (fun _ x y z _ u hu v hv hno hunit => hE_rev x y z u hu v hv hno hunit)
    (fun h => by cases h)

end FLatticePaper.Tiles.BaseHmOddRespects
