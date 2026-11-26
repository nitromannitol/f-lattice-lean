import FLatticePaper.Plane.Induction.FaceSign
import FLatticePaper.Plane.Induction.CollarBottomSquare
import FLatticePaper.Plane.Induction.CollarLeft
import FLatticePaper.Plane.Induction.CollarRight
import FLatticePaper.Plane.Induction.StripColours

/-! # The per-face strictness of the row squares (the arithmetic of `RowFaceStrictHyp`)

The six face rows of `FaceRows` / `FaceRowsForced` use, per face, one square of the collar centre `c` (in physical coordinates):

* bottom: `squareCorners (c.1 − 1) c.2` (the centre is its lower-right corner), by `bottom_square_strict`;
* aligned left (`ε = 1`): `squareCorners c.1 c.2` (the centre is its lower-left corner), by `left_square_strict`;
* aligned right (`ε = −1`): `squareCorners (c.1 − 1) (c.2 − 1)` (the centre is its upper-right corner), by `right_square_strict`.

The band lemmas need: the bottom centre is not `(1,1)`; a left (right) centre is neither bottom nor top. Two field facts supply these
for a white centre with `Ψ ≥ 0` (named premises, numerically checked on words of length at most 3):

* the laplacian of `MW` at `(1,1)` is `−1`, now from the strips of the word's frame (`StripColours.lap_one_one` with the input `HasStrips (MW word)`; the point `(1,1)` is strict and bottom but black);
* `SingleFaceSign`: a white strict collar centre with `Ψ ≥ 0` has at most one face witness. -/

namespace FLatticePaper.FaceSquares

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1NonfreeOut FLatticePaper.FaceWitness
  FLatticePaper.CollarSquare FLatticePaper.W1CollarFrame FLatticePaper.CollarChain FLatticePaper.FaceSign
  FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.ChainWire

/-- **The bottom face square** (`squareCorners (c.1 − 1) c.2`), strict when the centre is strict, not `(1,1)`, and on the bottom arc. -/
theorem bottom_face_strict {word : Word} {c : Site}
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hne : c ≠ (1, 1)) (hB : BottomWit (frameAt word) c) :
    ∀ c' ∈ squareCorners (c.1 - 1) c.2,
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c' :=
  FLatticePaper.CollarBottomSquare.bottom_square_strict (frameAt word) hcS hne hB

/-- **The aligned left square** (`squareCorners c.1 c.2`), strict when the centre is strict and on the left arc only. -/
theorem left_face_strict {word : Word} {c : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hL : LeftWit (frameAt word) c) :
    ∀ c' ∈ squareCorners c.1 c.2,
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c' :=
  FLatticePaper.CollarLeft.left_square_strict (frameAt word) hn3 hcS hB hT hL

/-- **The aligned right square** (`squareCorners (c.1 − 1) (c.2 − 1)`), strict when the centre is strict and on the right arc only. -/
theorem right_face_strict {word : Word} {c : Site} (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hR : RightWit (frameAt word) c) :
    ∀ c' ∈ squareCorners (c.1 - 1) (c.2 - 1),
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c' :=
  FLatticePaper.CollarRight.right_square_strict (frameAt word) hn3 hcS hB hT hR

/-- **The single-face fact** (named premise): a white strict collar centre with `Ψ ≥ 0` is on at most one of the four faces. -/
def SingleFaceSign (word : Word) : Prop :=
  ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c →
    ¬ (BottomWit (frameAt word) c ∧ LeftWit (frameAt word) c) ∧
    ¬ (BottomWit (frameAt word) c ∧ RightWit (frameAt word) c) ∧
    ¬ (BottomWit (frameAt word) c ∧ TopWit (frameAt word) c) ∧
    ¬ (LeftWit (frameAt word) c ∧ RightWit (frameAt word) c) ∧
    ¬ (LeftWit (frameAt word) c ∧ TopWit (frameAt word) c) ∧
    ¬ (RightWit (frameAt word) c ∧ TopWit (frameAt word) c)

/-- **The three face squares of a white strict collar centre with `Ψ ≥ 0`**, from the two field facts. -/
theorem face_squares_of_premises {word : Word} (hn3 : 3 ≤ (frameAt word).child.num)
    (hS : (frameAt word).HasStrips (MW word)) (hSingle : SingleFaceSign word) {c : Site}
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hM : laplacian (MW word) c = 0) (hc0 : 0 ≤ sheetPsi word c) (hcoll : CollarFrame (frameAt word) c) :
    (BottomWit (frameAt word) c →
      ∀ c' ∈ squareCorners (c.1 - 1) c.2,
        FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
    (LeftWit (frameAt word) c →
      ∀ c' ∈ squareCorners c.1 c.2,
        FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c') ∧
    (RightWit (frameAt word) c →
      ∀ c' ∈ squareCorners (c.1 - 1) (c.2 - 1),
        FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hSingle c hcS hM hc0 hcoll
  refine ⟨fun hB => ?_, fun hL => ?_, fun hR => ?_⟩
  · apply bottom_face_strict hcS _ hB
    intro e
    subst e
    have := FLatticePaper.StripColours.lap_one_one (frameAt word) hS
    rw [hM] at this
    norm_num at this
  · exact left_face_strict hn3 hcS (fun hB => h1 ⟨hB, hL⟩) (fun hT => h5 ⟨hL, hT⟩) hL
  · exact right_face_strict hn3 hcS (fun hB => h2 ⟨hB, hR⟩) (fun hT => h6 ⟨hR, hT⟩) hR

end FLatticePaper.FaceSquares
