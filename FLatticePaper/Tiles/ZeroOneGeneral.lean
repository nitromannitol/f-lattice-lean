import FLatticePaper.Tiles.ZeroOneOdometers

/-! Zero-one odometers for every word (task 16). The family of a letter sequence `ℓ` is given by recursion on the
index: positions `posF`, slope parameters `aF` (integer increments `deltaOf`, fixed by the slope relation) and
constants `bF` (increments `betaOf`, read off from the first overlap or adjacency). -/

namespace FLatticePaper.Tiles
open Finset

def dotS (v x : Site) : ℤ := v.1 * x.1 + v.2 * x.2

/-- The integer increment `delta = slopeDiff − (base(b) − base(a))` of the slope parameter. -/
def deltaOf : Orientation → Letter → Letter → Site
  | .horizontal, .p, .p => (0, 0)
  | .horizontal, .q, .q => (0, 0)
  | .horizontal, .p, .q => (-1, 0)
  | .horizontal, .q, .p => (1, 0)
  | .vertical, .p, .p => (0, -1)
  | .vertical, .q, .q => (1, -1)
  | .vertical, .p, .q => (0, -1)
  | .vertical, .q, .p => (1, -1)

/-- The target value of the non-overlap rule: `0` horizontally, `−1` vertically. -/
def targetOf : Orientation → ℤ
  | .horizontal => 0
  | .vertical => -1

/-- The corner step between consecutive letters `a, b` (reversed or not). -/
def stepOf (o : Orientation) (rev : Bool) (a b : Letter) : Site :=
  match o, rev with
  | .horizontal, false => zeroOneHorizontalStep b
  | .horizontal, true => zeroOneHorizontalReversedStep a b
  | .vertical, false => zeroOneVerticalStep b
  | .vertical, true => zeroOneVerticalReversedStep a b

/-- Lower-left positions of the tiles of the letter sequence `ℓ`. -/
def posF (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) : ℕ → Site
  | 0 => 0
  | k + 1 => posF o rev ℓ k + stepOf o rev (ℓ k) (ℓ (k + 1))

/-- The slope parameters of the letter sequence `ℓ`. -/
def aF (o : Orientation) (ℓ : ℕ → Letter) : ℕ → Site
  | 0 => 0
  | k + 1 => aF o ℓ k + deltaOf o (ℓ k) (ℓ (k + 1))

/-- A site `p` of the first tile with `p − s` in the second tile, where `s` is the step. -/
def overlapWitness (a b : Letter) (s : Site) : Option Site :=
  (tileSites a).find? fun p => decide (p - s ∈ tileSites b)

/-- A pair `(p, q)` of sites of the two tiles whose translated positions are adjacent. -/
def adjWitness (a b : Letter) (s : Site) : Option (Site × Site) :=
  ((tileSites a).flatMap fun p => (tileSites b).map fun q => (p, q)).find? fun pq =>
    decide ((pq.1 - pq.2 - s).1.natAbs + (pq.1 - pq.2 - s).2.natAbs = 1)

/-- The increment of the constant `b` at step `k`: read off from the overlap or from the adjacency. -/
def betaOf (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (k : ℕ) : ℤ :=
  let a := ℓ k
  let b := ℓ (k + 1)
  let s := stepOf o rev a b
  let d := deltaOf o a b
  let c := posF o rev ℓ k
  match overlapWitness a b s with
  | some p => (baseOdometer a p - baseOdometer b (p - s) - dotS d p) - dotS d c
  | none =>
    match adjWitness a b s with
    | some (p, q) =>
      targetOf o + (baseOdometer a p - baseOdometer b q - dotS d q)
        + dotS (aF o ℓ k) (p - q - s) - dotS d (c + s)
    | none => 0

/-- The ℕ-indexed constants `b`. -/
def bF (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) : ℕ → ℤ
  | 0 => 0
  | k + 1 => bF o rev ℓ k + betaOf o rev ℓ k

/-- The zero-one family of the letter sequence `ℓ` on `n` tiles. -/
def familyF (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (n : ℕ) : ZOFamily where
  n := n
  letter := ℓ
  pos := posF o rev ℓ
  a := aF o ℓ
  b := bF o rev ℓ

/-- The letter sequence of the (reversed) word, read as a function with default `p`. -/
def lettersOf (w : BinaryWord) (rev : Bool) : ℕ → Letter :=
  fun k => (if rev then w.reverse else w).getD k .p


/-! Finite local facts, decided over all configurations. -/

theorem overlap_consistent :
    ∀ o ∈ [Orientation.horizontal, Orientation.vertical], ∀ rev ∈ [false, true],
      ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q],
      ∀ p ∈ tileSites a, ∀ p' ∈ tileSites a,
        p - stepOf o rev a b ∈ tileSites b → p' - stepOf o rev a b ∈ tileSites b →
          baseOdometer a p - baseOdometer b (p - stepOf o rev a b) - dotS (deltaOf o a b) p =
            baseOdometer a p' - baseOdometer b (p' - stepOf o rev a b) - dotS (deltaOf o a b) p' := by
  decide +kernel

theorem adjacent_consistent :
    ∀ o ∈ [Orientation.horizontal, Orientation.vertical], ∀ rev ∈ [false, true],
      ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q],
      (∀ p ∈ tileSites a, p - stepOf o rev a b ∉ tileSites b) →
      ∀ p ∈ tileSites a, ∀ q ∈ tileSites b, ∀ p' ∈ tileSites a, ∀ q' ∈ tileSites b,
        (p - q - stepOf o rev a b).1.natAbs + (p - q - stepOf o rev a b).2.natAbs = 1 →
        (p' - q' - stepOf o rev a b).1.natAbs + (p' - q' - stepOf o rev a b).2.natAbs = 1 →
          p - q - stepOf o rev a b = p' - q' - stepOf o rev a b ∧
            baseOdometer a p - baseOdometer b q - dotS (deltaOf o a b) q =
              baseOdometer a p' - baseOdometer b q' - dotS (deltaOf o a b) q' := by
  decide +kernel

theorem distance_two_disjoint :
    ∀ o ∈ [Orientation.horizontal, Orientation.vertical], ∀ rev ∈ [false, true],
      ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q], ∀ c ∈ [Letter.p, Letter.q],
        ∀ p ∈ tileSites a, ∀ r ∈ tileSites c,
          p ≠ r + (stepOf o rev a b + stepOf o rev b c) := by
  decide +kernel

theorem slope_delta_consistent :
    ∀ o ∈ [Orientation.horizontal, Orientation.vertical],
      ∀ a ∈ [Letter.p, Letter.q], ∀ b ∈ [Letter.p, Letter.q],
        slopeDiff o a b =
          (((deltaOf o a b).1 : ℚ), ((deltaOf o a b).2 : ℚ)) +
            (slopeOf (baseOdometer b) (tileSites b) - slopeOf (baseOdometer a) (tileSites a)) := by
  decide +kernel

end FLatticePaper.Tiles
