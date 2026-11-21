import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Prod

/-! Section 4 of the paper: cells, tiles, boundary words, almost tilings, and the admissible words of
`lemma:almost_square_tiling`. Gaussian integers `a + b i` are pairs `(a, b)`. -/

namespace FLatticePaper.Tiles

/-- Gaussian integers `a + b i`, as pairs. -/
abbrev GInt := ℤ × ℤ

/-- The unit steps `1` and `i` as Gaussian integers. -/
def gOne : GInt := (1, 0)
def gI : GInt := (0, 1)

/-- The cell `s_x = {x, x+1, x+i, x+1+i}`, given by its lower-left corner `x` (Sec. 4). -/
def cellCorners (x : GInt) : Finset GInt := {x, x + gOne, x + gI, x + (gOne + gI)}

/-- A tile in the cell reading (Secs. 4 and 5.6): a finite set of lower-left corners of cells. -/
abbrev CellTile := Finset GInt

/-- The vertices of a tile: the corners of its cells. -/
def CellTile.vertices (T : CellTile) : Finset GInt := T.biUnion cellCorners

/-- `c` is the lower-left vertex of `T`: the vertex with the smallest imaginary part, then the smallest real part
(Sec. 5.2, line 1100). -/
def IsLowerLeft (T : CellTile) (c : GInt) : Prop :=
  c ∈ T.vertices ∧ ∀ v ∈ T.vertices, c.2 ≤ v.2 ∧ (v.2 = c.2 → c.1 ≤ v.1)

/-- The letters of `F_2`: the unit steps `1, i, -1, -i`. -/
inductive Unit4
  | one
  | i
  | negOne
  | negI
  deriving DecidableEq, Repr

/-- The unit step of a letter. -/
def Unit4.vec : Unit4 → GInt
  | .one => (1, 0)
  | .i => (0, 1)
  | .negOne => (-1, 0)
  | .negI => (0, -1)

/-- The inverse letter, `-x`. -/
def Unit4.neg : Unit4 → Unit4
  | .one => .negOne
  | .i => .negI
  | .negOne => .one
  | .negI => .i

/-- Multiplication of a letter by `i`, as in the map `w ↦ i·w` of Sec. 5.6. -/
def Unit4.mulI : Unit4 → Unit4
  | .one => .i
  | .i => .negOne
  | .negOne => .negI
  | .negI => .one

/-- Multiplication of a letter by `-i`. -/
def Unit4.mulNegI (x : Unit4) : Unit4 := x.mulI.mulI.mulI

/-- A word of `F_2`, as a list of letters. -/
abbrev F2Word := List Unit4

/-- The abelianization `Σ w` (Sec. 4). -/
def F2Word.sum (w : F2Word) : GInt := (w.map Unit4.vec).sum

/-- The inverse `ŵ`, with `ŵ * w = 1` (Sec. 4): reverse and negate. -/
def F2Word.hat (w : F2Word) : F2Word := (w.map Unit4.neg).reverse

/-- The reversal `rev(w)` (Sec. 4). -/
def F2Word.rev (w : F2Word) : F2Word := w.reverse

/-- The vertices visited by the walk of `w` from `c`, starting with `c`. -/
def F2Word.walk (c : GInt) (w : F2Word) : List GInt :=
  w.scanl (fun x s => x + s.vec) c

/-- The four oriented edges of the cell `c` in counterclockwise order, each paired with the cell on its other
side. -/
def cellEdgesWithOther (c : GInt) : List (GInt × GInt × GInt) :=
  [(c, c + gOne, c - gI),
   (c + gOne, c + gOne + gI, c + gOne),
   (c + gOne + gI, c + gI, c + gI),
   (c + gI, c, c - gOne)]

/-- The directed boundary edges of a cell tile: the counterclockwise edges of cells of `T` whose other side is not
in `T`. This is the boundary of Sec. 4 (the cell on the left, no cell on the right). -/
def CellTile.boundaryEdges (T : CellTile) : Finset (GInt × GInt) :=
  T.biUnion fun c =>
    (((cellEdgesWithOther c).filter fun e => e.2.2 ∉ T).toFinset).image fun e => (e.1, e.2.1)

/-- `w` traces the boundary of `T` counterclockwise from its lower-left vertex `c`: the closed walk traverses each
directed boundary edge of `T` exactly once and no other edge (Sec. 4, line 729). -/
def IsBoundaryWordAt (T : CellTile) (c : GInt) (w : F2Word) : Prop :=
  IsLowerLeft T c ∧ w.sum = 0 ∧
    ((F2Word.walk c w).zip (F2Word.walk c w).tail).Nodup ∧
    ((F2Word.walk c w).zip (F2Word.walk c w).tail).toFinset = T.boundaryEdges

/-- `w` is a boundary word of `T`. -/
def IsBoundaryWord (T : CellTile) (w : F2Word) : Prop := ∃ c, IsBoundaryWordAt T c w

/-- A tile whose boundary is a simple closed curve: its boundary word visits no vertex twice (Sec. 4). -/
def IsSimpleTile (T : CellTile) : Prop :=
  ∃ c w, IsBoundaryWordAt T c w ∧ ((F2Word.walk c w).dropLast).Nodup

/-- The lattice `Z v₁ + Z v₂` (Sec. 4, the `(v₁, v₂)`-regular condition). -/
def latticeOf (v₁ v₂ : GInt) : Set GInt :=
  {v | ∃ k k' : ℤ, v = (k * v₁.1 + k' * v₂.1, k * v₁.2 + k' * v₂.2)}

/-- Almost tiling (Sec. 4, lines 754-756), for the family of translates `T + v`, `v ∈ L`: every cell lies in at most
one translate, and every lattice point is a vertex of a cell of some translate. -/
def IsAlmostTiling (T : CellTile) (L : Set GInt) : Prop :=
  (∀ c : GInt, ∀ v ∈ L, ∀ v' ∈ L, c - v ∈ T → c - v' ∈ T → v = v') ∧
    (∀ x : GInt, ∃ v ∈ L, ∃ y ∈ T, x ∈ cellCorners (y + v))

/-- `T` generates a `(v₁, v₂)`-regular almost tiling: the family is `T + latticeOf v₁ v₂` (Sec. 4). -/
def IsRegularAlmostTiling (T : CellTile) (v₁ v₂ : GInt) : Prop :=
  IsAlmostTiling T (latticeOf v₁ v₂)

/-- The tiles `T` and `T + v` share an edge: some cell of `T` and some cell of `T + v` are edge-adjacent. -/
def SharesEdge (T : CellTile) (v : GInt) : Prop :=
  ∃ c ∈ T, ∃ e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)], c + e - v ∈ T

/-- The translation vectors `k g₁ + k' g₂` with `|k|, |k'| ≤ R`: a finite part of `latticeOf g₁ g₂`. -/
def windowTranslates (g₁ g₂ : GInt) (R : ℕ) : Finset GInt :=
  ((Finset.Icc (-(R : ℤ)) (R : ℤ)) ×ˢ (Finset.Icc (-(R : ℤ)) (R : ℤ))).image fun k : ℤ × ℤ =>
    (k.1 * g₁.1 + k.2 * g₂.1, k.1 * g₁.2 + k.2 * g₂.2)

/-- The cells of the window `[-B, B]²`. -/
def window (B : ℕ) : Finset GInt :=
  (Finset.Icc (-(B : ℤ)) (B : ℤ)) ×ˢ (Finset.Icc (-(B : ℤ)) (B : ℤ))

/-- Finite-window version of `IsRegularAlmostTiling T g₁ g₂`: the almost tiling conditions for cells and lattice
points of the window, with translates `|k|, |k'| ≤ R`. Decidable, for the decided instances only. -/
def WindowAlmostTiling (T : CellTile) (g₁ g₂ : GInt) (R B : ℕ) : Prop :=
  (∀ c ∈ window B, ∀ v ∈ windowTranslates g₁ g₂ R, ∀ v' ∈ windowTranslates g₁ g₂ R,
      c - v ∈ T → c - v' ∈ T → v = v') ∧
    (∀ x ∈ window B, ∃ v ∈ windowTranslates g₁ g₂ R, ∃ y ∈ T, x ∈ cellCorners (y + v))

/-- Finite-window version of the edge-sharing clause: a translate sharing an edge with `T` is `±g₁` or `±g₂`. -/
def WindowEdgeClause (T : CellTile) (g₁ g₂ : GInt) (R : ℕ) : Prop :=
  ∀ v ∈ windowTranslates g₁ g₂ R, v ≠ 0 → SharesEdge T v → v = g₁ ∨ v = -g₁ ∨ v = g₂ ∨ v = -g₂

instance (T : CellTile) (v : GInt) : Decidable (SharesEdge T v) := by
  unfold SharesEdge
  infer_instance

instance (T : CellTile) (g₁ g₂ : GInt) (R B : ℕ) : Decidable (WindowAlmostTiling T g₁ g₂ R B) := by
  unfold WindowAlmostTiling
  infer_instance

instance (T : CellTile) (g₁ g₂ : GInt) (R : ℕ) : Decidable (WindowEdgeClause T g₁ g₂ R) := by
  unfold WindowEdgeClause
  infer_instance

/-- Every letter of `w` is `1` or `i`: the monotonicity clause, `{-1, -i} ∉ w` (line 782). -/
def Monotone (w : F2Word) : Prop := ∀ x ∈ w, x = .one ∨ x = .i

/-- Every `i` of `w` is followed by at least `k` letters `1`. -/
def IFollowedBy (k : ℕ) (w : F2Word) : Prop :=
  ∀ j, w[j]? = some .i → ∀ m < k, w[j + 1 + m]? = some .one

/-- The bounded form of `IFollowedBy`, decidable for a given word. -/
theorem iFollowedBy_iff (k : ℕ) (w : F2Word) :
    IFollowedBy k w ↔ ∀ j < w.length, w[j]? = some .i → ∀ m < k, w[j + 1 + m]? = some .one := by
  constructor
  · intro h j _ hj
    exact h j hj
  · intro h j hj m hm
    have hlt : j < w.length := by
      by_contra hcon
      have hnone : w[j]? = none := List.getElem?_eq_none (by omega)
      rw [hnone] at hj
      simp at hj
    exact h j hlt hj m hm

instance (w : F2Word) : Decidable (Monotone w) := by
  unfold Monotone
  infer_instance

instance (T : CellTile) (c : GInt) : Decidable (IsLowerLeft T c) := by
  unfold IsLowerLeft
  infer_instance

instance (T : CellTile) (c : GInt) (w : F2Word) : Decidable (IsBoundaryWordAt T c w) := by
  unfold IsBoundaryWordAt
  infer_instance

instance (k : ℕ) (w : F2Word) : Decidable (IFollowedBy k w) :=
  decidable_of_iff _ (iFollowedBy_iff k w).symm

/-- The admissible words of `lemma:almost_square_tiling` (lines 782-799): monotone, first and last letters `1`, and
one of the cases (a) palindrome, (b) `w = (1*1*i) * w̃ * 1` with `w̃` a palindrome and every `i` followed by at least
one `1`, (c) `w = 1 * w̃ * (1*1*1)` with `w̃` a palindrome and every `i` followed by at least three `1`s. -/
def Admissible (w : F2Word) : Prop :=
  Monotone w ∧ w.head? = some .one ∧ w.getLast? = some .one ∧
    (w.reverse = w ∨
      (∃ wt : F2Word, w = [.one, .one, .i] ++ wt ++ [.one] ∧ wt.reverse = wt ∧ IFollowedBy 1 w) ∨
      (∃ wt : F2Word, w = [.one] ++ wt ++ [.one, .one, .one] ∧ wt.reverse = wt ∧ IFollowedBy 3 w))

end FLatticePaper.Tiles
