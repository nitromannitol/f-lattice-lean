import FLatticePaper.Tiles.BoundaryWalks
import FLatticePaper.Tiles.NearStairBoundary

/-! The boundary word `w₁ w₂ hat(rev w₁) hat(rev w₂)` as four walks (TeX 2723, step 3).

The walk of `hat(rev w₁)` from `z = Σw₁ + Σw₂` is the half-turn `e ↦ z - e` of the walk of `w₁` from `0`, and the walk of
`hat(rev w₂)` from `z - Σw₁` is the half-turn of the walk of `w₂` from `Σw₁`. So the edges of the boundary word are
`E₁ ++ E₂ ++ halfE z E₁ ++ halfE z E₂` for the bottom walk `E₁` and the right walk `E₂`. The criterion
`isBoundaryFrom_boundaryWordOf` reduces the boundary-word statement of a tile to: its bottom and right walks are boundary
edges, the tile is half-turn symmetric, and the boundary is covered by the four walks, each edge once (named inputs). -/

namespace FLatticePaper.Tiles.FourWalks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.BoundaryWalks

/-- The half-turn of a directed edge about `z / 2`: `e ↦ (z - a, z - b)`. -/
def halfE (z : GInt) (e : GInt × GInt) : GInt × GInt := (z - e.1, z - e.2)

theorem vec_neg_letter (x : Unit4) : Unit4.vec (Unit4.neg x) = -Unit4.vec x := by
  cases x <;> simp [Unit4.vec, Unit4.neg]

theorem F2Word_sum_map_neg (w : F2Word) : F2Word.sum (w.map Unit4.neg) = -F2Word.sum w := by
  induction w with
  | nil => simp [F2Word.sum]
  | cons x w ih =>
    rw [List.map_cons, F2Word_sum_cons, F2Word_sum_cons, vec_neg_letter, ih]
    abel

/-- The walk of the negated letters from `z - q` is the half-turn of the walk from `q`. -/
theorem edgesFrom_neg_half (z : GInt) (w : F2Word) : ∀ (q : GInt),
    edgesFrom (z - q) (w.map Unit4.neg) = (edgesFrom q w).map (halfE z) := by
  induction w with
  | nil => intro q; simp [edgesFrom]
  | cons x w ih =>
    intro q
    have h1 : (z - q) + Unit4.vec (Unit4.neg x) = z - (q + Unit4.vec x) := by
      rw [vec_neg_letter]
      abel
    simp only [List.map_cons, edgesFrom]
    rw [h1, ih]
    simp [halfE]

/-- The walk of `w₁ w₂ hat(rev w₁) hat(rev w₂)` from `0`: the bottom walk, the right walk and their half-turns. -/
theorem edgesFrom_boundaryWordOf (w₁ w₂ : F2Word) :
    edgesFrom 0 (boundaryWordOf w₁ w₂) =
      edgesFrom 0 w₁ ++ edgesFrom (F2Word.sum w₁) w₂ ++
        (edgesFrom 0 w₁).map (halfE (F2Word.sum w₁ + F2Word.sum w₂)) ++
        (edgesFrom (F2Word.sum w₁) w₂).map (halfE (F2Word.sum w₁ + F2Word.sum w₂)) := by
  unfold boundaryWordOf
  rw [NearStairBoundary.hat_rev_map_neg, NearStairBoundary.hat_rev_map_neg]
  have e1 : edgesFrom 0 (w₁ ++ w₂ ++ w₁.map Unit4.neg) =
      edgesFrom 0 w₁ ++ edgesFrom (F2Word.sum w₁) w₂ ++
        edgesFrom ((F2Word.sum w₁ + F2Word.sum w₂) - 0) (w₁.map Unit4.neg) := by
    simp only [edgesFrom_append, zero_add, F2Word_sum_append, sub_zero]
  have e2 : edgesFrom 0 (w₁ ++ w₂ ++ w₁.map Unit4.neg ++ w₂.map Unit4.neg) =
      (edgesFrom 0 w₁ ++ edgesFrom (F2Word.sum w₁) w₂ ++
        edgesFrom ((F2Word.sum w₁ + F2Word.sum w₂) - 0) (w₁.map Unit4.neg)) ++
        edgesFrom ((F2Word.sum w₁ + F2Word.sum w₂) + -F2Word.sum w₁) (w₂.map Unit4.neg) := by
    rw [edgesFrom_append, e1]
    simp only [zero_add, F2Word_sum_append, F2Word_sum_map_neg]
  rw [e2, ← sub_eq_add_neg, edgesFrom_neg_half, edgesFrom_neg_half]

/-- The boundary word of `w₁ w₂ hat(rev w₁) hat(rev w₂)` has sum zero. -/
theorem sum_boundaryWordOf (w₁ w₂ : F2Word) : F2Word.sum (boundaryWordOf w₁ w₂) = 0 := by
  unfold boundaryWordOf
  rw [NearStairBoundary.hat_rev_map_neg, NearStairBoundary.hat_rev_map_neg]
  simp only [F2Word_sum_append, F2Word_sum_map_neg]
  abel

/-- The criterion: a tile whose boundary is half-turn symmetric and covered by the four walks (each edge once) has the
boundary word `w₁ w₂ hat(rev w₁) hat(rev w₂)` from `0`. -/
theorem isBoundaryFrom_boundaryWordOf (T : CellTile) (w₁ w₂ : F2Word)
    (hsym : ∀ e ∈ T.boundaryEdges, halfE (F2Word.sum w₁ + F2Word.sum w₂) e ∈ T.boundaryEdges)
    (hsub : ∀ e ∈ edgesFrom 0 w₁ ++ edgesFrom (F2Word.sum w₁) w₂, e ∈ T.boundaryEdges)
    (hcov : ∀ e ∈ T.boundaryEdges, e ∈ edgesFrom 0 (boundaryWordOf w₁ w₂))
    (hnd : (edgesFrom 0 (boundaryWordOf w₁ w₂)).Nodup) :
    IsBoundaryFrom T 0 (boundaryWordOf w₁ w₂) := by
  refine ⟨sum_boundaryWordOf w₁ w₂, hnd, ?_⟩
  ext e
  rw [List.mem_toFinset]
  constructor
  · intro he
    rw [edgesFrom_boundaryWordOf] at he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with ((h | h) | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
    · exact hsub e (by simp [h])
    · exact hsub e (by simp [h])
    · exact hsym f (hsub f (by simp [hf]))
    · exact hsym f (hsub f (by simp [hf]))
  · intro he
    exact hcov e he

end FLatticePaper.Tiles.FourWalks
