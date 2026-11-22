import FLatticePaper.Tiles.RowInterval
import FLatticePaper.Tiles.RowChain

/-! Task 53, step 2 (row-chain route): a tile whose boundary word is `w1 * w2 * hat(rev w1) * hat(rev w2)` with
`w1` in `{1, i}` and `w2` in `{i, -1}` is a row chain as soon as the two end columns of its rows satisfy a finite set of
inequalities. The rows of the tile are the intervals `[arcLeft b, arcRight b)` (`mem_iff_interval`); the row-chain
properties then reduce to the inequalities: each row is nonempty, and consecutive rows overlap. Numerically (`scripts/arcs.py`)
every standard tile has this boundary shape, with these rows, and the inequalities hold up to length 5. The induction
on the recursion must prove the inequalities for the standard words. -/

namespace FLatticePaper.Tiles

/-- The left end column of row `b` of the tile of the arcs `w1, w2` starting at `c`: the column of the south step. -/
def arcLeft (w1 w2 : F2Word) (c : GInt) (b : ℤ) : ℤ :=
  colS (w1.map Unit4.neg ++ w2.map Unit4.neg) (c + F2Word.sum (w1 ++ w2)) b

/-- The right end column (exclusive) of row `b`: the column of the north step. -/
def arcRight (w1 w2 : F2Word) (c : GInt) (b : ℤ) : ℤ :=
  colN (w1 ++ w2) c b

/-- The cells of the tile in row `b` are exactly the columns of `[arcLeft b, arcRight b)`, for the rows `[c.2, c.2 + cntI)`. -/
theorem mem_arc_iff {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne) (a b : ℤ) :
    ((a, b) : GInt) ∈ T ↔
      (c.2 ≤ b ∧ b < c.2 + cntI (w1 ++ w2)) ∧ arcLeft w1 w2 c b ≤ a ∧ a < arcRight w1 w2 c b :=
  mem_iff_interval hT h1 h2 a b

/-- Row-chain from the end columns: each row in the range is nonempty, and consecutive rows overlap. -/
theorem cellRowChain_of_arcs {T : CellTile} {c : GInt} {w1 w2 : F2Word}
    (hT : IsBoundaryWordAt T c (boundaryWordOf w1 w2))
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i) (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hne : ∀ b, c.2 ≤ b → b < c.2 + cntI (w1 ++ w2) → arcLeft w1 w2 c b < arcRight w1 w2 c b)
    (hov : ∀ b, c.2 ≤ b → b + 1 < c.2 + cntI (w1 ++ w2) →
      arcLeft w1 w2 c (b + 1) < arcRight w1 w2 c b ∧ arcLeft w1 w2 c b < arcRight w1 w2 c (b + 1)) :
    CellRowChain T := by
  have mem := mem_arc_iff hT h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro y x₁ x₂ x₃ h₁ h₃ hle₁ hle₂
    rw [mem] at h₁ h₃ ⊢
    obtain ⟨r₁, l₁, u₁⟩ := h₁
    obtain ⟨r₃, l₃, u₃⟩ := h₃
    exact ⟨r₁, by omega, by omega⟩
  · rintro y ⟨x, hx⟩ ⟨x', hx'⟩
    rw [mem] at hx hx'
    have hlo : c.2 ≤ y := hx.1.1
    have hhi : y + 1 < c.2 + cntI (w1 ++ w2) := hx'.1.2
    obtain ⟨h₁, h₂⟩ := hov y hlo hhi
    have e₁ := hne y hlo (by omega)
    have e₂ := hne (y + 1) (by omega) hhi
    refine ⟨max (arcLeft w1 w2 c y) (arcLeft w1 w2 c (y + 1)), ?_, ?_⟩
    · rw [mem]
      refine ⟨⟨hlo, by omega⟩, le_max_left _ _, max_lt e₁ h₁⟩
    · rw [mem]
      refine ⟨⟨by omega, hhi⟩, le_max_right _ _, max_lt h₂ e₂⟩
  · intro y₁ y₂ y ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ hy₁ hy₂
    rw [mem] at h₁ h₂
    obtain ⟨⟨a₁, a₂⟩, -, -⟩ := h₁
    obtain ⟨⟨b₁, b₂⟩, -, -⟩ := h₂
    have hlo : c.2 ≤ y := by omega
    have hhi : y < c.2 + cntI (w1 ++ w2) := by omega
    refine ⟨arcLeft w1 w2 c y, ?_⟩
    rw [mem]
    exact ⟨⟨hlo, hhi⟩, le_refl _, hne y hlo hhi⟩

end FLatticePaper.Tiles
