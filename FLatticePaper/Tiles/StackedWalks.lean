import FLatticePaper.Tiles.StackedPaths
import FLatticePaper.Tiles.WalkDecomp

/-! Monotonicity of the boundary paths of binary words. The letters of `gH w` are `one` and `i` (the pair map `gPair` only
produces these letters), so every point of the walk of `gH w` from `c` is above `c` in the componentwise order, and the walk is
pairwise increasing: an earlier point of the walk is below a later one. -/

namespace FLatticePaper.Tiles.StackedWalks

open FLatticePaper.Tiles

/-- The letters of the pair map of a tile sequence are `one` and `i`. -/
theorem G_letters : ∀ ts : List ZTile, ∀ x ∈ GHJoin.G ts, x = Unit4.one ∨ x = Unit4.i
  | [] => by simp [GHJoin.G]
  | [_] => by simp [GHJoin.G]
  | a :: b :: r => by
    intro x hx
    rw [GHJoin.G_cons_cons, List.mem_append] at hx
    rcases hx with h | h
    · cases a <;> cases b <;> simp [gPair] at h <;> rcases h with rfl | rfl <;> simp
    · exact G_letters (b :: r) x h

/-- The letters of the boundary path `gH w` are `one` and `i`. -/
theorem gH_letters (w : BinaryWord) : ∀ x ∈ gH w, x = Unit4.one ∨ x = Unit4.i := by
  intro x hx
  rw [GHJoin.gH_eq, List.mem_append] at hx
  rcases hx with h | h
  · exact G_letters _ x h
  · simp at h
    exact Or.inl h

/-- A unit step of letter `one` or `i` moves a point up and right. -/
theorem le_add_vec (c : GInt) (x : Unit4) (hx : x = Unit4.one ∨ x = Unit4.i) :
    c.1 ≤ (c + x.vec).1 ∧ c.2 ≤ (c + x.vec).2 := by
  rcases hx with rfl | rfl <;> simp [Unit4.vec]

/-- Every point of the walk from `c` lies above `c`. -/
theorem walk_ge_start (w : F2Word) (hw : ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) :
    ∀ c : GInt, ∀ b ∈ F2Word.walk c w, c.1 ≤ b.1 ∧ c.2 ≤ b.2 := by
  induction w with
  | nil => intro c b hb; simp [WalkDecomp.walk_nil] at hb; subst hb; exact ⟨le_rfl, le_rfl⟩
  | cons x w ih =>
    intro c b hb
    have hx : x = Unit4.one ∨ x = Unit4.i := hw x (by simp)
    have hw' : ∀ y ∈ w, y = Unit4.one ∨ y = Unit4.i := fun y hy => hw y (by simp [hy])
    rw [WalkDecomp.walk_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨le_rfl, le_rfl⟩
    · have h1 := le_add_vec c x hx
      have h2 := ih hw' (c + x.vec) b hb
      exact ⟨le_trans h1.1 h2.1, le_trans h1.2 h2.2⟩

/-- **The walk of a word with letters `one` and `i` is pairwise increasing** in the componentwise order. -/
theorem walk_pairwise (w : F2Word) (hw : ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) :
    ∀ c : GInt, (F2Word.walk c w).Pairwise (fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2) := by
  induction w with
  | nil => intro c; simp [WalkDecomp.walk_nil]
  | cons x w ih =>
    intro c
    have hx : x = Unit4.one ∨ x = Unit4.i := hw x (by simp)
    have hw' : ∀ y ∈ w, y = Unit4.one ∨ y = Unit4.i := fun y hy => hw y (by simp [hy])
    rw [WalkDecomp.walk_cons, List.pairwise_cons]
    exact ⟨fun b hb => walk_ge_start w hw' (c + x.vec) b hb |>.imp (fun h => le_trans (le_add_vec c x hx).1 h)
        (fun h => le_trans (le_add_vec c x hx).2 h),
      ih hw' (c + x.vec)⟩

/-- The walk of the boundary path `gH b` is pairwise increasing. -/
theorem gH_walk_pairwise (b : BinaryWord) (c : GInt) :
    (F2Word.walk c (gH b)).Pairwise (fun a b => a.1 ≤ b.1 ∧ a.2 ≤ b.2) :=
  walk_pairwise _ (gH_letters b) c

end FLatticePaper.Tiles.StackedWalks
