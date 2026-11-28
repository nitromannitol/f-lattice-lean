import FLatticePaper.Tiles.StackedEntry
import FLatticePaper.Tiles.StackedWalks

/-! Consecutive points of a walk with letters `one` and `i`. A point of the walk over a column `t`, at height `h` maximal over
that column, followed by a point over `t + 1`, is followed in the walk by the horizontal step `(t, h) → (t + 1, h)`. Also every
point of a walk other than its start is preceded by a point. These are the list-level facts used to read the horizontal steps
of the bottom walk as boundary edges of the tile. -/

namespace FLatticePaper.Tiles.StackedWalkPattern

open FLatticePaper.Tiles FLatticePaper.Tiles.StackedWalks

/-- A walk is a start point followed by a list. -/
theorem walk_head_cons (c : GInt) (u : F2Word) : ∃ r : List GInt, F2Word.walk c u = c :: r := by
  cases u with
  | nil => exact ⟨[], by simp [WalkDecomp.walk_nil]⟩
  | cons x v => exact ⟨_, WalkDecomp.walk_cons c x v⟩

/-- **The horizontal step after a maximal point.** If `(t, h)` is the highest point of the walk over `t`, and the walk has a
point over `t + 1`, then `(t, h)` is immediately followed by `(t + 1, h)`. -/
theorem pattern_step : ∀ (u : F2Word), (∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c : GInt) (t h : ℤ),
      ((t, h) : GInt) ∈ F2Word.walk c u → (∀ q ∈ F2Word.walk c u, q.1 = t → q.2 ≤ h) →
      (∃ q ∈ F2Word.walk c u, q.1 = t + 1) →
      ∃ l1 l2 : List GInt, F2Word.walk c u = l1 ++ [((t, h) : GInt), ((t + 1, h) : GInt)] ++ l2 := by
  intro u
  induction u with
  | nil =>
    intro _ c t h hp _ hnext
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hp hnext
    obtain ⟨q, hq, hq1⟩ := hnext
    subst hq
    subst hp
    simp at hq1
  | cons x v ih =>
    intro hu c t h hp hmax hnext
    have hx : x = Unit4.one ∨ x = Unit4.i := hu x (by simp)
    have hv : ∀ y ∈ v, y = Unit4.one ∨ y = Unit4.i := fun y hy => hu y (by simp [hy])
    rw [WalkDecomp.walk_cons] at hp
    rcases List.mem_cons.1 hp with hhead | htail
    · -- the point is the start of the walk
      have hc : c = ((t, h) : GInt) := hhead.symm
      subst hc
      rcases hx with rfl | rfl
      · obtain ⟨r, hr⟩ := walk_head_cons (((t, h) : GInt) + Unit4.one.vec) v
        refine ⟨[], r, ?_⟩
        rw [WalkDecomp.walk_cons, hr]
        have e : ((t, h) : GInt) + Unit4.one.vec = ((t + 1, h) : GInt) := by
          ext <;> simp [Unit4.vec]
        rw [e]
        simp
      · exfalso
        have hm := hmax (((t, h) : GInt) + Unit4.i.vec)
          (by rw [WalkDecomp.walk_cons]; exact List.mem_cons_of_mem _ (StackedEntry.walk_head_mem' _ v))
          (by simp [Unit4.vec])
        simp [Unit4.vec] at hm
    · -- the point lies after the start
      have hpmem : ((t, h) : GInt) ∈ F2Word.walk c (x :: v) := by
        rw [WalkDecomp.walk_cons]
        exact List.mem_cons_of_mem _ htail
      have hcle := StackedWalks.walk_ge_start (x :: v) hu c ((t, h) : GInt) hpmem
      have hmax' : ∀ q ∈ F2Word.walk (c + x.vec) v, q.1 = t → q.2 ≤ h := by
        intro q hq hq1
        exact hmax q (by rw [WalkDecomp.walk_cons]; exact List.mem_cons_of_mem _ hq) hq1
      obtain ⟨q, hq, hq1⟩ := hnext
      rw [WalkDecomp.walk_cons] at hq
      rcases List.mem_cons.1 hq with hqc | hqt
      · exfalso
        rw [hqc] at hq1
        simp only at hq1 hcle
        omega
      · obtain ⟨l1, l2, hl⟩ := ih hv (c + x.vec) t h htail hmax' ⟨q, hqt, hq1⟩
        refine ⟨c :: l1, l2, ?_⟩
        rw [WalkDecomp.walk_cons, hl]
        simp

/-- **Every point of a walk other than its start has a predecessor in the walk.** -/
theorem pattern_pred : ∀ (u : F2Word), (∀ x ∈ u, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c p : GInt), p ∈ F2Word.walk c u → p ≠ c →
      ∃ q : GInt, ∃ l1 l2 : List GInt, F2Word.walk c u = l1 ++ [q, p] ++ l2 := by
  intro u
  induction u with
  | nil =>
    intro _ c p hp hne
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hp
    exact absurd hp hne
  | cons x v ih =>
    intro hu c p hp hne
    have hv : ∀ y ∈ v, y = Unit4.one ∨ y = Unit4.i := fun y hy => hu y (by simp [hy])
    rw [WalkDecomp.walk_cons] at hp ⊢
    rcases List.mem_cons.1 hp with hhead | htail
    · exact absurd hhead hne
    · by_cases hpe : p = c + x.vec
      · obtain ⟨r, hr⟩ := walk_head_cons (c + x.vec) v
        refine ⟨c, [], r, ?_⟩
        rw [hr, hpe]
        simp
      · obtain ⟨q, l1, l2, hl⟩ := ih hv (c + x.vec) p htail hpe
        refine ⟨q, c :: l1, l2, ?_⟩
        rw [hl]
        simp

end FLatticePaper.Tiles.StackedWalkPattern
