import FLatticePaper.Tiles.StackedWalks

/-! Entry facts for the walk of a word with letters `one` and `i`, used for the column propagation of the top and bottom walks.
A column is left only to the right, and the walk enters the next column at the top of the previous one. -/

namespace FLatticePaper.Tiles.StackedEntry

open FLatticePaper.Tiles FLatticePaper.Tiles.StackedWalks

theorem walk_head_mem' (c : GInt) (w : F2Word) : c ∈ F2Word.walk c w := by
  cases w <;> simp [WalkDecomp.walk_nil, WalkDecomp.walk_cons]

theorem vec_one_fst' (c : GInt) : (c + Unit4.one.vec).1 = c.1 + 1 := by simp [Unit4.vec]
theorem vec_one_snd' (c : GInt) : (c + Unit4.one.vec).2 = c.2 := by simp [Unit4.vec]
theorem vec_i_fst' (c : GInt) : (c + Unit4.i.vec).1 = c.1 := by simp [Unit4.vec]
theorem vec_i_snd' (c : GInt) : (c + Unit4.i.vec).2 = c.2 + 1 := by simp [Unit4.vec]

/-- **A later column lies above an earlier one.** Every point of the walk over a larger column is at or above every point over a
smaller column. -/
theorem walk_later_above : ∀ (w : F2Word), (∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c p q : GInt), p ∈ F2Word.walk c w → q ∈ F2Word.walk c w → p.1 < q.1 → p.2 ≤ q.2 := by
  intro w
  induction w with
  | nil =>
    intro hw c p q hp hq hlt
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hp hq
    subst hp; subst hq
    exact absurd hlt (lt_irrefl _)
  | cons x w ih =>
    intro hw c p q hp hq hlt
    have hx : x = Unit4.one ∨ x = Unit4.i := hw x (by simp)
    have hw' : ∀ y ∈ w, y = Unit4.one ∨ y = Unit4.i := fun y hy => hw y (by simp [hy])
    rw [WalkDecomp.walk_cons] at hp hq
    rw [List.mem_cons] at hp hq
    rcases hp with hpc | hp <;> rcases hq with hqc | hq
    · have e1 : p.1 = c.1 := congrArg Prod.fst hpc
      have e2 : q.1 = c.1 := congrArg Prod.fst hqc
      omega
    · have hle := le_add_vec c x hx
      have hq2 := walk_ge_start w hw' (c + x.vec) q hq
      have e1 : p.2 = c.2 := congrArg Prod.snd hpc
      omega
    · have hle := le_add_vec c x hx
      have hp2 := walk_ge_start w hw' (c + x.vec) p hp
      have e1 : q.1 = c.1 := congrArg Prod.fst hqc
      omega
    · exact ih hw' (c + x.vec) p q hp hq hlt

/-- **The walk enters the next column at or below the top of the previous one.** If `(s, H)` is the top point of the walk over column
`s` and the walk visits column `s + 1`, then it has a point over `s + 1` at a height at most `H`. -/
theorem walk_entry_le : ∀ (w : F2Word), (∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c : GInt) (s H : ℤ), ((s, H) : GInt) ∈ F2Word.walk c w →
      (∀ p ∈ F2Word.walk c w, p.1 = s → p.2 ≤ H) → (∃ q ∈ F2Word.walk c w, q.1 = s + 1) →
      ∃ h : ℤ, h ≤ H ∧ ((s + 1, h) : GInt) ∈ F2Word.walk c w := by
  intro w
  induction w with
  | nil =>
    intro hw c s H hsH hmax hnext
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hsH hnext
    obtain ⟨q, hq, hq1⟩ := hnext
    subst hq
    subst hsH
    simp at hq1
  | cons x w ih =>
    intro hw c s H hsH hmax hnext
    have hx : x = Unit4.one ∨ x = Unit4.i := hw x (by simp)
    have hw' : ∀ y ∈ w, y = Unit4.one ∨ y = Unit4.i := fun y hy => hw y (by simp [hy])
    rw [WalkDecomp.walk_cons] at hsH hmax hnext ⊢
    rw [List.mem_cons] at hsH
    rcases hsH with hhead | htail
    · -- the point `(s, H)` is the start `c`
      have hcs : c = ((s, H) : GInt) := hhead.symm
      have hc1 : c.1 = s := by rw [hcs]
      have hc2 : c.2 = H := by rw [hcs]
      obtain ⟨q, hq, hq1⟩ := hnext
      rw [List.mem_cons] at hq
      rcases hq with hqc | hqt
      · have := congrArg Prod.fst hqc
        omega
      rcases hx with hx1 | hx1 <;> subst hx1
      · refine ⟨H, le_rfl, List.mem_cons_of_mem _ ?_⟩
        have e : ((s + 1, H) : GInt) = c + Unit4.one.vec := by
          ext <;> simp [Unit4.vec, hc1, hc2]
        rw [e]
        exact walk_head_mem' _ w
      · have hmi := hmax (c + Unit4.i.vec) (List.mem_cons_of_mem _ (walk_head_mem' (c + Unit4.i.vec) w))
          (by rw [vec_i_fst', hc1])
        rw [vec_i_snd', hc2] at hmi
        omega
    · -- the point `(s, H)` lies after the start
      have hmax' : ∀ p ∈ F2Word.walk (c + x.vec) w, p.1 = s → p.2 ≤ H := by
        intro p hp hps
        exact hmax p (List.mem_cons_of_mem _ hp) hps
      obtain ⟨q, hq, hq1⟩ := hnext
      rw [List.mem_cons] at hq
      rcases hq with hqc | hqt
      · have hlt := walk_ge_start w hw' (c + x.vec) (s, H) htail
        have hcle := le_add_vec c x hx
        have hqc' := congrArg Prod.fst hqc
        omega
      · obtain ⟨h, hh, hmem⟩ := ih hw' (c + x.vec) s H htail hmax' ⟨q, hqt, hq1⟩
        exact ⟨h, hh, List.mem_cons_of_mem _ hmem⟩

end FLatticePaper.Tiles.StackedEntry
