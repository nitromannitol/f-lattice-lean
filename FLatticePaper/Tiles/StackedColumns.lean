import FLatticePaper.Tiles.StackedWalks

/-! The points of the walk of a word with letters `one` and `i` over one column form an interval of heights: the walk moves by
unit steps, and a column is entered and left only by vertical steps. This gives the column description `{t} × [B^-, B^+] =
B ∩ {x1 = t}` of the forward path of the text's Step 3. -/

namespace FLatticePaper.Tiles.StackedColumns

open FLatticePaper.Tiles FLatticePaper.Tiles.StackedWalks

theorem walk_head_mem (c : GInt) (w : F2Word) : c ∈ F2Word.walk c w := by
  cases w <;> simp [WalkDecomp.walk_nil, WalkDecomp.walk_cons]

theorem vec_one_fst (c : GInt) : (c + Unit4.one.vec).1 = c.1 + 1 := by simp [Unit4.vec]
theorem vec_i_fst (c : GInt) : (c + Unit4.i.vec).1 = c.1 := by simp [Unit4.vec]
theorem vec_i_snd (c : GInt) : (c + Unit4.i.vec).2 = c.2 + 1 := by simp [Unit4.vec]

/-- **The column interval.** Two points of the walk over the same column `t`, with the first below the second, carry every
intermediate lattice height over `t` in the walk. -/
theorem walk_column_interval : ∀ (w : F2Word), (∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i) →
    ∀ (c p q : GInt), p ∈ F2Word.walk c w → q ∈ F2Word.walk c w → p.1 = q.1 → p.2 ≤ q.2 →
      ∀ h : ℤ, p.2 ≤ h → h ≤ q.2 → ((p.1, h) : GInt) ∈ F2Word.walk c w := by
  intro w
  induction w with
  | nil =>
    intro hw c p q hp hq hpq hle h h1 h2
    simp only [WalkDecomp.walk_nil, List.mem_singleton] at hp hq ⊢
    have e1 : p.1 = c.1 := congrArg Prod.fst hp
    have e2 : p.2 = c.2 := congrArg Prod.snd hp
    have e3 : q.2 = c.2 := congrArg Prod.snd hq
    have hh : h = c.2 := by omega
    exact Prod.ext e1 hh
  | cons x w ih =>
    intro hw c p q hp hq hpq hle h h1 h2
    have hx : x = Unit4.one ∨ x = Unit4.i := hw x (by simp)
    have hw' : ∀ y ∈ w, y = Unit4.one ∨ y = Unit4.i := fun y hy => hw y (by simp [hy])
    rw [WalkDecomp.walk_cons] at hp hq ⊢
    rw [List.mem_cons] at hp hq ⊢
    rcases hx with hx1 | hx1 <;> subst hx1
    · -- the first step is horizontal: every later point lies strictly to the right of `c`
      rcases hp with hpc | hp <;> rcases hq with hqc | hq
      · have e1 : p.1 = c.1 := congrArg Prod.fst hpc
        have e2 : p.2 = c.2 := congrArg Prod.snd hpc
        have e3 : q.2 = c.2 := congrArg Prod.snd hqc
        have hh : h = c.2 := by omega
        exact Or.inl (Prod.ext e1 hh)
      · have e1 : p.1 = c.1 := congrArg Prod.fst hpc
        have := (walk_ge_start w hw' (c + Unit4.one.vec) q hq).1
        rw [vec_one_fst] at this
        omega
      · have e1 : q.1 = c.1 := congrArg Prod.fst hqc
        have := (walk_ge_start w hw' (c + Unit4.one.vec) p hp).1
        rw [vec_one_fst] at this
        omega
      · exact Or.inr (ih hw' (c + Unit4.one.vec) p q hp hq hpq hle h h1 h2)
    · -- the first step is vertical: the column of `c` continues through `c + i`
      rcases hp with hpc | hp <;> rcases hq with hqc | hq
      · have e1 : p.1 = c.1 := congrArg Prod.fst hpc
        have e2 : p.2 = c.2 := congrArg Prod.snd hpc
        have e3 : q.2 = c.2 := congrArg Prod.snd hqc
        have hh : h = c.2 := by omega
        exact Or.inl (Prod.ext e1 hh)
      · have e1 : p.1 = c.1 := congrArg Prod.fst hpc
        have e2 : p.2 = c.2 := congrArg Prod.snd hpc
        by_cases hhc : h = c.2
        · exact Or.inl (Prod.ext e1 hhc)
        · have hcq := walk_ge_start w hw' (c + Unit4.i.vec) q hq
          rw [vec_i_fst, vec_i_snd] at hcq
          have hwin := ih hw' (c + Unit4.i.vec) (c + Unit4.i.vec) q (walk_head_mem _ w) hq
            (by rw [vec_i_fst]; omega) (by rw [vec_i_snd]; omega) h
            (by rw [vec_i_snd]; omega) h2
          rw [vec_i_fst] at hwin
          exact Or.inr (by rw [e1]; exact hwin)
      · have e1 : q.1 = c.1 := congrArg Prod.fst hqc
        have e3 : q.2 = c.2 := congrArg Prod.snd hqc
        have := (walk_ge_start w hw' (c + Unit4.i.vec) p hp).2
        rw [vec_i_snd] at this
        omega
      · exact Or.inr (ih hw' (c + Unit4.i.vec) p q hp hq hpq hle h h1 h2)

end FLatticePaper.Tiles.StackedColumns
