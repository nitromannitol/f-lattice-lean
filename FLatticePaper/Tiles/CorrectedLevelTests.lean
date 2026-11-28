import FLatticePaper.Tiles.CorrectedFaceBounds

/-! Linear inequalities available from either sign of a bounded determinant test. -/

namespace FLatticePaper.Tiles.CorrectedLevelTests

open CorrectedFaceBounds (Cut)

/-- A projected determinant face. The horizontal or vertical case has just the signed distance. -/
inductive Line where
  | flat (w : ℤ)
  | sloped (w width value : ℤ)

/-- Membership of an integer site on the inward side of a projected face at cutoff four. -/
def Line.holds : Line → Prop
  | .flat w => 0 ≤ w
  | .sloped w W v => 4 < w ∨ ∃ l : ℤ, -4 ≤ l ∧ l ≤ 4 ∧ w=l ∧ v ≤ l*W

def Line.valid : Line → Prop
  | .flat _ => True
  | .sloped _ W _ => 0 ≤ W

/-- For a positive or negative test, the zeroth constraint is the one unconditional bound. The
remaining nine constraints describe the integer levels from minus four through four. -/
def Line.fact (l : Line) (inside : Bool) (i : ℕ) : Prop :=
  match l with
  | .flat w => if inside then 0 ≤ w else w < 0
  | .sloped w W v =>
    let level := (i : ℤ)-5
    if i=0 then (if inside then -4 ≤ w else w ≤ 4)
    else if inside then level < w ∨ v ≤ level*W else w < level ∨ level*W < v

theorem Line.facts (l : Line) (valid : l.valid) (sign : Bool)
    (h : if sign then l.holds else ¬l.holds) (i : ℕ) (hi : i ≤ 9) : l.fact sign i := by
  cases l with
  | flat w => cases sign <;> simp_all [Line.holds,Line.fact]
  | sloped w W v =>
    change 0 ≤ W at valid
    cases sign
    · simp only [Bool.false_eq_true,if_false,Line.holds] at h
      unfold Line.fact
      by_cases zero : i=0
      · simpa only [zero,if_true,Bool.false_eq_true,if_false] using (show w ≤ 4 by by_contra! e; exact h (Or.inl e))
      · simp only [zero,if_false,Bool.false_eq_true]
        by_contra! bad
        have hw : w ≤ 4 := by by_contra! e; exact h (Or.inl e)
        have q := mul_le_mul_of_nonneg_right bad.1 valid
        exact h (Or.inr ⟨w,by omega,hw,rfl,bad.2.trans q⟩)
    · simp only [if_true,Line.holds] at h
      unfold Line.fact
      by_cases zero : i=0
      · simp only [zero,if_true]
        rcases h with e|⟨j,jl,ju,rfl,_⟩ <;> omega
      · simp only [zero,if_false,if_true]
        rcases h with e|⟨j,_,_,rfl,e⟩
        · left; omega
        · by_cases hj : (i : ℤ)-5 < w
          · exact Or.inl hj
          · exact Or.inr (e.trans (mul_le_mul_of_nonneg_right (by omega) valid))

/-- The flat and nonflat records both implement the finite face test in the projection theorem. -/
theorem holds_of_cut (W k w v : ℤ) (hw : 0 < W) :
    Cut 4 ⟨W,k,0⟩ w v ↔ (if k=0 then Line.flat w else Line.sloped w W (k*v)).holds := by
  by_cases hk : k=0
  · subst k
    simp only [if_true,Line.holds,Cut,zero_mul]
    constructor
    · rintro (h|⟨l,_,_,rfl,hl⟩)
      · omega
      · by_contra! le
        exact (not_lt_of_ge hl) (mul_neg_of_neg_of_pos le hw)
    · intro h
      by_cases big : 4<w
      · exact Or.inl big
      · exact Or.inr ⟨w,by omega,by omega,rfl,mul_nonneg h hw.le⟩
  · simp [hk,Line.holds,Cut]

end FLatticePaper.Tiles.CorrectedLevelTests
