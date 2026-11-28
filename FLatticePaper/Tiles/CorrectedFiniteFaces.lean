import FLatticePaper.Tiles.CorrectedLevelTests

/-! Signed linear tests for any prescribed finite window of determinant levels, and for isolated boundary conditions. -/

namespace FLatticePaper.Tiles.CorrectedFiniteFaces

open CorrectedLevelTests CorrectedFaceBounds

/-- The same inward face at any cutoff. -/
def inside (m : ℤ) : Line → Prop
  | .flat w => 0≤w
  | .sloped w W v => m<w ∨ ∃ l : ℤ, -m≤l ∧ l≤m ∧ w=l ∧ v≤l*W

def fact (m : ℤ) (test : Line) (pos : Bool) (i : ℕ) : Prop :=
  match test with
  | .flat w => if pos then 0≤w else w<0
  | .sloped w W v =>
    let t := (i : ℤ)-m-1
    if i=0 then (if pos then -m≤w else w≤m)
    else if pos then t<w ∨ v≤t*W else w<t ∨ t*W<v

theorem facts (m : ℤ) (t : Line) (valid : t.valid) (pos : Bool)
    (h : if pos then inside m t else ¬inside m t) (i : ℕ) (hi : (i:ℤ)≤2*m+1) : fact m t pos i := by
  cases t with
  | flat w => cases pos <;> simp_all [inside,fact]
  | sloped w W v =>
    change 0≤W at valid
    cases pos
    · change ¬(m<w ∨ ∃ l : ℤ, -m≤l ∧ l≤m ∧ w=l ∧ v≤l*W) at h
      have upper : w≤m := by by_contra! hn; exact h (Or.inl hn)
      by_cases zero : i=0
      · simpa only [fact,zero,if_true,Bool.false_eq_true,if_false] using upper
      · simp only [fact,zero,if_false,Bool.false_eq_true]
        by_contra! miss
        have mul := mul_le_mul_of_nonneg_right miss.1 valid
        exact h (Or.inr ⟨w,by omega,upper,rfl,miss.2.trans mul⟩)
    · change m<w ∨ ∃ l : ℤ, -m≤l ∧ l≤m ∧ w=l ∧ v≤l*W at h
      by_cases zero : i=0
      · simp only [fact,zero,if_true]; rcases h with h|⟨l,_,_,rfl,_⟩ <;> omega
      · simp only [fact,zero,if_false,if_true]
        rcases h with h|⟨l,_,_,rfl,h⟩
        · left; omega
        · by_cases hl : (i:ℤ)-m-1 < w
          · exact Or.inl hl
          · exact Or.inr (h.trans (mul_le_mul_of_nonneg_right (by omega) valid))

/-- The rectangular cutoff used on a sheared base polygon is the same signed level test. -/
theorem inside_iff (m W k w v : ℤ) (hm : 0≤m) (hw : 0<W) :
    Cut m ⟨W,k,0⟩ w v ↔ inside m (if k=0 then .flat w else .sloped w W (k*v)) := by
  by_cases hk : k=0
  · subst k; simp only [if_true,inside,Cut,zero_mul]
    constructor
    · rintro (h|⟨j,_,_,rfl,h⟩)
      · omega
      · by_contra! hn; exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos hn hw)
    · intro h
      by_cases hh : m<w
      · exact Or.inl hh
      · exact Or.inr ⟨w,by omega,by omega,rfl,mul_nonneg h hw.le⟩
  · simp [hk,Cut,inside]

/-- A polygonal face or an explicit condition at a boundary segment or vertex. -/
inductive Test where
  | line (m : ℤ) (l : Line)
  | boundary (P : Prop)

def Test.holds : Test → Prop
  | .line m l => inside m l
  | .boundary P => P

def Test.bound (t : Test) (sgn : Bool) (j : ℕ) : Prop :=
  match t with
  | .line m l => fact m l sgn j
  | .boundary P => if sgn then P else ¬P

def Test.valid (t : Test) (j : ℕ) : Prop :=
  match t with
  | .line m l => l.valid ∧ (j:ℤ)≤2*m+1
  | .boundary _ => True

theorem Test.bounds (t : Test) (sgn : Bool) (j : ℕ) (hv : t.valid j) (h : if sgn then t.holds else ¬t.holds) :
    t.bound sgn j := by
  cases t with
  | line m l => exact facts m l hv.1 sgn h j hv.2
  | boundary p => exact h

end FLatticePaper.Tiles.CorrectedFiniteFaces
