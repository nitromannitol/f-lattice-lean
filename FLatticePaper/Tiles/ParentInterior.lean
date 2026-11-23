import FLatticePaper.Tiles.CeilWords

/-! Task 53, marksIn (block facts): the Farey parents of a word have strictly interior fractions, except along the boundary words.

For a word `u` with parents `(O, E)` (`parentsAt u`), the current fractions are `O + E` (odd) and `2O + E` (even). The blocks of
the forward horizontal words of `u·d` are ceiling words of these slopes and of the parent slopes. A ceiling word of slope `k/l`
with `1 ≤ k < l` starts with `q` and ends with `p`; the slopes are interior exactly when `1 ≤ num < den`.

* `strict_all`: every word has a lower-strict parent (`1 ≤ O.num` or `1 ≤ E.num`) and an upper-strict one (`O.num < O.den` or
  `E.num < E.den`). This makes the current fractions interior.
* `even_int_or`: the even parent is interior, unless the word is a power of `2` (all letters `two`).
* `odd_int_or`: the odd parent is interior, unless the word is a power of `3` (all letters `three`). -/

namespace FLatticePaper.Tiles.ParentInterior

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.CeilWords

/-- A fraction in the open interval: `1 ≤ num < den`. -/
def Inner01 (f : Fraction) : Prop := 1 ≤ f.num ∧ f.num < f.den

/-- Some parent has numerator at least one. -/
def LowerStrict (P : Parents) : Prop := 1 ≤ P.odd.num ∨ 1 ≤ P.even.num

/-- Some parent is strictly below one. -/
def UpperStrict (P : Parents) : Prop := P.odd.num < P.odd.den ∨ P.even.num < P.even.den

theorem strict_root : LowerStrict root ∧ UpperStrict root := by
  constructor
  · right
    simp [root]
  · left
    simp [root]

theorem strict_one (P : Parents) (hv : P.ValidFrame) (hl : LowerStrict P) (hu : UpperStrict P) :
    LowerStrict (Parents.mk (P.current .odd) (P.current .even)) ∧
      UpperStrict (Parents.mk (P.current .odd) (P.current .even)) := by
  obtain ⟨hod, hon, hol⟩ := hv.odd_bounds
  obtain ⟨hed, hen, hel⟩ := hv.even_bounds
  have c1 : (P.current .odd).num = P.odd.num + P.even.num := by simp [Parents.current, Parents.combine]
  have c2 : (P.current .odd).den = P.odd.den + P.even.den := by simp [Parents.current, Parents.combine]
  have c3 : (P.current .even).num = 2 * P.odd.num + P.even.num := by simp [Parents.current, Parents.combine]
  have c4 : (P.current .even).den = 2 * P.odd.den + P.even.den := by simp [Parents.current, Parents.combine]
  dsimp only [LowerStrict, UpperStrict] at hl hu ⊢
  constructor <;> omega

theorem strict_two (P : Parents) (hv : P.ValidFrame) (hl : LowerStrict P) (hu : UpperStrict P) :
    LowerStrict (Parents.mk (P.current .odd) P.even) ∧ UpperStrict (Parents.mk (P.current .odd) P.even) := by
  obtain ⟨hod, hon, hol⟩ := hv.odd_bounds
  obtain ⟨hed, hen, hel⟩ := hv.even_bounds
  have c1 : (P.current .odd).num = P.odd.num + P.even.num := by simp [Parents.current, Parents.combine]
  have c2 : (P.current .odd).den = P.odd.den + P.even.den := by simp [Parents.current, Parents.combine]
  dsimp only [LowerStrict, UpperStrict] at hl hu ⊢
  constructor <;> omega

theorem strict_three (P : Parents) (hv : P.ValidFrame) (hl : LowerStrict P) (hu : UpperStrict P) :
    LowerStrict (Parents.mk P.odd (P.current .even)) ∧ UpperStrict (Parents.mk P.odd (P.current .even)) := by
  obtain ⟨hod, hon, hol⟩ := hv.odd_bounds
  obtain ⟨hed, hen, hel⟩ := hv.even_bounds
  have c3 : (P.current .even).num = 2 * P.odd.num + P.even.num := by simp [Parents.current, Parents.combine]
  have c4 : (P.current .even).den = 2 * P.odd.den + P.even.den := by simp [Parents.current, Parents.combine]
  dsimp only [LowerStrict, UpperStrict] at hl hu ⊢
  constructor <;> omega

/-- Every word has a lower-strict and an upper-strict parent pair. -/
theorem strict_all (u : Word) : LowerStrict (parentsAt u) ∧ UpperStrict (parentsAt u) := by
  induction u using List.reverseRecOn with
  | nil => exact strict_root
  | append_singleton v d ih =>
    have hv := parentsAt_valid v
    cases d with
    | one =>
      rw [parentsAt_snoc_one]
      exact strict_one _ hv ih.1 ih.2
    | two =>
      rw [parentsAt_snoc_two]
      exact strict_two _ hv ih.1 ih.2
    | three =>
      rw [parentsAt_snoc_three]
      exact strict_three _ hv ih.1 ih.2

theorem inner_cur_odd (v : Word) : Inner01 ((parentsAt v).current .odd) := by
  have hv := parentsAt_valid v
  obtain ⟨hod, hon, hol⟩ := hv.odd_bounds
  obtain ⟨hed, hen, hel⟩ := hv.even_bounds
  obtain ⟨hL, hU⟩ := strict_all v
  have c1 : ((parentsAt v).current .odd).num = (parentsAt v).odd.num + (parentsAt v).even.num := by
    simp [Parents.current, Parents.combine]
  have c2 : ((parentsAt v).current .odd).den = (parentsAt v).odd.den + (parentsAt v).even.den := by
    simp [Parents.current, Parents.combine]
  dsimp only [Inner01, LowerStrict, UpperStrict] at hL hU ⊢
  constructor <;> omega

theorem inner_cur_even (v : Word) : Inner01 ((parentsAt v).current .even) := by
  have hv := parentsAt_valid v
  obtain ⟨hod, hon, hol⟩ := hv.odd_bounds
  obtain ⟨hed, hen, hel⟩ := hv.even_bounds
  obtain ⟨hL, hU⟩ := strict_all v
  have c3 : ((parentsAt v).current .even).num = 2 * (parentsAt v).odd.num + (parentsAt v).even.num := by
    simp [Parents.current, Parents.combine]
  have c4 : ((parentsAt v).current .even).den = 2 * (parentsAt v).odd.den + (parentsAt v).even.den := by
    simp [Parents.current, Parents.combine]
  dsimp only [Inner01, LowerStrict, UpperStrict] at hL hU ⊢
  constructor <;> omega

/-- The even parent is interior, unless the word is all `two`s. -/
theorem even_int_or (u : Word) : (∀ d ∈ u, d = Digit.two) ∨ Inner01 (parentsAt u).even := by
  induction u using List.reverseRecOn with
  | nil => exact Or.inl (by simp)
  | append_singleton v d ih =>
    cases d with
    | one =>
      right
      rw [parentsAt_snoc_one]
      exact inner_cur_even v
    | two =>
      rw [parentsAt_snoc_two]
      rcases ih with h | h
      · left
        intro x hx
        rcases List.mem_append.1 hx with h' | h'
        · exact h x h'
        · simp at h'
          exact h'
      · right
        exact h
    | three =>
      right
      rw [parentsAt_snoc_three]
      exact inner_cur_even v

/-- The odd parent is interior, unless the word is all `three`s. -/
theorem odd_int_or (u : Word) : (∀ d ∈ u, d = Digit.three) ∨ Inner01 (parentsAt u).odd := by
  induction u using List.reverseRecOn with
  | nil => exact Or.inl (by simp)
  | append_singleton v d ih =>
    cases d with
    | one =>
      right
      rw [parentsAt_snoc_one]
      exact inner_cur_odd v
    | two =>
      right
      rw [parentsAt_snoc_two]
      exact inner_cur_odd v
    | three =>
      rw [parentsAt_snoc_three]
      rcases ih with h | h
      · left
        intro x hx
        rcases List.mem_append.1 hx with h' | h'
        · exact h x h'
        · simp at h'
          exact h'
      · right
        exact h

theorem even_inner_of_not_twos (u : Word) (h : ¬ ∀ d ∈ u, d = Digit.two) :
    Inner01 (parentsAt u).even :=
  (even_int_or u).resolve_left h

theorem odd_inner_of_not_threes (u : Word) (h : ¬ ∀ d ∈ u, d = Digit.three) :
    Inner01 (parentsAt u).odd :=
  (odd_int_or u).resolve_left h

end FLatticePaper.Tiles.ParentInterior
