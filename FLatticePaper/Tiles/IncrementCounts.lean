import FLatticePaper.Tiles.BinaryWords

/-! Task 51 (clause (b) from the fix of Q9): the letter counts of the zero-one words of a standard tile.

For a word `u` with parent registers `P = parentsAt u` and quad `Q = quadAt [] u`, the increment sums of the four strings of the
fix are fixed by the fractions `P.current .odd`, `P.current .even` (the child fractions) and the parents `P.odd`, `P.even`:

* `FwdCount f c` (odd type): `#p = den − num`, `#q = 2 num`; so the forward horizontal sum `(2 #p + #q, #q)` of the odd child word is
  `(2 den, 2 num) = 2 (d, n)`, the doubled odd period `U = μ (d, n)` with `μ = 2` (the sum `d + n` of the odd child is odd);
* `EvnCount f c` (even type): `2 #p = den − num`, `#q = num`; so the forward sum of the even child word is `(den, num) = μ (d, n)`
  with `μ = 1`.

The parity of the sums is not an extra hypothesis: the odd child has odd `num + den` and the even child has even `num + den` by the
recursion, so the period multiplier is fixed by the type. The induction is over the appended digit, using `parentsAt_append_singleton`
and `quadAt_append_singleton`. -/

namespace FLatticePaper.Tiles

open Farey

/-- The odd-type count register of a fraction: `#p = den − num` and `#q = 2 num`. -/
def FwdCount (f : Fraction) (c : BinaryWord) : Prop :=
  (c.count Letter.p : ℤ) = f.den - f.num ∧ (c.count Letter.q : ℤ) = 2 * f.num

/-- The even-type count register of a fraction: `2 #p = den − num` and `#q = num`. -/
def EvnCount (f : Fraction) (c : BinaryWord) : Prop :=
  2 * (c.count Letter.p : ℤ) = f.den - f.num ∧ (c.count Letter.q : ℤ) = f.num

/-- The four registers of the quad of `u` against the parent fractions at `u`. -/
def QuadCounts (u : Word) : Prop :=
  FwdCount ((parentsAt u).current .odd) (quadAt [] u).childP ∧
    EvnCount ((parentsAt u).current .even) (quadAt [] u).childQ ∧
    FwdCount (parentsAt u).odd (quadAt [] u).parentP ∧
    EvnCount (parentsAt u).even (quadAt [] u).parentQ

/-- The seed: the registers of the root fractions `0/1` (odd) and `1/1` (even). -/
theorem quadCounts_nil : QuadCounts [] := by
  unfold QuadCounts FwdCount EvnCount
  simp [quadAt_nil, initialQuad, childWords, parentsAt, root, Parents.current, Parents.combine, Parents.walk]


/-- The step by the digit `one`: the odd parent becomes the current odd fraction and the even parent the current even one. -/
theorem quadCounts_snoc_one (u : Word) (h : QuadCounts u) : QuadCounts (u ++ [Digit.one]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FwdCount at h1 h3
  unfold EvnCount at h2 h4
  simp only [Parents.current, Parents.combine] at h1 h2 h3 h4
  have hcount : (u ++ [Digit.one]).count Digit.one = u.count Digit.one + 1 := by simp [List.count_append]
  unfold QuadCounts
  rw [parentsAt_append_singleton, quadAt_append_singleton]
  unfold FwdCount EvnCount at *
  simp only [WordQuad.step, Parents.step, childWords, List.nil_append, Parents.current, Parents.combine,
    hcount]
  split_ifs <;> dsimp only <;> (try simp only [List.count_append, Nat.cast_add]) <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- The step by the digit `two`: the odd parent becomes the current odd fraction; the even parent is kept. -/
theorem quadCounts_snoc_two (u : Word) (h : QuadCounts u) : QuadCounts (u ++ [Digit.two]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FwdCount at h1 h3
  unfold EvnCount at h2 h4
  simp only [Parents.current, Parents.combine] at h1 h2 h3 h4
  have hcount : (u ++ [Digit.two]).count Digit.one = u.count Digit.one := by simp [List.count_append]
  unfold QuadCounts
  rw [parentsAt_append_singleton, quadAt_append_singleton]
  unfold FwdCount EvnCount at *
  simp only [WordQuad.step, Parents.step, childWords, List.nil_append, Parents.current, Parents.combine,
    hcount]
  split_ifs <;> dsimp only <;> (try simp only [List.count_append, Nat.cast_add]) <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- The step by the digit `three`: the even parent becomes the current even fraction; the odd parent is kept. -/
theorem quadCounts_snoc_three (u : Word) (h : QuadCounts u) : QuadCounts (u ++ [Digit.three]) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FwdCount at h1 h3
  unfold EvnCount at h2 h4
  simp only [Parents.current, Parents.combine] at h1 h2 h3 h4
  have hcount : (u ++ [Digit.three]).count Digit.one = u.count Digit.one := by simp [List.count_append]
  unfold QuadCounts
  rw [parentsAt_append_singleton, quadAt_append_singleton]
  unfold FwdCount EvnCount at *
  simp only [WordQuad.step, Parents.step, childWords, List.nil_append, Parents.current, Parents.combine,
    hcount]
  split_ifs <;> dsimp only <;> (try simp only [List.count_append, Nat.cast_add]) <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- The register invariant holds at every word, by induction over the appended digit. -/
theorem quadCounts_all (u : Word) : QuadCounts u := by
  induction u using List.reverseRecOn with
  | nil => exact quadCounts_nil
  | append_singleton u d ih =>
    cases d with
    | one => exact quadCounts_snoc_one u ih
    | two => exact quadCounts_snoc_two u ih
    | three => exact quadCounts_snoc_three u ih

end FLatticePaper.Tiles
