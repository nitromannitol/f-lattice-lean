import FLatticePaper.Tiles.BinaryWords
import FLatticePaper.Farey.Rotation

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


/-! ### The vertical string and the forward increment sums -/

/-- The letter exchange `p ↔ q` of the vertical string (the vertical zero-one string is the child word of the swapped word, with
the letters exchanged). -/
def swapLetter : Letter → Letter
  | .p => .q
  | .q => .p

/-- The vertical zero-one word of the word `u`: the even child word of the two-three swapped word, with the letters exchanged. -/
def vertWord (u : Word) : BinaryWord := (quadAt [] (u.map Digit.swapTwoThree)).childQ.map swapLetter

theorem count_map_swapLetter_p (w : BinaryWord) : (w.map swapLetter).count Letter.p = w.count Letter.q := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [swapLetter, ih]

theorem count_map_swapLetter_q (w : BinaryWord) : (w.map swapLetter).count Letter.q = w.count Letter.p := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [swapLetter, ih]

/-- The parents of the two-three swapped word are the rotated parents (`Parents.ValidFrame.rotate_walk` at the root). -/
theorem parentsAt_map_swap (u : Word) : parentsAt (u.map Digit.swapTwoThree) = (parentsAt u).rotate := by
  have h := Parents.ValidFrame.rotate_walk root_valid u
  have hr : root.rotate = root := rfl
  rw [hr] at h
  exact h.symm

/-- The vertical counts: `#p(vertWord u) = d − n` and `#q(vertWord u) = n`, with `(n, d)` the current odd fraction at `u`. -/
theorem vertWord_counts (u : Word) :
    ((vertWord u).count Letter.p : ℤ) = ((parentsAt u).current .odd).den - ((parentsAt u).current .odd).num ∧
      ((vertWord u).count Letter.q : ℤ) = ((parentsAt u).current .odd).num := by
  have hE := (quadCounts_all (u.map Digit.swapTwoThree)).2.1
  unfold EvnCount at hE
  rw [parentsAt_map_swap] at hE
  have hV := parentsAt_valid u
  have hodd : ((parentsAt u).odd.num + (parentsAt u).odd.den) % 2 = 1 := hV.odd_parity
  have heven : ((parentsAt u).even.num + (parentsAt u).even.den) % 2 = 0 := hV.even_parity
  unfold vertWord
  rw [count_map_swapLetter_p, count_map_swapLetter_q]
  simp only [Parents.rotate, Parents.current, Parents.combine] at hE ⊢
  rw [Fraction.rotate_of_even hV.even_parity, Fraction.rotate_of_odd hV.odd_parity] at hE
  obtain ⟨hE1, hE2⟩ := hE
  dsimp only at hE1 hE2 ⊢
  constructor <;> omega


/-- The increment sum of a zero-one word in the horizontal offsets `p ↦ (2, 0)`, `q ↦ (1, 1)`. -/
def hIncSum (c : BinaryWord) : ℤ × ℤ := (2 * (c.count Letter.p : ℤ) + (c.count Letter.q : ℤ), (c.count Letter.q : ℤ))

/-- **The forward horizontal sum of the odd child word is the doubled odd period** `2 (d, n)`, with `(n, d)` the current odd
fraction at `u` (the sum of the increments equals `U = μ (d, n)` with `μ = 2`). -/
theorem hIncSum_childP (u : Word) :
    hIncSum (quadAt [] u).childP = (2 * ((parentsAt u).current .odd).den, 2 * ((parentsAt u).current .odd).num) := by
  have h := (quadCounts_all u).1
  unfold FwdCount at h
  unfold hIncSum
  obtain ⟨h1, h2⟩ := h
  ext
  · dsimp only; omega
  · dsimp only; omega

/-- **The forward horizontal sum of the even child word is the period** `(d, n)` of the even fraction (`μ = 1`). -/
theorem hIncSum_childQ (u : Word) :
    hIncSum (quadAt [] u).childQ = (((parentsAt u).current .even).den, ((parentsAt u).current .even).num) := by
  have h := (quadCounts_all u).2.1
  unfold EvnCount at h
  unfold hIncSum
  obtain ⟨h1, h2⟩ := h
  ext
  · dsimp only; omega
  · dsimp only; omega

/-- **The reversed vertical last corner**: the vertical increments `#p (−1, 1) + #q (0, 2)` of `vertWord u` sum to
`V = (−C, L)` with `C = d − n` and `L = d + n`, for the odd fraction `(n, d)` at `u`. -/
theorem vertWord_lastCorner (u : Word) :
    (-(vertWord u).count Letter.p : ℤ) = -(((parentsAt u).current .odd).den - ((parentsAt u).current .odd).num) ∧
      ((vertWord u).count Letter.p : ℤ) + 2 * ((vertWord u).count Letter.q : ℤ) =
        ((parentsAt u).current .odd).den + ((parentsAt u).current .odd).num := by
  obtain ⟨h1, h2⟩ := vertWord_counts u
  constructor
  · rw [h1]
  · rw [h1, h2]; ring

end FLatticePaper.Tiles
