import FLatticePaper.Farey.Recursion

namespace FLatticePaper.Tiles
open Farey

inductive Letter
  | p | q
  deriving DecidableEq, Repr

abbrev BinaryWord := List Letter

/-- The child operator `C_{(w)}(p_t,q_t)` on binary words; the case is the parity of the number of ones in `w`. -/
def childWords (word : Word) (pw qw : BinaryWord) : BinaryWord × BinaryWord :=
  if word.count .one % 2 = 0 then (qw ++ qw ++ pw, qw ++ pw) else (pw ++ qw ++ qw, pw ++ qw)

/-- A binary word quadruple `(p_{t+1}, q_{t+1}, p_t, q_t)`. -/
structure WordQuad where
  childP : BinaryWord
  childQ : BinaryWord
  parentP : BinaryWord
  parentQ : BinaryWord
  deriving DecidableEq, Repr

/-- `Q_{(w_0)} = (C_{w_0}(p,q), p, q)`. -/
def initialQuad (w0 : Word) : WordQuad :=
  ⟨(childWords w0 [.p] [.q]).1, (childWords w0 [.p] [.q]).2, [.p], [.q]⟩

/-- One step of `eq:child_farey_quad_continuedfrac`, from `Q_{(w)}` to `Q_{(w*digit)}`. -/
def WordQuad.step (w : Word) (quad : WordQuad) : Digit → WordQuad
  | .one => ⟨(childWords (w ++ [Digit.one]) quad.childP quad.childQ).1,
      (childWords (w ++ [Digit.one]) quad.childP quad.childQ).2, quad.childP, quad.childQ⟩
  | .two => ⟨(childWords (w ++ [Digit.two]) quad.childP quad.parentQ).1,
      (childWords (w ++ [Digit.two]) quad.childP quad.parentQ).2, quad.childP, quad.parentQ⟩
  | .three => ⟨(childWords (w ++ [Digit.three]) quad.parentP quad.childQ).1,
      (childWords (w ++ [Digit.three]) quad.parentP quad.childQ).2, quad.parentP, quad.childQ⟩

/-- `Q_{(w_0 u)}` for an extension `u` of `w_0`, built digit by digit. -/
def quadAt (w0 u : Word) : WordQuad :=
  (u.foldl (fun (acc : Word × WordQuad) digit => (acc.1 ++ [digit], acc.2.step acc.1 digit))
    (w0, initialQuad w0)).2

def IsAlmostPalindrome (w : BinaryWord) : Prop :=
  ∃ (first last : Letter) (middle : BinaryWord), middle.reverse = middle ∧ w = first :: (middle ++ [last])

/-- `w[2:n]`: the letters in positions `2, …, n`, counted from one. -/
def slice2 (w : BinaryWord) (n : ℕ) : BinaryWord := (w.drop 1).take (n - 1)

theorem quadAt_nil (w0 : Word) : quadAt w0 [] = initialQuad w0 := rfl

/-- The word component of the accumulator grows by the appended digits. -/
theorem foldl_fst (u : Word) (acc : Word × WordQuad) :
    (u.foldl (fun (acc : Word × WordQuad) digit => (acc.1 ++ [digit], acc.2.step acc.1 digit)) acc).1
      = acc.1 ++ u := by
  induction u generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih]
    simp

theorem quadAt_append_singleton (w0 u : Word) (d : Digit) :
    quadAt w0 (u ++ [d]) = (quadAt w0 u).step (w0 ++ u) d := by
  have h := foldl_fst u (w0, initialQuad w0)
  unfold quadAt at *
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h]

theorem childWords_congr {w w' : Word} (h : w.count .one % 2 = w'.count .one % 2)
    (pw qw : BinaryWord) : childWords w pw qw = childWords w' pw qw := by
  unfold childWords
  rw [h]

theorem WordQuad.step_congr {w w' : Word} (h : w.count .one % 2 = w'.count .one % 2)
    (quad : WordQuad) (d : Digit) : quad.step w d = quad.step w' d := by
  have h1 : (w ++ [Digit.one]).count .one % 2 = (w' ++ [Digit.one]).count .one % 2 := by
    simp [List.count_append] <;> omega
  have h2 : (w ++ [Digit.two]).count .one % 2 = (w' ++ [Digit.two]).count .one % 2 := by
    simp [List.count_append] <;> omega
  have h3 : (w ++ [Digit.three]).count .one % 2 = (w' ++ [Digit.three]).count .one % 2 := by
    simp [List.count_append] <;> omega
  cases d
  · simp only [WordQuad.step, childWords_congr h1]
  · simp only [WordQuad.step, childWords_congr h2]
  · simp only [WordQuad.step, childWords_congr h3]

/-- `Q_{(w_0 u)}` depends on `w_0` only through the parity of its ones. -/
theorem quadAt_congr {w0 w0' : Word} (h : w0.count .one % 2 = w0'.count .one % 2) (u : Word) :
    quadAt w0 u = quadAt w0' u := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [quadAt_nil, quadAt_nil]
    unfold initialQuad
    rw [childWords_congr h]
  | append_singleton u d ih =>
    have h' : (w0 ++ u).count .one % 2 = (w0' ++ u).count .one % 2 := by
      simp only [List.count_append]; omega
    rw [quadAt_append_singleton, quadAt_append_singleton, ih, WordQuad.step_congr h']

/-- Reversing every word of a quadruple. -/
def WordQuad.rev (quad : WordQuad) : WordQuad :=
  ⟨quad.childP.reverse, quad.childQ.reverse, quad.parentP.reverse, quad.parentQ.reverse⟩

/-- Reversal exchanges the two parities of the child operator. -/
theorem childWords_reverse (w : Word) (X Y : BinaryWord) :
    childWords (.one :: w) X.reverse Y.reverse
      = ((childWords w X Y).1.reverse, (childWords w X Y).2.reverse) := by
  unfold childWords
  rw [List.count_cons_self]
  split_ifs <;> first | (exfalso; omega) | simp [List.reverse_append, List.append_assoc]

theorem WordQuad.rev_step (w : Word) (quad : WordQuad) (d : Digit) :
    quad.rev.step ([Digit.one] ++ w) d = (quad.step w d).rev := by
  cases d with
  | one =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.one]) quad.childP quad.childQ]
  | two =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.two]) quad.childP quad.parentQ]
  | three =>
    simp only [WordQuad.step, WordQuad.rev, List.cons_append, List.nil_append]
    rw [childWords_reverse (w ++ [Digit.three]) quad.parentP quad.childQ]

/-- The odd-root family is the reversal of the even-root family. -/
theorem quadAt_one_eq_rev (u : Word) : quadAt [Digit.one] u = (quadAt [] u).rev := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [quadAt_nil, quadAt_nil]
    have hc : childWords [Digit.one] [.p] [.q]
        = ((childWords [] [.p] [.q]).1.reverse, (childWords [] [.p] [.q]).2.reverse) := by
      have := childWords_reverse [] [.p] [.q]
      simpa using this
    unfold initialQuad WordQuad.rev
    rw [hc]
    simp
  | append_singleton u d ih =>
    rw [quadAt_append_singleton, quadAt_append_singleton, ih, WordQuad.rev_step, List.nil_append]

end FLatticePaper.Tiles
