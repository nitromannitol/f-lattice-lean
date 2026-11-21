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
  | .one => ⟨(childWords (w ++ [.one]) quad.childP quad.childQ).1,
      (childWords (w ++ [.one]) quad.childP quad.childQ).2, quad.childP, quad.childQ⟩
  | .two => ⟨(childWords (w ++ [.two]) quad.childP quad.parentQ).1,
      (childWords (w ++ [.two]) quad.childP quad.parentQ).2, quad.childP, quad.parentQ⟩
  | .three => ⟨(childWords (w ++ [.three]) quad.parentP quad.childQ).1,
      (childWords (w ++ [.three]) quad.parentP quad.childQ).2, quad.parentP, quad.childQ⟩

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
theorem foldl_fst (w0 u : Word) (acc : Word × WordQuad) :
    (u.foldl (fun (acc : Word × WordQuad) digit => (acc.1 ++ [digit], acc.2.step acc.1 digit)) acc).1
      = acc.1 ++ u := by
  induction u generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih]
    simp

theorem quadAt_append_singleton (w0 u : Word) (d : Digit) :
    quadAt w0 (u ++ [d]) = (quadAt w0 u).step (w0 ++ u) d := by
  have h := foldl_fst w0 u (w0, initialQuad w0)
  unfold quadAt at *
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h]

end FLatticePaper.Tiles
