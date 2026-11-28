import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.JointRot

/-! # The boundary words of a standard child in the words of its registers

For a word `w` that is not a base word, with registers `u1`, `u2` (`regsAt w = (some u1, some u2)`), the horizontal words of the
two children are the child operator (`childWords`) applied to the horizontal words of the registers, and the vertical words of
the two children are the child operator applied to the vertical words of the registers in the other order:

* `hWordOf_child`: `hWordOf w false`, `hWordOf w true` are the two child words of `(hWordOf u1 false, hWordOf u2 true)`;
* `vWordOf_child`: `vWordOf w false`, `vWordOf w true` are the second and the first child words of
  `(vWordOf u2 true, vWordOf u1 false)` (through `swapW`, which exchanges the registers, `JointRot.regsAt_swapW`).

The register of a prefix is the source of its parent word (`srcOf_of_regsAt`), so the parent words of `quadAt [] w` are the
child words of the registers (`RegisterLink.parentP_eq_childP_srcOf`). -/

namespace FLatticePaper.Tiles.GlueWords

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RecursionIdentity
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regRun regStep)

/-- The register run and the source run agree on the registers that are set. -/
theorem srcFrom_of_regRun (rest : Word) : ∀ (pre : Word) (r : Option Word × Option Word) (s : Word × Word) (a b : Word),
    (∀ x, r.1 = some x → x = s.1) → (∀ x, r.2 = some x → x = s.2) →
    regRun pre rest r = (some a, some b) → srcFrom pre rest s = (a, b) := by
  induction rest with
  | nil =>
    intro pre r s a b h1 h2 h
    simp only [regRun] at h
    simp only [srcFrom]
    rw [h] at h1 h2
    exact Prod.ext (h1 a rfl).symm (h2 b rfl).symm
  | cons d rest ih =>
    intro pre r s a b h1 h2 h
    simp only [regRun] at h
    simp only [srcFrom]
    refine ih (pre ++ [d]) _ _ a b ?_ ?_ h
    · intro x hx
      cases d with
      | one => simp [regStep] at hx; simp [hx]
      | two => simp [regStep] at hx; simp [hx]
      | three => simp only [regStep] at hx; simpa using h1 x hx
    · intro x hx
      cases d with
      | one => simp [regStep] at hx; simp [hx]
      | two => simp only [regStep] at hx; simpa using h2 x hx
      | three => simp [regStep] at hx; simp [hx]

/-- The sources of the parent words are the registers. -/
theorem srcOf_of_regsAt (w u1 u2 : Word) (h : regsAt w = (some u1, some u2)) : srcOf w = (u1, u2) :=
  srcFrom_of_regRun w [] (none, none) ([], []) u1 u2 (fun _ hx => by simp at hx) (fun _ hx => by simp at hx) h

theorem regRun_fst_threes (rest : Word) : ∀ (pre : Word) (r : Option Word × Option Word),
    (∀ d ∈ rest, d = Digit.three) → (regRun pre rest r).1 = r.1 := by
  induction rest with
  | nil => intro pre r _; rfl
  | cons d rest ih =>
    intro pre r h
    simp only [regRun]
    rw [ih _ _ (fun e he => h e (List.mem_cons_of_mem d he))]
    rw [h d (List.mem_cons_self)]
    rfl

theorem regRun_snd_twos (rest : Word) : ∀ (pre : Word) (r : Option Word × Option Word),
    (∀ d ∈ rest, d = Digit.two) → (regRun pre rest r).2 = r.2 := by
  induction rest with
  | nil => intro pre r _; rfl
  | cons d rest ih =>
    intro pre r h
    simp only [regRun]
    rw [ih _ _ (fun e he => h e (List.mem_cons_of_mem d he))]
    rw [h d (List.mem_cons_self)]
    rfl

theorem exists_one_two (w u1 : Word) (h : (regsAt w).1 = some u1) : ∃ y ∈ w, y = Digit.one ∨ y = Digit.two := by
  by_contra hn
  simp only [not_exists, not_and, not_or] at hn
  have h3 : ∀ d ∈ w, d = Digit.three := by
    intro d hd
    obtain ⟨h1, h2⟩ := hn d hd
    cases d <;> simp_all
  have := regRun_fst_threes w [] (none, none) h3
  rw [show regRun [] w (none, none) = regsAt w from rfl, h] at this
  simp at this

theorem exists_one_three (w u2 : Word) (h : (regsAt w).2 = some u2) : ∃ y ∈ w, y = Digit.one ∨ y = Digit.three := by
  by_contra hn
  simp only [not_exists, not_and, not_or] at hn
  have h2 : ∀ d ∈ w, d = Digit.two := by
    intro d hd
    obtain ⟨h1, h3⟩ := hn d hd
    cases d <;> simp_all
  have := regRun_snd_twos w [] (none, none) h2
  rw [show regRun [] w (none, none) = regsAt w from rfl, h] at this
  simp at this

/-- The parent words of `w` are the horizontal words of its registers. -/
theorem parents_of_regsAt (w u1 u2 : Word) (h : regsAt w = (some u1, some u2)) :
    (quadAt [] w).parentP = hWordOf u1 false ∧ (quadAt [] w).parentQ = hWordOf u2 true := by
  have hs := srcOf_of_regsAt w u1 u2 h
  constructor
  · rw [RegisterLink.parentP_eq_childP_srcOf w (exists_one_two w u1 (by rw [h])), hs]
    rfl
  · rw [RegisterLink.parentQ_eq_childQ_srcOf w (exists_one_three w u2 (by rw [h])), hs]
    rfl

/-- **The horizontal words of the children** are the child words of the horizontal words of the registers. -/
theorem hWordOf_child (w u1 u2 : Word) (h : regsAt w = (some u1, some u2)) :
    hWordOf w false = (childWords w (hWordOf u1 false) (hWordOf u2 true)).1 ∧
      hWordOf w true = (childWords w (hWordOf u1 false) (hWordOf u2 true)).2 := by
  obtain ⟨hP, hQ⟩ := parents_of_regsAt w u1 u2 h
  obtain ⟨c1, c2⟩ := RegisterLink.childPQ_eq w
  rw [hP, hQ] at c1 c2
  exact ⟨c1, c2⟩

theorem count_one_swapW (w : Word) : (Standard.swapW w).count Digit.one = w.count Digit.one := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    show (d.swapTwoThree :: Standard.swapW w).count Digit.one = (d :: w).count Digit.one
    cases d <;> simp [ih, Digit.swapTwoThree]

/-- **The vertical words of the children** are the child words of the vertical words of the registers, in the other order:
`vWordOf w false` is the second child word and `vWordOf w true` the first, of `(vWordOf u2 true, vWordOf u1 false)`. -/
theorem vWordOf_child (w u1 u2 : Word) (h : regsAt w = (some u1, some u2)) :
    vWordOf w false = (childWords w (vWordOf u2 true) (vWordOf u1 false)).2 ∧
      vWordOf w true = (childWords w (vWordOf u2 true) (vWordOf u1 false)).1 := by
  have hs : regsAt (Standard.swapW w) = (some (Standard.swapW u2), some (Standard.swapW u1)) := by
    rw [JointRot.regsAt_swapW, h]
    rfl
  obtain ⟨hP, hQ⟩ := parents_of_regsAt _ _ _ hs
  obtain ⟨c1, c2⟩ := RegisterLink.childPQ_eq (Standard.swapW w)
  rw [hP, hQ] at c1 c2
  have e1 : vWordOf u1 false = (hWordOf (Standard.swapW u1) true).map swapLetter := rfl
  have e2 : vWordOf u2 true = (hWordOf (Standard.swapW u2) false).map swapLetter := rfl
  have ew1 : vWordOf w false = (quadAt [] (Standard.swapW w)).childQ.map swapLetter := rfl
  have ew2 : vWordOf w true = (quadAt [] (Standard.swapW w)).childP.map swapLetter := rfl
  rw [ew1, ew2, c1, c2, e1, e2]
  unfold childWords
  rw [count_one_swapW]
  split_ifs <;> simp

end FLatticePaper.Tiles.GlueWords
