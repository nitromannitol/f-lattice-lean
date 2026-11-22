import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.BinaryWords

/-! Task 51, admissibility, part 1: list lemmas over `F2Word`.

The bottom edges are the images of binary words under the augmented token morphism `muOf A B`
(`p ↦ A`, `q ↦ B`, the tokens being the augmented edges `w ++ [i]`). This file proves the
palindrome transfer for these images and the `IFollowedBy` bookkeeping. -/

namespace FLatticePaper.Tiles
open Farey

/-- The augmented token of a binary letter: `p ↦ A`, `q ↦ B`. -/
def tokOf (A B : F2Word) : Letter → F2Word
  | .p => A
  | .q => B

/-- The augmented morphism on binary words. -/
def muOf (A B : F2Word) : BinaryWord → F2Word
  | [] => []
  | c :: x => tokOf A B c ++ muOf A B x

theorem muOf_append (A B : F2Word) (x y : BinaryWord) :
    muOf A B (x ++ y) = muOf A B x ++ muOf A B y := by
  induction x with
  | nil => simp [muOf]
  | cons c x ih => simp [muOf, ih, List.append_assoc]

theorem muOf_singleton (A B : F2Word) (c : Letter) : muOf A B [c] = tokOf A B c := by
  simp [muOf]

theorem oneI_succ (n : ℕ) : oneI (n + 1) = [Unit4.one, Unit4.i] ++ oneI n := by
  simp [oneI, List.replicate_succ]

theorem oneI_comm (n : ℕ) : oneI n ++ [Unit4.one, Unit4.i] = [Unit4.one, Unit4.i] ++ oneI n := by
  induction n with
  | zero => simp [oneI]
  | succ n ih =>
    rw [oneI_succ]
    simp only [List.append_assoc, ih]

/-- `[1] ++ (1 i)^n` reversed is `(1 i)^n ++ [1]`: the word `(1 i)^n 1` is a palindrome up to the first letter. -/
theorem one_rev_oneI (n : ℕ) : [Unit4.one] ++ (oneI n).reverse = oneI n ++ [Unit4.one] := by
  induction n with
  | zero => simp [oneI]
  | succ n ih =>
    rw [oneI_succ]
    have h := oneI_comm n
    calc [Unit4.one] ++ ([Unit4.one, Unit4.i] ++ oneI n).reverse
        = [Unit4.one] ++ ((oneI n).reverse ++ [Unit4.i, Unit4.one]) := by simp
      _ = ([Unit4.one] ++ (oneI n).reverse) ++ [Unit4.i, Unit4.one] := by simp
      _ = (oneI n ++ [Unit4.one]) ++ [Unit4.i, Unit4.one] := by rw [ih]
      _ = oneI n ++ ([Unit4.one, Unit4.i] ++ [Unit4.one]) := by simp
      _ = (oneI n ++ [Unit4.one, Unit4.i]) ++ [Unit4.one] := by simp
      _ = ([Unit4.one, Unit4.i] ++ oneI n) ++ [Unit4.one] := by rw [h]
      _ = oneI (n + 1) ++ [Unit4.one] := by rw [oneI_succ]

/-- The block `1 (1 i)^n 1 1` is a palindrome. -/
theorem block_rev (n : ℕ) :
    ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one]).reverse = [Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one] := by
  have h := one_rev_oneI n
  calc ([Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one]).reverse
      = [Unit4.one, Unit4.one] ++ (oneI n).reverse ++ [Unit4.one] := by simp
    _ = [Unit4.one] ++ ([Unit4.one] ++ (oneI n).reverse) ++ [Unit4.one] := by simp
    _ = [Unit4.one] ++ (oneI n ++ [Unit4.one]) ++ [Unit4.one] := by rw [h]
    _ = [Unit4.one] ++ oneI n ++ [Unit4.one, Unit4.one] := by simp

/-- The Z-form transfer: when both tokens satisfy `rev T ++ Z = Z ++ T`, the reversal of `μ x` is
`μ (rev x)` moved past `Z`. -/
theorem muOf_rev_Z (A B Z : F2Word) (hA : A.reverse ++ Z = Z ++ A) (hB : B.reverse ++ Z = Z ++ B) :
    ∀ x : BinaryWord, (muOf A B x).reverse ++ Z = Z ++ muOf A B x.reverse := by
  intro x
  induction x with
  | nil => simp [muOf]
  | cons c x ih =>
    have ht : (tokOf A B c).reverse ++ Z = Z ++ tokOf A B c := by
      cases c with
      | p => exact hA
      | q => exact hB
    have hr : muOf A B (c :: x).reverse = muOf A B x.reverse ++ tokOf A B c := by
      rw [List.reverse_cons, muOf_append, muOf_singleton]
    rw [hr]
    simp only [muOf, List.reverse_append]
    calc (muOf A B x).reverse ++ (tokOf A B c).reverse ++ Z
        = (muOf A B x).reverse ++ ((tokOf A B c).reverse ++ Z) := by simp only [List.append_assoc]
      _ = (muOf A B x).reverse ++ (Z ++ tokOf A B c) := by rw [ht]
      _ = ((muOf A B x).reverse ++ Z) ++ tokOf A B c := by simp only [List.append_assoc]
      _ = (Z ++ muOf A B x.reverse) ++ tokOf A B c := by rw [ih]
      _ = Z ++ (muOf A B x.reverse ++ tokOf A B c) := by simp only [List.append_assoc]

/-- The Y-form transfer: when both tokens satisfy `Y ++ rev T = T ++ Y`, the same holds for `μ x`. -/
theorem muOf_rev_Y (A B Y : F2Word) (hA : Y ++ A.reverse = A ++ Y) (hB : Y ++ B.reverse = B ++ Y) :
    ∀ x : BinaryWord, Y ++ (muOf A B x).reverse = muOf A B x.reverse ++ Y := by
  intro x
  induction x with
  | nil => simp [muOf]
  | cons c x ih =>
    have ht : Y ++ (tokOf A B c).reverse = tokOf A B c ++ Y := by
      cases c with
      | p => exact hA
      | q => exact hB
    have hr : muOf A B (c :: x).reverse = muOf A B x.reverse ++ tokOf A B c := by
      rw [List.reverse_cons, muOf_append, muOf_singleton]
    rw [hr]
    simp only [muOf, List.reverse_append]
    calc Y ++ ((muOf A B x).reverse ++ (tokOf A B c).reverse)
        = (Y ++ (muOf A B x).reverse) ++ (tokOf A B c).reverse := by simp only [List.append_assoc]
      _ = (muOf A B x.reverse ++ Y) ++ (tokOf A B c).reverse := by rw [ih]
      _ = muOf A B x.reverse ++ (Y ++ (tokOf A B c).reverse) := by simp only [List.append_assoc]
      _ = muOf A B x.reverse ++ (tokOf A B c ++ Y) := by rw [ht]
      _ = muOf A B x.reverse ++ tokOf A B c ++ Y := by simp only [List.append_assoc]

/-! ### `IFollowedBy` bookkeeping -/

theorem ifb_nil (k : ℕ) : IFollowedBy k [] := by
  intro j hj
  simp at hj

theorem ifb_cons_one (k : ℕ) (w : F2Word) : IFollowedBy k (Unit4.one :: w) ↔ IFollowedBy k w := by
  constructor
  · intro h j hj m hm
    have h1 := h (j + 1) (by rw [List.getElem?_cons_succ]; exact hj) m hm
    rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ] at h1
    exact h1
  · intro h j hj m hm
    cases j with
    | zero => simp at hj
    | succ j =>
      have h3 := h j (by rw [List.getElem?_cons_succ] at hj; exact hj) m hm
      rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ]
      exact h3

theorem ifb_cons_ne (k : ℕ) (x : Unit4) (hx : x ≠ Unit4.i) (w : F2Word) :
    IFollowedBy k (x :: w) ↔ IFollowedBy k w := by
  constructor
  · intro h j hj m hm
    have h1 := h (j + 1) (by rw [List.getElem?_cons_succ]; exact hj) m hm
    rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ] at h1
    exact h1
  · intro h j hj m hm
    cases j with
    | zero =>
      rw [List.getElem?_cons_zero] at hj
      exact absurd (Option.some.inj hj) hx
    | succ j =>
      have h3 := h j (by rw [List.getElem?_cons_succ] at hj; exact hj) m hm
      rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ]
      exact h3

theorem ifb_cons_i (k : ℕ) (w : F2Word) :
    IFollowedBy k (Unit4.i :: w) ↔ (∀ m < k, w[m]? = some Unit4.one) ∧ IFollowedBy k w := by
  constructor
  · intro h
    refine ⟨fun m hm => ?_, fun j hj m hm => ?_⟩
    · have h0 := h 0 (by simp) m hm
      rw [show 0 + 1 + m = m + 1 by omega, List.getElem?_cons_succ] at h0
      exact h0
    · have h1 := h (j + 1) (by rw [List.getElem?_cons_succ]; exact hj) m hm
      rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ] at h1
      exact h1
  · rintro ⟨h1, h2⟩ j hj m hm
    cases j with
    | zero =>
      rw [show 0 + 1 + m = m + 1 by omega, List.getElem?_cons_succ]
      exact h1 m hm
    | succ j =>
      have h3 := h2 j (by rw [List.getElem?_cons_succ] at hj; exact hj) m hm
      rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ]
      exact h3

theorem ifb_replicate (k n : ℕ) : IFollowedBy k (List.replicate n Unit4.one) := by
  intro j hj
  rw [List.getElem?_replicate] at hj
  split at hj <;> simp at hj

/-- Gluing: if `T` followed by `k` ones is fine, and `R` is fine and starts with `k` ones, then `T ++ R` is fine. -/
theorem ifb_app (k : ℕ) (T R : F2Word) (hT : IFollowedBy k (T ++ List.replicate k Unit4.one))
    (hR : IFollowedBy k R) (hRk : ∀ m < k, R[m]? = some Unit4.one) : IFollowedBy k (T ++ R) := by
  induction T with
  | nil => simpa using hR
  | cons x T ih =>
    by_cases hx : x = Unit4.i
    · subst hx
      rw [List.cons_append] at hT ⊢
      rw [ifb_cons_i] at hT ⊢
      refine ⟨fun m hm => ?_, ih hT.2⟩
      have h1 := hT.1 m hm
      by_cases hmT : m < T.length
      · rw [List.getElem?_append_left hmT] at h1 ⊢
        exact h1
      · have hle : T.length ≤ m := by omega
        rw [List.getElem?_append_right hle] at h1 ⊢
        have hj : m - T.length < k := by
          by_contra hcon
          simp [hcon] at h1
        exact hRk _ hj
    · rw [List.cons_append] at hT ⊢
      rw [ifb_cons_ne k x hx] at hT ⊢
      exact ih hT

/-- Removing the padding: if `E' ++ 1^k ++ [i] ++ 1^k` is fine then so is `E' ++ 1^k`. -/
theorem ifb_of_pad (k : ℕ) (E' : F2Word)
    (h : IFollowedBy k (E' ++ List.replicate k Unit4.one ++ [Unit4.i] ++ List.replicate k Unit4.one)) :
    IFollowedBy k (E' ++ List.replicate k Unit4.one) := by
  have key : ∀ n, n < E'.length + k →
      (E' ++ List.replicate k Unit4.one ++ [Unit4.i] ++ List.replicate k Unit4.one)[n]?
        = (E' ++ List.replicate k Unit4.one)[n]? := by
    intro n hn
    have h1 : n < (E' ++ List.replicate k Unit4.one ++ [Unit4.i]).length := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
    have h2 : n < (E' ++ List.replicate k Unit4.one).length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [List.getElem?_append_left h1, List.getElem?_append_left h2]
  intro j hj m hm
  have hjE' : j < E'.length := by
    by_contra hcon
    have hle : E'.length ≤ j := by omega
    rw [List.getElem?_append_right hle] at hj
    rw [List.getElem?_replicate] at hj
    split at hj <;> simp at hj
  have hB : (E' ++ List.replicate k Unit4.one ++ [Unit4.i] ++ List.replicate k Unit4.one)[j]?
      = some Unit4.i := by
    rw [key j (by omega)]
    exact hj
  have hbig := h j hB m hm
  rw [key (j + 1 + m) (by omega)] at hbig
  exact hbig

end FLatticePaper.Tiles
