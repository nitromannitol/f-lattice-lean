import FLatticePaper.Tiles.AdmissibleLists

/-! Task 51, admissibility, part 2: the admissible shapes of `lemma:almost_square_tiling` (cases (b) and (c))
for the augmented-token images, and the `IFollowedBy` facts for their tokens. -/

namespace FLatticePaper.Tiles
open Farey

/-- The word `1^k`, written with the letter `one` only. -/
abbrev rep1 (k : ℕ) : F2Word := List.replicate k Unit4.one

theorem admissible_of_b (E wt : F2Word) (hE : E = [Unit4.one, Unit4.one, Unit4.i] ++ wt ++ [Unit4.one])
    (hwt : wt.reverse = wt) (hifb : IFollowedBy 1 E) (hmono : ∀ x ∈ E, x = Unit4.one ∨ x = Unit4.i) :
    Admissible E := by
  refine ⟨hmono, ?_, ?_, Or.inr (Or.inl ⟨wt, hE, hwt, hifb⟩)⟩
  · rw [hE]; simp
  · rw [hE, List.getLast?_concat]

theorem admissible_of_c (E wt : F2Word) (hE : E = [Unit4.one] ++ wt ++ [Unit4.one, Unit4.one, Unit4.one])
    (hwt : wt.reverse = wt) (hifb : IFollowedBy 3 E) (hmono : ∀ x ∈ E, x = Unit4.one ∨ x = Unit4.i) :
    Admissible E := by
  refine ⟨hmono, ?_, ?_, Or.inr (Or.inr ⟨wt, hE, hwt, hifb⟩)⟩
  · rw [hE]; simp
  · rw [hE, List.getLast?_append_of_ne_nil _ (by simp)]; simp

/-- The letters of a word in `{1, i}`. -/
def OneI (w : F2Word) : Prop := ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.i

theorem oneI_letters (n : ℕ) : OneI (oneI n) := by
  induction n with
  | zero => intro x hx; simp [oneI] at hx
  | succ n ih =>
    intro x hx
    rw [oneI_succ] at hx
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with hx | hx
    · rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact ih x hx

theorem muOf_letters (A B : F2Word) (hA : OneI A) (hB : OneI B) (x : BinaryWord) : OneI (muOf A B x) := by
  induction x with
  | nil => intro y hy; simp [muOf] at hy
  | cons c x ih =>
    intro y hy
    rw [muOf, List.mem_append] at hy
    rcases hy with hy | hy
    · cases c with
      | p => exact hA y hy
      | q => exact hB y hy
    · exact ih y hy

/-- Palindrome of the (b)-middle word `P ++ [1,1,i] ++ Y ++ [1] ++ P ++ [1]` with `P = (1 i)^m`, given the
Z-form identity `rev Y ++ [i] = [i] ++ Y` for the image `Y` of a palindrome. -/
theorem pal_b (m : ℕ) (Y : F2Word) (hY : Y.reverse ++ [Unit4.i] = [Unit4.i] ++ Y) :
    (oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one]).reverse
      = oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one] := by
  have h1 : [Unit4.one] ++ (oneI m).reverse = oneI m ++ [Unit4.one] := one_rev_oneI m
  have hrev : (oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one]).reverse
      = [Unit4.one] ++ (oneI m).reverse ++ [Unit4.one] ++ Y.reverse ++ [Unit4.i, Unit4.one, Unit4.one]
          ++ (oneI m).reverse := by
    simp [List.reverse_append]
  have hA : Y.reverse ++ [Unit4.i, Unit4.one, Unit4.one] ++ (oneI m).reverse
      = [Unit4.i] ++ Y ++ [Unit4.one] ++ (oneI m ++ [Unit4.one]) := by
    rw [show Y.reverse ++ [Unit4.i, Unit4.one, Unit4.one] ++ (oneI m).reverse
        = (Y.reverse ++ [Unit4.i]) ++ ([Unit4.one, Unit4.one] ++ (oneI m).reverse) by simp, hY,
      show [Unit4.one, Unit4.one] ++ (oneI m).reverse = [Unit4.one] ++ ([Unit4.one] ++ (oneI m).reverse) by simp,
      h1]
    simp
  rw [hrev]
  calc [Unit4.one] ++ (oneI m).reverse ++ [Unit4.one] ++ Y.reverse ++ [Unit4.i, Unit4.one, Unit4.one]
          ++ (oneI m).reverse
      = ([Unit4.one] ++ (oneI m).reverse) ++ [Unit4.one]
          ++ (Y.reverse ++ [Unit4.i, Unit4.one, Unit4.one] ++ (oneI m).reverse) := by simp
    _ = (oneI m ++ [Unit4.one]) ++ [Unit4.one] ++ ([Unit4.i] ++ Y ++ [Unit4.one] ++ (oneI m ++ [Unit4.one])) := by
        rw [h1, hA]
    _ = oneI m ++ [Unit4.one, Unit4.one, Unit4.i] ++ Y ++ [Unit4.one] ++ oneI m ++ [Unit4.one] := by simp

/-- Palindrome of the (c)-middle word `1^a i H Y 1^a` with `H = 1^b i`, given the Z-form identity for `Z = i H`. -/
theorem pal_c3 (a b : ℕ) (Y : F2Word)
    (hY : Y.reverse ++ ([Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]))
      = ([Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i])) ++ Y) :
    (List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]) ++ Y
      ++ List.replicate a Unit4.one).reverse
      = List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]) ++ Y
        ++ List.replicate a Unit4.one := by
  have hH : (List.replicate b Unit4.one ++ [Unit4.i]).reverse ++ [Unit4.i]
      = [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]) := by
    simp [List.reverse_replicate]
  calc (List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]) ++ Y
          ++ List.replicate a Unit4.one).reverse
      = List.replicate a Unit4.one ++ (Y.reverse ++ ((List.replicate b Unit4.one ++ [Unit4.i]).reverse
          ++ [Unit4.i])) ++ List.replicate a Unit4.one := by
        simp [List.reverse_replicate, List.append_assoc]
    _ = List.replicate a Unit4.one ++ (Y.reverse ++ ([Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i])))
          ++ List.replicate a Unit4.one := by rw [hH]
    _ = List.replicate a Unit4.one ++ (([Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i])) ++ Y)
          ++ List.replicate a Unit4.one := by rw [hY]
    _ = List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ [Unit4.i]) ++ Y
        ++ List.replicate a Unit4.one := by simp only [List.append_assoc]

/-- Palindrome of the (c)-middle word `1^a i Y 1^b i 1^a` (the even-token case), given the Y-form identity. -/
theorem pal_c_Y (a b : ℕ) (Y : F2Word)
    (hY : List.replicate b Unit4.one ++ Y.reverse = Y ++ List.replicate b Unit4.one) :
    (List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate b Unit4.one ++ [Unit4.i]
      ++ List.replicate a Unit4.one).reverse
      = List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate b Unit4.one ++ [Unit4.i]
        ++ List.replicate a Unit4.one := by
  calc (List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate b Unit4.one ++ [Unit4.i]
          ++ List.replicate a Unit4.one).reverse
      = List.replicate a Unit4.one ++ [Unit4.i] ++ (List.replicate b Unit4.one ++ Y.reverse)
          ++ [Unit4.i] ++ List.replicate a Unit4.one := by
        simp [List.reverse_replicate, List.append_assoc]
    _ = List.replicate a Unit4.one ++ [Unit4.i] ++ (Y ++ List.replicate b Unit4.one) ++ [Unit4.i]
          ++ List.replicate a Unit4.one := by rw [hY]
    _ = List.replicate a Unit4.one ++ [Unit4.i] ++ Y ++ List.replicate b Unit4.one ++ [Unit4.i]
        ++ List.replicate a Unit4.one := by simp only [List.append_assoc]

end FLatticePaper.Tiles
