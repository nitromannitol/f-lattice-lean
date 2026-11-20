import FLatticePaper.Construction.BaseRegisters
import FLatticePaper.Farey.Lineage
import Mathlib.Data.List.TakeWhile

namespace FLatticePaper.Construction

open Farey

def BaseRun.word : BaseRun → Word
  | .empty => []
  | .twos extra => List.replicate (extra + 1) .two
  | .threes extra => List.replicate (extra + 1) .three

/-- The maximal initial pure run and the untouched mixed-step suffix.
A word starting with digit one uses the empty initializer. -/
def splitInitial : Word → BaseRun × Word
  | [] => (.empty, [])
  | .one :: rest => (.empty, .one :: rest)
  | .two :: rest => (.twos (rest.takeWhile (fun digit => decide (digit = .two))).length,
      rest.dropWhile (fun digit => decide (digit = .two)))
  | .three :: rest => (.threes (rest.takeWhile (fun digit => decide (digit = .three))).length,
      rest.dropWhile (fun digit => decide (digit = .three)))

private theorem takeWhile_eq_replicate (digit : Digit) (word : Word) :
    let portion := word.takeWhile (fun current => decide (current = digit))
    portion = List.replicate portion.length digit := by
  dsimp only
  apply List.eq_replicate_of_mem
  intro current hm
  exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun letter => decide (letter = digit)) hm)

theorem splitInitial_word (word : Word) :
    (splitInitial word).1.word ++ (splitInitial word).2 = word := by
  cases word with
  | nil => rfl
  | cons digit tail =>
    have key (repeatDigit : Digit) :
        List.replicate ((tail.takeWhile (fun current => decide (current = repeatDigit))).length + 1)
          repeatDigit ++ tail.dropWhile (fun current => decide (current = repeatDigit)) =
          repeatDigit :: tail := by
      rw [List.replicate_succ, ← takeWhile_eq_replicate, List.cons_append,
        List.takeWhile_append_dropWhile]
    cases digit
    · rfl
    · exact key .two
    · exact key .three

/-- Word components of the exact saved-ancestor registers. The current
constructor's correction reads these before pushing the new digit. -/
structure AncestorHistory where
  current : Word
  savedTwo : Word
  savedThree : Word

def AncestorHistory.init (initializer : BaseRun) : AncestorHistory :=
  ⟨initializer.word, initializer.word, initializer.word⟩

def AncestorHistory.push (history : AncestorHistory) (digit : Digit) : AncestorHistory :=
  let next := history.current ++ [digit]
  match digit with
  | .one => ⟨next, next, next⟩
  | .two => ⟨next, history.savedTwo, next⟩
  | .three => ⟨next, next, history.savedThree⟩

def AncestorHistory.walk (history : AncestorHistory) (suffix : Word) : AncestorHistory :=
  suffix.foldl AncestorHistory.push history

theorem AncestorHistory.walk_current (history : AncestorHistory) (suffix : Word) :
    (history.walk suffix).current = history.current ++ suffix := by
  induction suffix generalizing history with
  | nil => simp [AncestorHistory.walk]
  | cons digit tail ih =>
    change ((history.push digit).walk tail).current = _
    rw [ih]
    cases digit <;> simp [AncestorHistory.push, List.append_assoc]

private def AncestorHistory.HasSavedSuffixes (history : AncestorHistory) : Prop :=
  (∃ length, history.current = history.savedTwo ++ List.replicate length .two) ∧
  (∃ length, history.current = history.savedThree ++ List.replicate length .three)

private theorem AncestorHistory.HasSavedSuffixes.push {history : AncestorHistory}
    (h : history.HasSavedSuffixes) (digit : Digit) : (history.push digit).HasSavedSuffixes := by
  obtain ⟨⟨twoLength, htwo⟩, ⟨threeLength, hthree⟩⟩ := h
  cases digit
  · exact ⟨⟨0, by simp [AncestorHistory.push]⟩, ⟨0, by simp [AncestorHistory.push]⟩⟩
  · refine ⟨⟨twoLength + 1, ?_⟩, ⟨0, by simp [AncestorHistory.push]⟩⟩
    change history.current ++ [.two] = history.savedTwo ++ List.replicate (twoLength + 1) .two
    rw [htwo, List.append_assoc, List.replicate_succ']
  · refine ⟨⟨0, by simp [AncestorHistory.push]⟩, ⟨threeLength + 1, ?_⟩⟩
    change history.current ++ [.three] =
      history.savedThree ++ List.replicate (threeLength + 1) .three
    rw [hthree, List.append_assoc, List.replicate_succ']

private theorem AncestorHistory.HasSavedSuffixes.walk {history : AncestorHistory}
    (h : history.HasSavedSuffixes) (suffix : Word) : (history.walk suffix).HasSavedSuffixes := by
  induction suffix generalizing history with
  | nil => exact h
  | cons digit tail ih => exact ih (h.push digit)

def ancestorHistory (word : Word) : AncestorHistory :=
  (AncestorHistory.init (splitInitial word).1).walk (splitInitial word).2

theorem ancestorHistory_current (word : Word) : (ancestorHistory word).current = word := by
  unfold ancestorHistory
  rw [AncestorHistory.walk_current]
  exact splitInitial_word word

private theorem ancestorHistory_savedSuffixes (word : Word) :
    (ancestorHistory word).HasSavedSuffixes := by
  unfold ancestorHistory
  apply AncestorHistory.HasSavedSuffixes.walk
  exact ⟨⟨0, by simp [AncestorHistory.init]⟩, ⟨0, by simp [AncestorHistory.init]⟩⟩

theorem ancestorHistory_two_suffix (word : Word) :
    ∃ length, word = (ancestorHistory word).savedTwo ++ List.replicate length .two := by
  obtain ⟨length, heq⟩ := (ancestorHistory_savedSuffixes word).1
  exact ⟨length, (ancestorHistory_current word).symm.trans heq⟩

theorem ancestorHistory_three_suffix (word : Word) :
    ∃ length, word = (ancestorHistory word).savedThree ++ List.replicate length .three := by
  obtain ⟨length, heq⟩ := (ancestorHistory_savedSuffixes word).2
  exact ⟨length, (ancestorHistory_current word).symm.trans heq⟩

/-- The correction source at an actual mixed-step update, read before pushing
the new digit. Pure initializers are not processed by this update. -/
def AncestorHistory.readCorrection (history : AncestorHistory) : Digit → Option Word
  | .one => none
  | .two => some history.savedTwo
  | .three => some history.savedThree

private theorem AncestorHistory.walk_saved_nonempty {history : AncestorHistory}
    (htwo : history.savedTwo ≠ []) (hthree : history.savedThree ≠ []) (suffix : Word) :
    (history.walk suffix).savedTwo ≠ [] ∧ (history.walk suffix).savedThree ≠ [] := by
  induction suffix generalizing history with
  | nil => exact ⟨htwo, hthree⟩
  | cons digit tail ih =>
    change ((history.push digit).walk tail).savedTwo ≠ [] ∧
      ((history.push digit).walk tail).savedThree ≠ []
    apply ih <;> cases digit <;> simp [AncestorHistory.push, htwo, hthree]

theorem ancestorHistory_saved_nonempty {word : Word} (hne : word ≠ []) :
    (ancestorHistory word).savedTwo ≠ [] ∧ (ancestorHistory word).savedThree ≠ [] := by
  cases word with
  | nil => exact False.elim (hne rfl)
  | cons digit tail =>
    cases digit
    · change (((AncestorHistory.init .empty).push .one).walk tail).savedTwo ≠ [] ∧
        (((AncestorHistory.init .empty).push .one).walk tail).savedThree ≠ []
      exact AncestorHistory.walk_saved_nonempty (by decide) (by decide) tail
    · unfold ancestorHistory
      apply AncestorHistory.walk_saved_nonempty <;>
        simp [AncestorHistory.init, splitInitial, BaseRun.word]
    · unfold ancestorHistory
      apply AncestorHistory.walk_saved_nonempty <;>
        simp [AncestorHistory.init, splitInitial, BaseRun.word]

end FLatticePaper.Construction
