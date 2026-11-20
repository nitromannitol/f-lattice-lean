import FLattice.Auxiliary.Ceiling
import Mathlib.Data.List.Basic

/-!
# Soundness of finite incoming-average certificates

This module checks finite deductions from explicitly supplied lower bounds.
It is independent of any particular graph, growth condition, or recurrence
definition. Applications must prove the seed inequalities separately.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary

universe u

/-- A claimed integer lower bound at a vertex. -/
abbrev Fact (V : Type u) := V × ℤ

/-- A leaf reads an authorized seed; an average reads two earlier facts. -/
inductive Step (V : Type u) where
  | leaf (seedIndex : ℕ)
  | average (vertex : V) (leftIndex rightIndex : ℕ) (value : ℤ)
  deriving DecidableEq, Repr

variable {V : Type u} [DecidableEq V]

/-- Check one deduction. Invalid indices or an incorrect star are rejected. -/
def evalStep (left right : V → V) (seeds established : List (Fact V)) :
    Step V → Option (Fact V)
  | .leaf index => seeds[index]?
  | .average z i j value =>
      match established[i]?, established[j]? with
      | some a, some b =>
          if a.1 = left z ∧ b.1 = right z ∧ value = ceilHalf (a.2 + b.2) then
            some (z, value)
          else none
      | _, _ => none

/-- Replay a sequence, retaining the literal order of all emitted facts. -/
def runFrom (left right : V → V) (seeds : List (Fact V))
    (established : List (Fact V)) : List (Step V) → Option (List (Fact V))
  | [] => some established
  | step :: rest =>
      match evalStep left right seeds established step with
      | some fact => runFrom left right seeds (established ++ [fact]) rest
      | none => none

/-- Replay a certificate from an empty list of established facts. -/
def run (left right : V → V) (seeds : List (Fact V)) (steps : List (Step V)) :
    Option (List (Fact V)) :=
  runFrom left right seeds [] steps

/-- A successful single deduction is a true bound when its premises are true. -/
theorem evalStep_sound (left right : V → V) (h : V → ℤ)
    (hsuper : ∀ z, h (left z) + h (right z) ≤ 2 * h z)
    (seeds established : List (Fact V))
    (hseeds : ∀ a ∈ seeds, a.2 ≤ h a.1)
    (hestablished : ∀ a ∈ established, a.2 ≤ h a.1)
    (step : Step V) (fact : Fact V)
    (heval : evalStep left right seeds established step = some fact) :
    fact.2 ≤ h fact.1 := by
  cases step with
  | leaf index =>
      exact hseeds fact (List.mem_of_getElem? heval)
  | average z i j value =>
      cases ha : established[i]? with
      | none =>
          simp only [evalStep, ha] at heval
          cases heval
      | some a =>
          cases hb : established[j]? with
          | none =>
              simp only [evalStep, ha, hb] at heval
              cases heval
          | some b =>
              simp only [evalStep, ha, hb] at heval
              split at heval
              next hcheck =>
                have hfact : (z, value) = fact := Option.some.inj heval
                subst fact
                obtain ⟨hl, hr, hv⟩ := hcheck
                have hla := hestablished a (List.mem_of_getElem? ha)
                have hrb := hestablished b (List.mem_of_getElem? hb)
                rw [hl] at hla
                rw [hr] at hrb
                change value ≤ h z
                rw [hv]
                exact ceilHalf_add_le_of_le hla hrb (hsuper z)
              next _ => cases heval

/-- A successful replay preserves the truth of every emitted lower bound. -/
theorem runFrom_sound (left right : V → V) (h : V → ℤ)
    (hsuper : ∀ z, h (left z) + h (right z) ≤ 2 * h z)
    (seeds : List (Fact V)) (hseeds : ∀ a ∈ seeds, a.2 ≤ h a.1)
    (steps : List (Step V)) (established result : List (Fact V))
    (hestablished : ∀ a ∈ established, a.2 ≤ h a.1)
    (hrun : runFrom left right seeds established steps = some result) :
    ∀ a ∈ result, a.2 ≤ h a.1 := by
  induction steps generalizing established with
  | nil =>
      have heq : established = result := Option.some.inj hrun
      simpa only [heq] using hestablished
  | cons step rest ih =>
      cases heval : evalStep left right seeds established step with
      | none =>
          simp only [runFrom, heval] at hrun
          cases hrun
      | some fact =>
          have hfact := evalStep_sound left right h hsuper seeds established
            hseeds hestablished step fact heval
          have hnext : ∀ a ∈ established ++ [fact], a.2 ≤ h a.1 := by
            intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact hestablished a ha
            · have heq : a = fact := List.mem_singleton.mp ha
              simpa only [heq] using hfact
          simp only [runFrom, heval] at hrun
          exact ih (established ++ [fact]) hnext hrun

/-- Soundness at a specified output index, including its physical vertex. -/
theorem certified_bound (left right : V → V) (h : V → ℤ)
    (hsuper : ∀ z, h (left z) + h (right z) ≤ 2 * h z)
    (seeds : List (Fact V)) (hseeds : ∀ a ∈ seeds, a.2 ≤ h a.1)
    (steps : List (Step V)) (result : List (Fact V))
    (hrun : run left right seeds steps = some result)
    (index : ℕ) (z : V) (value : ℤ)
    (hindex : result[index]? = some (z, value)) : value ≤ h z := by
  have hresult := runFrom_sound left right h hsuper seeds hseeds steps [] result
    (by intro a ha; cases ha) hrun
  exact hresult (z, value) (List.mem_of_getElem? hindex)

end FLattice.Auxiliary
