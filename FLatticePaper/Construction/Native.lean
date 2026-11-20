import FLatticePaper.Construction.Chronology
import FLatticePaper.Construction.NativeSchedules

namespace FLatticePaper.Construction

open Farey

structure SavedRegisters where
  word : Word
  tiles : TileRegisters

structure NativeState where
  current : SavedRegisters
  savedTwo : SavedRegisters
  savedThree : SavedRegisters

def NativeState.init (run : BaseRun) : NativeState :=
  let saved : SavedRegisters := ⟨run.word, run.registers⟩
  ⟨saved, saved, saved⟩

def NativeState.history (state : NativeState) : AncestorHistory :=
  ⟨state.current.word, state.savedTwo.word, state.savedThree.word⟩

private def correctionPair (saved : SavedRegisters) (beforePush : Word)
    (parity : Parity) (elongated : Bool) : Except String CorrectionPair := do
  let left ← correctionSchedule saved.tiles saved.word beforePush parity true elongated
  let left ← left.eval .correction "left L"
  let right ← correctionSchedule saved.tiles saved.word beforePush parity false elongated
  let right ← right.eval .correction "right L"
  return ⟨left.llCenter, right.llCenter⟩

/-- One unbounded step from the actual four input registers, consuming both
lengths of correction from the relevant pre-update saved registers. -/
def NativeState.nextRegisters (state : NativeState) (digit : Digit) : Except String TileRegisters := do
  let beforePush := state.current.word
  let word := beforePush ++ [digit]
  let parents := state.current.tiles.parentsFor digit
  let standard := fun parity => (ordinaryStandardSchedule parents word parity).eval .tile "standard"
  let alternate := fun parity =>
    (ordinaryAlternateSchedule parents beforePush digit parity).eval .tile "alternate"
  let correctedStd := fun pair parity =>
    (correctedStandardSchedule parents pair beforePush digit parity).eval .tile "corrected standard"
  let correctedAlt := fun pair parity =>
    (correctedAlternateSchedule parents pair beforePush digit parity).eval .tile "corrected alternate"
  let (odd, even, altOdd, altEven) ← match digit with
    | .one => do pure (← standard .odd, ← standard .even, ← alternate .odd, ← alternate .even)
    | .two => do
      let short ← correctionPair state.savedTwo beforePush .odd false
      let long ← correctionPair state.savedTwo beforePush .odd true
      pure (← standard .odd, ← correctedStd short .even, ← correctedAlt long .odd, ← alternate .even)
    | .three => do
      let short ← correctionPair state.savedThree beforePush .even false
      let long ← correctionPair state.savedThree beforePush .even true
      pure (← correctedStd short .odd, ← standard .even, ← alternate .odd, ← correctedAlt long .even)
  return ⟨⟨odd, even, parents.odd, parents.even⟩,
    ⟨altOdd, altEven, parents.alternateOdd, parents.alternateEven⟩⟩

private def NativeState.saveNext (state : NativeState) (digit : Digit)
    (registers : TileRegisters) : NativeState :=
  let new : SavedRegisters := ⟨state.current.word ++ [digit], registers⟩
  match digit with
  | .one => ⟨new, new, new⟩
  | .two => ⟨new, state.savedTwo, new⟩
  | .three => ⟨new, new, state.savedThree⟩

def NativeState.advance (state : NativeState) (digit : Digit) : Except String NativeState :=
  (state.nextRegisters digit).map (state.saveNext digit)

theorem NativeState.advance_history (state next : NativeState) (digit : Digit)
    (h : state.advance digit = .ok next) : next.history = state.history.push digit := by
  unfold advance at h
  cases heq : state.nextRegisters digit with
  | error reason => simp [heq, Except.map] at h
  | ok registers =>
    rw [heq] at h
    have hnext : state.saveNext digit registers = next := Except.ok.inj h
    subst next
    cases digit <;> rfl

def NativeState.walk (state : NativeState) : Word → Except String NativeState
  | [] => .ok state
  | digit :: rest =>
    match state.advance digit with
    | .ok next => next.walk rest
    | .error reason => .error reason

theorem NativeState.walk_history (state result : NativeState) (suffix : Word)
    (h : state.walk suffix = .ok result) : result.history = state.history.walk suffix := by
  induction suffix generalizing state with
  | nil =>
    have heq : state = result := Except.ok.inj h
    subst result
    rfl
  | cons digit tail ih =>
    cases hstep : state.advance digit with
    | error reason => simp [walk, hstep] at h
    | ok next =>
      have htail : next.walk tail = .ok result := by simpa [walk, hstep] using h
      rw [ih next htail, state.advance_history next digit hstep]
      rfl

def evaluateNativeState (word : Word) : Except String NativeState :=
  let (initializer, suffix) := splitInitial word
  (NativeState.init initializer).walk suffix

theorem evaluateNativeState_history (word : Word) (state : NativeState)
    (h : evaluateNativeState word = .ok state) : state.history = ancestorHistory word :=
  (NativeState.init (splitInitial word).1).walk_history state (splitInitial word).2 h

/-- The exact sparse evaluator, ending in the occupied lower-left convention.
Errors are not tiles; unconditional success on every word is a separate
geometric obligation. -/
def evaluateNative (word : Word) : Except String TileRegisters :=
  (evaluateNativeState word).map (fun state => state.current.tiles.llCenter)

theorem evaluateNative_base (initializer : BaseRun) :
    evaluateNative initializer.word = .ok initializer.registers.llCenter := by
  unfold evaluateNative evaluateNativeState
  rw [splitInitial_base]
  rfl

end FLatticePaper.Construction
