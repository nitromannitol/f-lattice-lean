import FLatticePaper.Construction.ScheduleKinds

/-! # The evaluator fails only at contacts, for every word (task 36)

`evaluateNative w` (Native.lean) can fail in two ways: a *structural* error of the correction schedule (an empty saved
ancestor, or a saved ancestor that is not the suffix of the current word), or a *contact* error of `PlacedSchedule.eval`
(a required contact between the placed copies is disjoint). The structural errors cannot occur: the saved ancestors of the
evaluator satisfy the suffix invariant `SuffixInvariant`, which is preserved by every step and holds at the start of every
word (the base run of `splitInitial`). So for every word, an evaluation failure is a contact failure. Whether the contacts
hold is the geometric content of `lemma:l_correct_existence` and `lemma:tile-odometer-existence`, which is not proved here
(the numerical check is in the report). -/

namespace FLatticePaper.Construction

open Farey

/-- A contact failure, the only error that the geometry of the schedules produces (`PlacedSchedule.eval`). -/
def IsContactError (e : String) : Prop :=
  ∃ ctx : String, e = "disjoint required contact: " ++ ctx

/-- Every error of the value is a contact failure (no structural error). -/
def NoStructuralError {α : Type} (x : Except String α) : Prop :=
  ∀ e : String, x = .error e → IsContactError e

theorem noStructural_ok {α : Type} (a : α) : NoStructuralError (Except.ok a : Except String α) := by
  intro e h
  cases h

theorem noStructural_eval (schedule : PlacedSchedule) (mode : AssemblyFinish) (context : String) :
    NoStructuralError (schedule.eval mode context) := by
  intro e h
  unfold PlacedSchedule.eval at h
  split at h
  · cases h
  · cases h
    exact ⟨context, rfl⟩

theorem noStructural_bind {α β : Type} {x : Except String α} {f : α → Except String β}
    (hx : NoStructuralError x) (hf : ∀ a, NoStructuralError (f a)) :
    NoStructuralError (x >>= f) := by
  intro e h
  cases x with
  | error e' =>
    change Except.error e' = Except.error e at h
    cases h
    exact hx _ rfl
  | ok a =>
    exact hf a e h

theorem noStructural_choose {α : Type} (kind : ScheduleKind) {a b c : Except String α}
    (ha : NoStructuralError a) (hb : NoStructuralError b) (hc : NoStructuralError c) :
    NoStructuralError (chooseKind kind a b c) := by
  cases kind
  · exact ha
  · exact hb
  · exact hc

/-- The saved-suffix invariant of a history: the current word is each saved word followed by a pure run, and a nonempty
current word has nonempty saved words. -/
structure SuffixInvariant (h : AncestorHistory) : Prop where
  two : ∃ k : ℕ, h.current = h.savedTwo ++ List.replicate k .two
  three : ∃ k : ℕ, h.current = h.savedThree ++ List.replicate k .three
  nonempty : h.current ≠ [] → h.savedTwo ≠ [] ∧ h.savedThree ≠ []

theorem suffixInvariant_push (h : AncestorHistory) (digit : Digit) (hI : SuffixInvariant h)
    (hadm : h.current = [] → digit = .one) : SuffixInvariant (h.push digit) := by
  obtain ⟨kt, ht⟩ := hI.two
  obtain ⟨ki, hi⟩ := hI.three
  cases digit with
  | one =>
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ?_⟩
    · simp [AncestorHistory.push]
    · simp [AncestorHistory.push]
    · intro _
      simp [AncestorHistory.push]
  | two =>
    have hcur : h.current ≠ [] := by
      intro hc
      have := hadm hc
      cases this
    refine ⟨⟨kt + 1, ?_⟩, ⟨0, ?_⟩, ?_⟩
    · simp [AncestorHistory.push, ht, List.replicate_succ', List.append_assoc]
    · simp [AncestorHistory.push]
    · intro _
      exact ⟨(hI.nonempty hcur).1, by simp [AncestorHistory.push]⟩
  | three =>
    have hcur : h.current ≠ [] := by
      intro hc
      have := hadm hc
      cases this
    refine ⟨⟨0, ?_⟩, ⟨ki + 1, ?_⟩, ?_⟩
    · simp [AncestorHistory.push]
    · simp [AncestorHistory.push, hi, List.replicate_succ', List.append_assoc]
    · intro _
      exact ⟨by simp [AncestorHistory.push], (hI.nonempty hcur).2⟩

theorem correctionSchedule_noStructural (tiles : TileRegisters) (ancestor beforePush : Word) (parity : Parity)
    (flip elongated : Bool) (hne : ancestor ≠ []) (k : ℕ)
    (hsuffix : beforePush = ancestor ++ List.replicate k (match parity with | .odd => Digit.two | .even => Digit.three)) :
    NoStructuralError (correctionSchedule tiles ancestor beforePush parity flip elongated) := by
  have hlast : ∃ last, ancestor.getLast? = some last := by
    cases ancestor with
    | nil => exact absurd rfl hne
    | cons a t => exact ⟨(a :: t).getLast (by simp), rfl⟩
  obtain ⟨last, hl⟩ := hlast
  have hscan : beforePush.length - ancestor.length = k := by
    rw [hsuffix]
    simp
  cases parity <;> intro e h <;> unfold correctionSchedule at h <;> simp [hl, hsuffix] at h <;> cases h

theorem correctionPairOf_noStructural (saved : SavedRegisters) (beforePush : Word) (parity : Parity)
    (elongated : Bool) (hne : saved.word ≠ []) (k : ℕ)
    (hsuffix : beforePush = saved.word ++ List.replicate k (match parity with | .odd => Digit.two | .even => Digit.three)) :
    NoStructuralError (correctionPairOf saved beforePush parity elongated) := by
  unfold correctionPairOf
  refine noStructural_bind (correctionSchedule_noStructural saved.tiles saved.word beforePush parity true elongated hne k hsuffix) (fun left => ?_)
  refine noStructural_bind (noStructural_eval _ _ _) (fun left' => ?_)
  refine noStructural_bind (correctionSchedule_noStructural saved.tiles saved.word beforePush parity false elongated hne k hsuffix) (fun right => ?_)
  refine noStructural_bind (noStructural_eval _ _ _) (fun right' => ?_)
  exact noStructural_ok _

theorem tableRegisters_noStructural (state : NativeState) (digit : Digit)
    (hI : SuffixInvariant state.history) (hadm : state.current.word = [] → digit = .one) :
    NoStructuralError (tableRegisters state digit) := by
  cases digit with
  | one =>
    simp only [tableRegisters]
    refine noStructural_bind (noStructural_eval _ _ _) (fun oddTile => ?_)
    refine noStructural_bind (noStructural_eval _ _ _) (fun evenTile => ?_)
    refine noStructural_bind (noStructural_eval _ _ _) (fun altOdd => ?_)
    refine noStructural_bind (noStructural_eval _ _ _) (fun altEven => ?_)
    exact noStructural_ok _
  | two =>
    have hcur : state.current.word ≠ [] := by
      intro hc
      have := hadm hc
      cases this
    obtain ⟨k, hk⟩ := hI.two
    have hsaved := (hI.nonempty hcur).1
    simp only [tableRegisters]
    refine noStructural_bind (correctionPairOf_noStructural state.savedTwo state.current.word .odd false hsaved k
      hk) (fun short => ?_)
    refine noStructural_bind (correctionPairOf_noStructural state.savedTwo state.current.word .odd true hsaved k
      hk) (fun long => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun oddTile => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun evenTile => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun altOdd => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun altEven => ?_)
    exact noStructural_ok _
  | three =>
    have hcur : state.current.word ≠ [] := by
      intro hc
      have := hadm hc
      cases this
    obtain ⟨k, hk⟩ := hI.three
    have hsaved := (hI.nonempty hcur).2
    simp only [tableRegisters]
    refine noStructural_bind (correctionPairOf_noStructural state.savedThree state.current.word .even false hsaved k
      hk) (fun short => ?_)
    refine noStructural_bind (correctionPairOf_noStructural state.savedThree state.current.word .even true hsaved k
      hk) (fun long => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun oddTile => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun evenTile => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun altOdd => ?_)
    refine noStructural_bind (noStructural_choose _ (noStructural_eval _ _ _) (noStructural_eval _ _ _)
      (noStructural_eval _ _ _)) (fun altEven => ?_)
    exact noStructural_ok _

/-- A failed step of the evaluator is a contact failure, given the invariant at its state. -/
theorem advance_error_contact (state : NativeState) (digit : Digit) (e : String)
    (hI : SuffixInvariant state.history) (hadm : state.current.word = [] → digit = .one)
    (h : state.advance digit = .error e) : IsContactError e := by
  unfold NativeState.advance at h
  cases hn : state.nextRegisters digit with
  | error e' =>
    rw [hn] at h
    change Except.error e' = Except.error e at h
    cases h
    have hns := tableRegisters_noStructural state digit hI hadm
    rw [← nextRegisters_eq_tableRegisters] at hns
    exact hns _ hn
  | ok r =>
    rw [hn] at h
    simp [Except.map] at h

theorem walk_error_contact (suffix : Word) :
    ∀ (state : NativeState), SuffixInvariant state.history →
      (state.current.word = [] → ∀ d tl, suffix = d :: tl → d = .one) →
      ∀ e : String, state.walk suffix = .error e → IsContactError e := by
  induction suffix with
  | nil =>
    intro state _ _ e h
    change Except.ok state = Except.error e at h
    cases h
  | cons digit tail ih =>
    intro state hI hadm e h
    unfold NativeState.walk at h
    cases hadv : state.advance digit with
    | error e' =>
      rw [hadv] at h
      change Except.error e' = Except.error e at h
      cases h
      exact advance_error_contact state digit _ hI (fun hc => hadm hc digit tail rfl) hadv
    | ok next =>
      rw [hadv] at h
      have hhist := state.advance_history next digit hadv
      have hI' : SuffixInvariant next.history := by
        rw [hhist]
        exact suffixInvariant_push state.history digit hI (fun hc => hadm hc digit tail rfl)
      have hadm' : next.current.word = [] → ∀ d tl, tail = d :: tl → d = .one := by
        intro hc
        exfalso
        have hh : next.history.current = state.history.current ++ [digit] := by
          rw [hhist]
          cases digit <;> rfl
        have hn : next.history.current ≠ [] := by
          rw [hh]
          simp
        exact hn hc
      exact ih next hI' hadm' e h

/-- The initial base run of `splitInitial` has the suffix invariant, and an empty base run is followed only by the digit one. -/
theorem splitInitial_start (word : Word) :
    SuffixInvariant (AncestorHistory.init (splitInitial word).1) ∧
      ((splitInitial word).1.word = [] → ∀ d tl, (splitInitial word).2 = d :: tl → d = .one) := by
  cases word with
  | nil =>
    refine ⟨⟨⟨0, by simp [AncestorHistory.init]⟩, ⟨0, by simp [AncestorHistory.init]⟩, fun h => (h rfl).elim⟩, ?_⟩
    intro _ d tl h
    simp [splitInitial] at h
  | cons digit rest =>
    cases digit with
    | one =>
      refine ⟨⟨⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩,
        ⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩, fun h => (h rfl).elim⟩, ?_⟩
      intro _ d tl h
      have hs : (splitInitial (Digit.one :: rest)).2 = Digit.one :: rest := by simp [splitInitial]
      rw [hs] at h
      injection h with h1 _
      exact h1.symm
    | two =>
      refine ⟨⟨⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩,
        ⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩, fun _ => ⟨?_, ?_⟩⟩, ?_⟩
      · simp [AncestorHistory.init, splitInitial, BaseRun.word]
      · simp [AncestorHistory.init, splitInitial, BaseRun.word]
      · intro hc
        simp [splitInitial, BaseRun.word] at hc
    | three =>
      refine ⟨⟨⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩,
        ⟨0, by simp [AncestorHistory.init, splitInitial, BaseRun.word]⟩, fun _ => ⟨?_, ?_⟩⟩, ?_⟩
      · simp [AncestorHistory.init, splitInitial, BaseRun.word]
      · simp [AncestorHistory.init, splitInitial, BaseRun.word]
      · intro hc
        simp [splitInitial, BaseRun.word] at hc

/-- Every evaluation failure of the evaluator is a contact failure, for every word. -/
theorem evaluateNativeState_error_contact (word : Word) (e : String)
    (h : evaluateNativeState word = .error e) : IsContactError e := by
  unfold evaluateNativeState at h
  obtain ⟨hI, hadm⟩ := splitInitial_start word
  exact walk_error_contact (splitInitial word).2 (NativeState.init (splitInitial word).1) hI hadm e h

/-- Every evaluation failure of `evaluateNative` is a contact failure, for every word. -/
theorem evaluateNative_error_contact (word : Word) (e : String) (h : evaluateNative word = .error e) :
    IsContactError e := by
  unfold evaluateNative at h
  cases hs : evaluateNativeState word with
  | error e' =>
    rw [hs] at h
    change Except.error e' = Except.error e at h
    cases h
    exact evaluateNativeState_error_contact word _ hs
  | ok state =>
    rw [hs] at h
    change Except.ok _ = Except.error e at h
    cases h

end FLatticePaper.Construction
