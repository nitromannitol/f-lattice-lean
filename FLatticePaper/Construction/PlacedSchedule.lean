import FLatticePaper.Construction.BaseRegisters
import FLatticePaper.Construction.PlacedAssembly

namespace FLatticePaper.Construction

open HeightTile

/-- The nonempty chronological list of already placed sources. -/
structure PlacedSchedule where
  first : NonemptyTile
  rest : List NonemptyTile

def PlacedSchedule.copies (schedule : PlacedSchedule) : List (HeightTile Site) :=
  schedule.rest.map Subtype.val

def decideOrderedContacts (occupied : Finset Site) :
    (copies : List (HeightTile Site)) → Decidable (OrderedContacts occupied copies)
  | [] => isTrue trivial
  | incoming :: rest =>
    letI := decideOrderedContacts (occupied ∪ incoming.sites) rest
    inferInstanceAs (Decidable
      ((occupied ∩ incoming.sites).Nonempty ∧ OrderedContacts (occupied ∪ incoming.sites) rest))

inductive AssemblyFinish
  | tile | correction

def PlacedSchedule.raw (schedule : PlacedSchedule)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) : NonemptyTile :=
  ⟨schedule.first.val.insertAll schedule.copies contacts,
    schedule.first.property.mono (schedule.first.val.subset_insertAll_sites schedule.copies contacts)⟩

def PlacedSchedule.finish (schedule : PlacedSchedule) (mode : AssemblyFinish)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) : NonemptyTile :=
  let trimmed := (schedule.raw contacts).trim
  match mode with
  | .tile => trimmed
  | .correction => ⟨trimmed.val.maxZero trimmed.property, trimmed.property⟩

/-- Executable ordered minimum. A disjoint required contact is an error, just
as in the pinned constructor: there is no supplied normalization in that case. -/
def PlacedSchedule.eval (schedule : PlacedSchedule) (mode : AssemblyFinish) (context : String) :
    Except String NonemptyTile :=
  letI := decideOrderedContacts schedule.first.val.sites schedule.copies
  if contacts : OrderedContacts schedule.first.val.sites schedule.copies then
    .ok (schedule.finish mode contacts)
  else .error ("disjoint required contact: " ++ context)

theorem PlacedSchedule.eval_eq_ok (schedule : PlacedSchedule) (mode : AssemblyFinish)
    (context : String) (contacts : OrderedContacts schedule.first.val.sites schedule.copies) :
    schedule.eval mode context = .ok (schedule.finish mode contacts) := by
  unfold PlacedSchedule.eval
  exact dif_pos contacts

theorem PlacedSchedule.eval_ok_iff (schedule : PlacedSchedule) (mode : AssemblyFinish)
    (context : String) (result : NonemptyTile) :
    schedule.eval mode context = .ok result ↔
      ∃ contacts, schedule.finish mode contacts = result := by
  unfold PlacedSchedule.eval
  split
  · rename_i contacts
    exact ⟨fun heq => ⟨contacts, Except.ok.inj heq⟩,
      fun ⟨_, heq⟩ => congrArg Except.ok heq⟩
  · rename_i hdisjoint
    constructor
    · intro heq
      cases heq
    · rintro ⟨contacts, _⟩
      exact False.elim (hdisjoint contacts)

theorem PlacedSchedule.finish_tile (schedule : PlacedSchedule)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) :
    (schedule.finish .tile contacts).val =
      schedule.first.val.meldPlaced schedule.copies contacts schedule.first.property := rfl

theorem PlacedSchedule.finish_correction (schedule : PlacedSchedule)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) :
    (schedule.finish .correction contacts).val =
      schedule.first.val.meldCorrection schedule.copies contacts schedule.first.property := rfl

theorem PlacedSchedule.eval_tile_agrees (schedule : PlacedSchedule) (context : String)
    {target : Field} {gauge : ℤ} (hfirst : schedule.first.val.Agrees target gauge)
    (hcopies : OrderedComparisons target schedule.first.val.sites schedule.copies) :
    let raw := schedule.raw hcopies.contacts
    ∃ result, schedule.eval .tile context = .ok result ∧
      result.val.Agrees (fun site => target (site + raw.val.boxOrigin raw.property)) gauge := by
  refine ⟨schedule.finish .tile hcopies.contacts, schedule.eval_eq_ok .tile context _, ?_⟩
  exact schedule.first.val.meldPlaced_agrees schedule.copies _ schedule.first.property hfirst hcopies

theorem PlacedSchedule.eval_correction_agrees (schedule : PlacedSchedule) (context : String)
    {target : Field} {gauge : ℤ} (hfirst : schedule.first.val.Agrees target gauge)
    (hcopies : OrderedComparisons target schedule.first.val.sites schedule.copies) :
    let raw := schedule.raw hcopies.contacts
    ∃ result, schedule.eval .correction context = .ok result ∧
      ∃ newGauge, result.val.Agrees (fun site => target (site + raw.val.boxOrigin raw.property))
        newGauge := by
  refine ⟨schedule.finish .correction hcopies.contacts, schedule.eval_eq_ok .correction context _, ?_⟩
  exact schedule.first.val.meldCorrection_agrees schedule.copies _ schedule.first.property hfirst hcopies

end FLatticePaper.Construction
