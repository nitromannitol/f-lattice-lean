import FLatticePaper.Construction.PlacedSchedule
import FLatticePaper.Construction.OrderedOverlap

/-! # Nonempty overlaps at every insertion, through canonical common sites (task 37)

The geometric core of the evaluator is that at every insertion the incoming copy meets the occupied set
(`OrderedContacts`). A common site gives the contact: if a site lies in the occupied union and in the incoming copy, the
intersection is nonempty. A site of a placed copy is a point of its donor translated by the offset (`mem_place_sites`), so a
canonical site is given by its donor point and the translation. The induction over the word has to show that the canonical
sites exist; this file proves the generic part, from which evaluation succeeds whenever every insertion has an overlap. -/

namespace FLatticePaper.Construction

open HeightTile

variable {α : Type} [DecidableEq α]

/-- A common site of the occupied union and the incoming copy is a contact. -/
theorem contact_of_common_site (occupied incoming : Finset α) (site : α) (ho : site ∈ occupied)
    (hi : site ∈ incoming) : (occupied ∩ incoming).Nonempty :=
  ⟨site, Finset.mem_inter.mpr ⟨ho, hi⟩⟩

/-- A donor point translated by the offset of the placed copy is a site of the placed copy. -/
theorem donor_point_placed (tile : HeightTile Site) (offset slope donor : Site) (hd : donor ∈ tile.sites) :
    donor + offset ∈ (tile.place offset slope).sites := by
  rw [HeightTile.mem_place_sites]
  simpa only [add_sub_cancel_right] using hd

/-- A donor point of the placed copy that also lies in an occupied site is a contact of the insertion. -/
theorem contact_of_donor_point (occupied : Finset Site) (tile : HeightTile Site) (offset slope donor : Site)
    (hd : donor ∈ tile.sites) (hoccupied : donor + offset ∈ occupied) :
    (occupied ∩ (tile.place offset slope).sites).Nonempty :=
  contact_of_common_site occupied _ (donor + offset) hoccupied (donor_point_placed tile offset slope donor hd)

/-- The contact of one insertion followed by the contacts of the rest, with the occupied union after it. -/
theorem orderedContacts_cons (occupied : Finset Site) (incoming : HeightTile Site)
    (rest : List (HeightTile Site)) (contact : (occupied ∩ incoming.sites).Nonempty)
    (restContacts : OrderedContacts (occupied ∪ incoming.sites) rest) :
    OrderedContacts occupied (incoming :: rest) :=
  ⟨contact, restContacts⟩

/-- Evaluation succeeds for a placed schedule whose insertions all have nonempty overlaps. -/
theorem eval_ok_of_ordered (schedule : PlacedSchedule) (mode : AssemblyFinish) (context : String)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) :
    ∃ result, schedule.eval mode context = .ok result :=
  ⟨_, schedule.eval_eq_ok mode context contacts⟩

/-- The implication of the task: when the copies of a schedule have nonempty overlaps at every insertion, evaluation
succeeds, for either finishing mode. -/
theorem eval_ok_of_overlaps (schedule : PlacedSchedule) (mode : AssemblyFinish) (context : String)
    (overlaps : OrderedContacts schedule.first.val.sites schedule.copies) :
    ∃ result, schedule.eval mode context = .ok result :=
  eval_ok_of_ordered schedule mode context overlaps

end FLatticePaper.Construction
