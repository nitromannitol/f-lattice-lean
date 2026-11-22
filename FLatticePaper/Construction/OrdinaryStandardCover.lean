import FLatticePaper.Construction.NativeCoverage

/-! Task 23, step 1 (ordinary standard cover propagation).

The output site set of the ordinary standard schedule is the union of its six placed copies, and
covering of the output is equivalent to covering of that union. The covering of the union by the
child's modified deck is the hand step (ALL_ORDINARY_STANDARD_NATIVE_COVER_PROPAGATES_HAND_THEOREM),
which is not formalized in this file. -/

namespace FLatticePaper.Construction

open Farey HeightTile

/-- The placed copy in a given slot of the ordinary standard schedule. -/
def ordinaryStandardCopy (parents : TileParents) (word : Word) (parity : Parity) (slot : Fin 6) :
    NonemptyTile :=
  placedBySlot (standardJets word parity) (standardSources parents parity) slot

/-- The union of the sites of the six placed copies of the ordinary standard schedule. -/
def ordinaryStandardSites (parents : TileParents) (word : Word) (parity : Parity) : Finset Site :=
  Finset.univ.biUnion fun slot : Fin 6 => (ordinaryStandardCopy parents word parity slot).val.sites

theorem ordinaryStandardSchedule_first (parents : TileParents) (word : Word) (parity : Parity) :
    (ordinaryStandardSchedule parents word parity).first =
      ordinaryStandardCopy parents word parity 0 :=
  rfl

theorem ordinaryStandardSchedule_rest (parents : TileParents) (word : Word) (parity : Parity) :
    (ordinaryStandardSchedule parents word parity).rest =
      (afterFirstStandard parity).map (ordinaryStandardCopy parents word parity) :=
  rfl

theorem afterFirstStandard_cases (parity : Parity) (slot : Fin 6) :
    slot = 0 ∨ slot ∈ afterFirstStandard parity := by
  cases parity <;> revert slot <;> decide

theorem mem_foldl_sites (copies : List (HeightTile Site)) (init : Finset Site) (site : Site) :
    site ∈ copies.foldl (fun occupied incoming => occupied ∪ incoming.sites) init ↔
      site ∈ init ∨ ∃ incoming ∈ copies, site ∈ incoming.sites := by
  induction copies generalizing init with
  | nil => simp
  | cons incoming rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_raw_sites (schedule : PlacedSchedule)
    (contacts : OrderedContacts schedule.first.val.sites schedule.copies) (site : Site) :
    site ∈ (schedule.raw contacts).val.sites ↔
      site ∈ schedule.first.val.sites ∨ ∃ incoming ∈ schedule.rest, site ∈ incoming.val.sites := by
  change site ∈ (schedule.first.val.insertAll schedule.copies contacts).sites ↔ _
  rw [insertAll_sites, mem_foldl_sites]
  unfold PlacedSchedule.copies
  constructor
  · rintro (h | ⟨t, ht, hs⟩)
    · exact Or.inl h
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact Or.inr ⟨u, hu, hs⟩
  · rintro (h | ⟨u, hu, hs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u.val, List.mem_map_of_mem hu, hs⟩

/-- The raw assembled site set is exactly the union of the six placed copies. -/
theorem ordinaryStandard_raw_sites (parents : TileParents) (word : Word) (parity : Parity)
    (contacts : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    ((ordinaryStandardSchedule parents word parity).raw contacts).val.sites =
      ordinaryStandardSites parents word parity := by
  ext site
  rw [mem_raw_sites, ordinaryStandardSchedule_first, ordinaryStandardSchedule_rest,
    ordinaryStandardSites, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨t, ht, hs⟩)
    · exact ⟨0, Finset.mem_univ _, h⟩
    · obtain ⟨slot, -, rfl⟩ := List.mem_map.mp ht
      exact ⟨slot, Finset.mem_univ _, hs⟩
  · rintro ⟨slot, -, hs⟩
    rcases afterFirstStandard_cases parity slot with rfl | hslot
    · exact Or.inl hs
    · exact Or.inr ⟨_, List.mem_map_of_mem hslot, hs⟩

/-- Covering of the output of a successful ordinary standard evaluation is equivalent to covering
of the union of its six placed copies. The output is a translate of the raw assembly. -/
theorem ordinaryStandard_eval_covers_iff (deck : PeriodDeck) (parents : TileParents) (word : Word)
    (parity : Parity) (context : String) (out : NonemptyTile)
    (hEval : (ordinaryStandardSchedule parents word parity).eval .tile context = .ok out) :
    deck.Covers out.val.sites ↔ deck.Covers (ordinaryStandardSites parents word parity) := by
  obtain ⟨contacts, hfin⟩ := (PlacedSchedule.eval_ok_iff _ _ _ _).mp hEval
  have hout : out.val.sites =
      (((ordinaryStandardSchedule parents word parity).raw contacts).trim).val.sites := by
    rw [← hfin]
    rfl
  rw [hout, ← ordinaryStandard_raw_sites parents word parity contacts]
  constructor
  · intro h
    exact covers_of_place (tile := ((ordinaryStandardSchedule parents word parity).raw contacts).val)
      (-((ordinaryStandardSchedule parents word parity).raw contacts).val.boxOrigin
        ((ordinaryStandardSchedule parents word parity).raw contacts).property) 0 h
  · intro h
    exact covers_trim h _

/-- Covering of the union of the six placed copies gives covering of the successful output. -/
theorem ordinaryStandard_output_covers (deck : PeriodDeck) (parents : TileParents) (word : Word)
    (parity : Parity) (context : String) (out : NonemptyTile)
    (hEval : (ordinaryStandardSchedule parents word parity).eval .tile context = .ok out)
    (hUnion : deck.Covers (ordinaryStandardSites parents word parity)) :
    deck.Covers out.val.sites :=
  (ordinaryStandard_eval_covers_iff deck parents word parity context out hEval).mpr hUnion

/-- The parent tiles that the ordinary schedule reads are covered by the two frames of the child
word, whenever the register state covers the frames of the word before the digit. -/
theorem parents_cover_of_registers (registers : TileRegisters) (beforePush : Word) (digit : Digit)
    (hregs : registers.llCenter.Covers (parentsAt beforePush)) :
    (parentsAt (beforePush ++ [digit])).odd.modifiedDeck.Covers
        (registers.parentsFor digit).odd.val.sites ∧
      (parentsAt (beforePush ++ [digit])).even.modifiedDeck.Covers
        (registers.parentsFor digit).even.val.sites := by
  rw [parentsAt_append_singleton]
  cases digit with
  | one => exact ⟨hregs.standardOdd, hregs.standardEven⟩
  | two => exact ⟨hregs.standardOdd, hregs.standardRetainedEven⟩
  | three => exact ⟨hregs.standardRetainedOdd, hregs.standardEven⟩

/-- Task 23, conditional form. The parent covers from the register state feed the union claim
`core`, which gives covering of the successful ordinary standard output. The claim `core` is the
open hand step: it is the statement that the six placed copies cover the child's modified deck. -/
theorem ordinaryStandard_output_covers_of_core (registers : TileRegisters) (beforePush : Word)
    (digit : Digit) (parity : Parity) (context : String) (out : NonemptyTile)
    (hregs : registers.llCenter.Covers (parentsAt beforePush))
    (hEval : (ordinaryStandardSchedule (registers.parentsFor digit) (beforePush ++ [digit])
      parity).eval .tile context = .ok out)
    (core : (parentsAt (beforePush ++ [digit])).odd.modifiedDeck.Covers
          (registers.parentsFor digit).odd.val.sites →
        (parentsAt (beforePush ++ [digit])).even.modifiedDeck.Covers
          (registers.parentsFor digit).even.val.sites →
        ((parentsAt (beforePush ++ [digit])).current parity).modifiedDeck.Covers
          (ordinaryStandardSites (registers.parentsFor digit) (beforePush ++ [digit]) parity)) :
    ((parentsAt (beforePush ++ [digit])).current parity).modifiedDeck.Covers out.val.sites := by
  obtain ⟨hOdd, hEven⟩ := parents_cover_of_registers registers beforePush digit hregs
  exact ordinaryStandard_output_covers _ _ _ _ _ _ hEval (core hOdd hEven)

end FLatticePaper.Construction
