import FLatticePaper.Construction.OrdinaryComparisons
import FLatticePaper.Construction.OrdinaryStandardCover

/-! The output of an ordinary standard agrees with its target, from the nominal agreement of its six copies and the
chronological contacts (task 41, the reduction in supplement Part II section II).

Each copy `c` in the schedule agrees with the target up to one constant (the nominal price statement). Then comparisons
1 and 2 hold for every insertion with that constant, comparison 3 is the contact of the insertion, and the ordered
minimum of the six copies agrees with the target (`PlacedSchedule.eval_tile_agrees`). -/

namespace FLatticePaper.Construction

open Farey HeightTile

/-- The ordered comparisons of a list of copies, from their nominal agreement and the contacts. -/
theorem orderedComparisons_of_nominal {α : Type*} [DecidableEq α] (target : α → ℤ) :
    ∀ (occupied : Finset α) (copies : List (HeightTile α)),
      (∀ c ∈ copies, ∃ g : ℤ, c.Agrees target g) → OrderedContacts occupied copies →
        OrderedComparisons target occupied copies
  | _, [], _, _ => trivial
  | occupied, c :: rest, hnom, hcon => by
    obtain ⟨g, hg⟩ := hnom c (List.mem_cons_self)
    exact ⟨hg.fits hcon.1, orderedComparisons_of_nominal target (occupied ∪ c.sites) rest
      (fun c' hc' => hnom c' (List.mem_cons_of_mem _ hc')) hcon.2⟩

/-- The six copies of an ordinary standard, as listed in the schedule. -/
theorem ordinaryStandard_copies_mem (parents : TileParents) (word : Word) (parity : Parity)
    (c : HeightTile Site) (hc : c ∈ (ordinaryStandardSchedule parents word parity).copies) :
    ∃ slot : Fin 6, c = (ordinaryStandardCopy parents word parity slot).val := by
  unfold PlacedSchedule.copies at hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  rw [ordinaryStandardSchedule_rest] at ht
  obtain ⟨slot, -, rfl⟩ := List.mem_map.mp ht
  exact ⟨slot, rfl⟩

/-- The output of an ordinary standard agrees with its target, from the nominal agreement of its six copies and the
chronological contacts of its insertions. -/
theorem ordinaryStandard_output_agrees (parents : TileParents) (word : Word) (parity : Parity) (context : String)
    {target : Field}
    (hnom : ∀ slot : Fin 6, ∃ g : ℤ, (ordinaryStandardCopy parents word parity slot).val.Agrees target g)
    (hcon : OrderedContacts (ordinaryStandardSchedule parents word parity).first.val.sites
      (ordinaryStandardSchedule parents word parity).copies) :
    ∃ result, (ordinaryStandardSchedule parents word parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => target (site + ((ordinaryStandardSchedule parents word parity).raw hcon).val.boxOrigin
          ((ordinaryStandardSchedule parents word parity).raw hcon).property)) g := by
  obtain ⟨g0, h0⟩ := hnom 0
  have hfirst : ((ordinaryStandardSchedule parents word parity).first).val.Agrees target g0 := by
    rw [ordinaryStandardSchedule_first]
    exact h0
  have hnomCopies : ∀ c ∈ (ordinaryStandardSchedule parents word parity).copies,
      ∃ g : ℤ, c.Agrees target g := by
    intro c hc
    obtain ⟨slot, rfl⟩ := ordinaryStandard_copies_mem parents word parity c hc
    exact hnom slot
  have hcopies := orderedComparisons_of_nominal target _ _ hnomCopies hcon
  obtain ⟨result, hres, hagree⟩ := (ordinaryStandardSchedule parents word parity).eval_tile_agrees context
    hfirst hcopies
  exact ⟨result, hres, g0, hagree⟩

end FLatticePaper.Construction
