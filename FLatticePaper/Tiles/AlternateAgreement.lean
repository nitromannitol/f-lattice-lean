import FLatticePaper.Tiles.AlternateOrdinary
import FLatticePaper.Construction.OrdinaryAgreement

/-! # The ordinary alternate output and its plane target: the reduction to nominal agreement and contacts (task 46)

An ordinary alternate schedule has seven copies: the first copy is the placed standard donor in slot `0`; the rest are the
restored alternate piece (`oldAlternate`, placed at `seventhAlternateJet`) and the five further placed standard donors of
`afterSeventhAlternate`. The numerical check (scripts/alt_plane_check.py) finds that the ordinary even output agrees with
the alternate midpoint `H` of its word at zero translation, and the ordinary odd output agrees with the quarter turn of `H`
of the swapped word only for words of even phase. The statements below are the reduction, for any target field: if every
copy agrees with the target up to one constant and the copies meet their contacts, then the output agrees with the target
(the same argument as `ordinaryStandard_output_agrees`), with the constant of the first copy. Applying it to the alternate
targets is then a question of the nominal agreement of the seven copies, which is not proved here. -/

namespace FLatticePaper.Tiles.AlternateAgreement

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Alternate
open FLatticePaper.Tiles.AlternateOrdinary FLatticePaper.Tiles.OrdinaryStandard

/-- The copies of an ordinary alternate schedule: the restored alternate piece, and the placed standard donors of the
slots `afterSeventhAlternate` (every slot other than `0` occurs once). -/
theorem ordinaryAlternate_copies_mem (parents : TileParents) (beforePush : Word) (digit : Digit) (parity : Parity)
    (c : HeightTile Site) (hc : c ∈ (ordinaryAlternateSchedule parents beforePush digit parity).copies) :
    c = ((seventhAlternateJet beforePush digit parity).place
        (oldAlternate parents (beforePush ++ [digit]) parity)).val ∨
      ∃ s ∈ afterSeventhAlternate parity,
        c = (placedBySlot (alternateJets (beforePush ++ [digit]) parity)
          (standardSources parents parity.flip) s).val := by
  unfold PlacedSchedule.copies at hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp ht with rfl | ht'
  · exact Or.inl rfl
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht'
    exact Or.inr ⟨s, hs, rfl⟩

/-- **Output agreement from the nominal agreement of the seven copies and the contacts.** The ordinary alternate output
agrees with `target` up to one constant on the chart of its raw box origin, when the first copy agrees with `target` and
every copy agrees with `target` up to a constant, and the copies meet their chronological contacts. -/
theorem ordinaryAlternate_output_agrees (parents : TileParents) (beforePush : Word) (digit : Digit) (parity : Parity)
    (context : String) {target : Field} {g0 : ℤ}
    (hfirst : (ordinaryAlternateSchedule parents beforePush digit parity).first.val.Agrees target g0)
    (hnom : ∀ c ∈ (ordinaryAlternateSchedule parents beforePush digit parity).copies,
      ∃ g : ℤ, c.Agrees target g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit parity).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit parity).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit parity).eval .tile context = .ok result ∧
      result.val.Agrees
        (fun site => target (site + ((ordinaryAlternateSchedule parents beforePush digit parity).raw hcon).val.boxOrigin
          ((ordinaryAlternateSchedule parents beforePush digit parity).raw hcon).property)) g0 := by
  have hcopies := orderedComparisons_of_nominal target _ _ hnom hcon
  obtain ⟨result, hres, hagree⟩ := (ordinaryAlternateSchedule parents beforePush digit parity).eval_tile_agrees
    context hfirst hcopies
  exact ⟨result, hres, hagree⟩

/-- The seven-copy form of the reduction: the restored alternate piece and each placed standard donor agree with the target
up to constants, and the contacts hold. -/
theorem ordinaryAlternate_output_agrees_of_seven (parents : TileParents) (beforePush : Word) (digit : Digit)
    (parity : Parity) (context : String) {target : Field} {g0 : ℤ}
    (hfirst : (ordinaryAlternateSchedule parents beforePush digit parity).first.val.Agrees target g0)
    (hseventh : ∃ g : ℤ, ((seventhAlternateJet beforePush digit parity).place
        (oldAlternate parents (beforePush ++ [digit]) parity)).val.Agrees target g)
    (hslot : ∀ s ∈ afterSeventhAlternate parity, ∃ g : ℤ,
        (placedBySlot (alternateJets (beforePush ++ [digit]) parity)
          (standardSources parents parity.flip) s).val.Agrees target g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit parity).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit parity).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit parity).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => target (site + ((ordinaryAlternateSchedule parents beforePush digit parity).raw hcon).val.boxOrigin
          ((ordinaryAlternateSchedule parents beforePush digit parity).raw hcon).property)) g := by
  have hnom : ∀ c ∈ (ordinaryAlternateSchedule parents beforePush digit parity).copies,
      ∃ g : ℤ, c.Agrees target g := by
    intro c hc
    rcases ordinaryAlternate_copies_mem parents beforePush digit parity c hc with rfl | ⟨s, hs, rfl⟩
    · exact hseventh
    · exact hslot s hs
  obtain ⟨result, hres, hagree⟩ := ordinaryAlternate_output_agrees parents beforePush digit parity context hfirst hnom hcon
  exact ⟨result, hres, g0, hagree⟩

end FLatticePaper.Tiles.AlternateAgreement
