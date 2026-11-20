import FLatticePaper.Construction.CorrectionHeight

namespace FLatticePaper.Checks

open Construction

private def prefixTile : HeightTile ℤ where
  sites := {0, 1}
  height _ := 9

private def incomingTile : HeightTile ℤ where
  sites := {0, 1, 2}
  height site := if site.val = 0 then 6 else 5

private theorem prefix_agrees : prefixTile.Agrees (fun _ => 0) 9 := fun _ => rfl

private theorem incoming_fits : incomingTile.Fits prefixTile.sites (fun _ => 0) := by
  refine ⟨5, ?_, ?_, ⟨⟨1, by decide⟩, by decide, by decide⟩⟩
  · intro site hfresh
    have hne : site.val ≠ 0 := fun hzero => hfresh (hzero ▸ (by decide : 0 ∈ prefixTile.sites))
    simp [incomingTile, hne]
  · intro site _
    change 0 ≤ (if site.val = 0 then 6 else 5) - 5
    split <;> decide

private theorem orderedComparisons :
    HeightTile.OrderedComparisons (fun _ => 0) prefixTile.sites [incomingTile] :=
  ⟨incoming_fits, trivial⟩

private theorem strict_incoming :
    incomingTile.height ⟨0, by decide⟩ - 5 > (0 : ℤ) := by decide

theorem strictOverlap_identified :
    (prefixTile.insert incomingTile incoming_fits.contact).Agrees (fun _ => 0) 9 :=
  prefixTile.insert_agrees incomingTile incoming_fits.contact prefix_agrees incoming_fits

private def outerTile : HeightTile ℤ where
  sites := {-1, 0}
  height _ := -4

private theorem prefix_nonempty : prefixTile.sites.Nonempty := ⟨0, by decide⟩

private theorem outer_contact :
    (outerTile.sites ∩
      (prefixTile.correctionHeight [incomingTile] orderedComparisons.contacts prefix_nonempty).sites
    ).Nonempty :=
  ⟨0, by decide⟩

theorem strictOverlap_correction_reinserted :
    (outerTile.insert
      (prefixTile.correctionHeight [incomingTile] orderedComparisons.contacts prefix_nonempty)
      outer_contact).Agrees (fun _ => 0) (-4) :=
  outerTile.insert_correctionHeight_agrees prefixTile [incomingTile]
    orderedComparisons.contacts prefix_nonempty outer_contact (fun _ => rfl)
    prefix_agrees orderedComparisons

#print axioms HeightTile.contactShift_eq_of_agrees
#print axioms HeightTile.insert_height_eq_min
#print axioms HeightTile.insert_agrees
#print axioms HeightTile.insertAll_agrees
#print axioms HeightTile.correctionHeight_agrees
#print axioms HeightTile.insert_correctionHeight_agrees
#print axioms strict_incoming
#print axioms strictOverlap_identified
#print axioms strictOverlap_correction_reinserted

end FLatticePaper.Checks
