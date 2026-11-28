import FLatticePaper.Tiles.CorrectedExceptionalRotation
import FLatticePaper.Tiles.CorrectedSwappedDomains
import FLatticePaper.Tiles.CorrectedCellsOrdinary

/-! Rotation at every corrected exit and reduction of all four word domains to the two three-ending domains. -/

namespace FLatticePaper.Tiles.CorrectedAllRotations

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles Standard
open JointFamily JointRot LCorrecProps CorrectedEvenPlacement CorrectedPlacementFrames
open CorrectedChildColumns CorrectedCellRotation

private theorem stripped (v : Word) : stemPrefix v=[] ∨ ∃ u one, stemPrefix v=u++[exit one] := by
  induction v using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton v s ih =>
    change stripTrailing .three (v++[s])=[] ∨ ∃ u one, stripTrailing .three (v++[s])=u++[exit one]
    rw [stripTrailing_snoc]
    cases s
    · exact Or.inr ⟨v,true,rfl⟩
    · exact Or.inr ⟨v,false,rfl⟩
    · exact ih

theorem exit_of_nonbase (v : Word) (hn : ¬IsBase (v++[.three])) : ∃ u one, stemPrefix v=u++[exit one] := by
  rcases stripped v with h|h
  · have e := strip_append_replicate Digit.three v
    change stemPrefix v++List.replicate (trailingCount .three v) .three=v at e
    rw [h,List.nil_append] at e
    apply False.elim; apply hn
    rw [←e,←List.replicate_succ']
    exact AltRotStep.isBase_replicate_three _
  · exact h

/-- Ordinary and elongated columns rotate at all corrected exits, including the enlarged bridge. -/
theorem columns (v u : Word) (one plus long : Bool) (pre : stemPrefix v=u++[exit one]) :
    CellsRot (evenLCells v plus long) (oddLCells (swapW v) (plus != W1Odd v) long)
      (texV1Even ((parentsAt v).current .even)-((0,1):Site)) := by
  by_cases pure : IsBase (stemPrefix v)
  · rcases pure with nil|three|two
    · rw [pre] at nil; simp at nil
    · have d := three (exit one) (by rw [pre]; simp)
      cases one <;> contradiction
    · have R : stemPrefix v=List.replicate (u.length+1) .two := List.eq_replicate_iff.mpr ⟨by simp [pre],two⟩
      exact CorrectedExceptionalRotation.cells v u.length plus long R
  · exact CorrectedRegularRotation.at_exit v u one plus long pre pure

/-- The two three-ending native domains suffice for every non-base word in both families. -/
theorem corrected (domains : ∀ (v u : Word) (one : Bool), stemPrefix v=u++[exit one] → ¬IsBase (v++[.three]) →
    evenChild evenLCells v false=oddTile (v++[.three]) ∧ evenChild evenLCells v true=altEvenT (v++[.three])) :
    CorrectedCells := by
  intro w hn
  induction w using List.reverseRecOn with
  | nil => exact False.elim (hn (Or.inl rfl))
  | append_singleton v s _ =>
    cases s
    · exact ⟨CorrectedCellsOrdinary.odd_domain _ hn (by simp),CorrectedCellsOrdinary.even_domain _ hn (by simp),
        CorrectedCellsOrdinary.alt_odd_domain _ hn (by simp),CorrectedCellsOrdinary.alt_even_domain _ hn (by simp)⟩
    · have sw : swapW (v++[.two])=swapW v++[.three] := by rw [swapW_append]; rfl
      have h := nonbase_swap hn
      rw [sw] at h
      obtain ⟨u,one,pre⟩ := exit_of_nonbase (swapW v) h
      obtain ⟨A,B⟩ := domains (swapW v) u one pre h
      have R := CorrectedSwappedDomains.transfer (swapW v) h (fun p l => columns _ _ _ p l pre) A B
      rw [swapW_swapW'] at R
      exact ⟨CorrectedCellsOrdinary.odd_domain _ hn (by simp),R.1,R.2,
        CorrectedCellsOrdinary.alt_even_domain _ hn (by simp)⟩
    · obtain ⟨u,one,pre⟩ := exit_of_nonbase v hn
      obtain ⟨A,B⟩ := domains v u one pre hn
      exact ⟨A,CorrectedCellsOrdinary.even_domain _ hn (by simp),CorrectedCellsOrdinary.alt_odd_domain _ hn (by simp),B⟩

end FLatticePaper.Tiles.CorrectedAllRotations
