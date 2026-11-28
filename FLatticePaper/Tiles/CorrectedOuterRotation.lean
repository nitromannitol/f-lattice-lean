import FLatticePaper.Tiles.CorrectedCellRotation

/-! Rotation of every placed stem and head, including the columns with an enlarged bridge. -/

namespace FLatticePaper.Tiles.CorrectedOuterRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps SurgicalWeak SurgicalAlt SurgicalDict JointRot
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedCellRotation

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)

def outer (w : Word) (plus elong : Bool) : List Piece :=
  (List.range (trailingCount .three w+1)).map (eStem cellData O E w plus) ++
  (List.range (2*(trailingCount .three w+1)-(if elong then 0 else 1))).map (eHead cellData O E AO AE w plus)

def swapped (w : Word) (plus elong : Bool) : List Piece :=
  (List.range (trailingCount .two w+1)).map (oStem cellData O E w plus) ++
  (List.range (2*(trailingCount .two w+1)-(if elong then 0 else 1))).map (oHead cellData O E AO AE w plus)

set_option maxHeartbeats 400000 in
/-- The stems and heads rotate with the child offset at every one or two exit. -/
theorem pieces (w : Word) (plus elong : Bool)
    (hlast : (stemPrefix w).getLast?=some .one ∨ (stemPrefix w).getLast?=some .two)
    (hS : CellsRot (regOdo cellData O E (regsAt (stemPrefix w)).1 true).dom
      (regOdo cellData O E (regsAt (swapW (stemPrefix w))).2 false).dom (vP1 (stemPrefix w)-((0,1):Site)))
    (hH : CellsRot (regOdo cellData AO AE (regsAt (stemPrefix w)).1 true).dom
      (regOdo cellData AO AE (regsAt (swapW (stemPrefix w))).2 false).dom (altParP (stemPrefix w)).1) :
    CellsRot (pieceUnion (outer w plus elong)) (pieceUnion (swapped (swapW w) (plus != W1Odd w) elong))
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  apply CorrectedCellRotation.union
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_three w
  have hWw := W1Odd_swapW w
  have hpw : parentsAt w = ⟨(parentsAt (stripTrailing Digit.three w)).odd, ⟨(parentsAt (stripTrailing Digit.three w)).even.num +
      2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.num,
      (parentsAt (stripTrailing Digit.three w)).even.den + 2 * (trailingCount Digit.three w : ℕ) * (parentsAt (stripTrailing Digit.three w)).odd.den⟩⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact parents_append_threes _ _
  have hpsw : parentsAt (swapW w) = ⟨⟨(parentsAt (swapW (stripTrailing Digit.three w))).odd.num +
      (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.num,
      (parentsAt (swapW (stripTrailing Digit.three w))).odd.den + (trailingCount Digit.three w : ℕ) * (parentsAt (swapW (stripTrailing Digit.three w))).even.den⟩,
      (parentsAt (swapW (stripTrailing Digit.three w))).even⟩ := by
    conv_lhs => rw [← strip_append_replicate Digit.three w, swapW_append, swapW_replicate]
    exact parents_append_twos _ _
  have hWo : W1Odd w = W1Odd (stripTrailing Digit.three w) := by
    conv_lhs => rw [← strip_append_replicate Digit.three w]
    exact W1Odd_append_replicate _ _ _ (by decide)
  obtain ⟨-, -, -, -, e5, e6⟩ := vecs_swapW (stripTrailing Digit.three w)
  have hq : ((parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.den) % 2 = 0 := (parentsAt_valid _).even_parity
  obtain ⟨a, hdq⟩ : ∃ a : ℤ, (parentsAt (stripTrailing Digit.three w)).even.den = 2 * a + (parentsAt (stripTrailing Digit.three w)).even.num :=
    ⟨((parentsAt (stripTrailing Digit.three w)).even.den - (parentsAt (stripTrailing Digit.three w)).even.num) / 2, by omega⟩
  have hA : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num - (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a := by omega
  have hB' : (2 * a + (parentsAt (stripTrailing Digit.three w)).even.num + (parentsAt (stripTrailing Digit.three w)).even.num) / 2 = a + (parentsAt (stripTrailing Digit.three w)).even.num := by omega
  unfold outer swapped
  rw [hsw2]
  apply List.rel_append
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro j _
    apply CorrectedCellRotation.placed (u := vP1 (stemPrefix w)-((0,1):Site))
    · simp only [eStem,oStem,stdPiece,hsw1]; exact hS
    · unfold eStem oStem eK oK
      simp only [hsw1]
      rcases hlast with hl|hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;>
        l_unfold <;> simp only [hdq] <;> simp only [hA,hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro j _
    apply CorrectedCellRotation.placed (u := (altParP (stemPrefix w)).1)
    · simp only [eHead,oHead,hsw1]; exact hH
    · unfold eHead oHead eK oK
      simp only [hsw1,hsw2]
      rcases hlast with hl|hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;>
        l_unfold <;> simp only [hdq] <;> simp only [hA,hB'] <;> l_ring

/-- The prescribed rotation for the actual stem and head parents, including the first exit. -/
theorem at_exit (w u : Word) (one plus elong : Bool) (pre : stemPrefix w=u++[exit one]) :
    CellsRot (pieceUnion (outer w plus elong)) (pieceUnion (swapped (swapW w) (plus != W1Odd w) elong))
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  have reg : (regsAt (stemPrefix w)).1=some u := by
    rw [pre,WeakStepPaper.regsAt_snoc]; cases one <;> rfl
  have S := regsAt_swapW (stemPrefix w)
  have o := (parents_of_regs (stemPrefix w)).1 u reg
  have d : exit one=.one ∨ exit one=.two := by cases one <;> simp [exit]
  have cf := altCf_odd_reg u (exit one) d
  rw [←pre] at cf
  apply pieces w plus elong
  · rw [pre]; cases one <;> simp [exit]
  · simp only [S,reg,Option.map_some,regOdo,domOdo,O,E,vP1,←o]
    exact CorrectedCellRotation.odd u
  · simp only [S,reg,Option.map_some,regOdo,domOdo,AO,AE,←cf]
    exact CorrectedCellRotation.alt_odd u

end FLatticePaper.Tiles.CorrectedOuterRotation
