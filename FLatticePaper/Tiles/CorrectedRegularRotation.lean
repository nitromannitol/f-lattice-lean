import FLatticePaper.Tiles.CorrectedCellRotation

/-! Rotation of the entire regular L-column in the prescribed child coordinates. -/

namespace FLatticePaper.Tiles.CorrectedRegularRotation

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps SurgicalWeak SurgicalAlt SurgicalDict JointRot
open CorrectedEvenPlacement CorrectedPlacementFrames CorrectedCellRotation

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)

set_option maxHeartbeats 400000 in
/-- Rotation of a regular corrected column, before pairing its two placements in the child. -/
theorem cells (w : Word) (plus elong : Bool) (hd : enlarged w=false)
    (hlast : (stemPrefix w).getLast?=some .one ∨ (stemPrefix w).getLast?=some .two)
    (hS : CellsRot (regOdo cellData O E (regsAt (stemPrefix w)).1 true).dom
      (regOdo cellData O E (regsAt (swapW (stemPrefix w))).2 false).dom (vP1 (stemPrefix w)-((0,1):Site)))
    (hB : CellsRot (regOdo cellData O E (regsAt (stemPrefix w)).2 false).dom
      (regOdo cellData O E (regsAt (swapW (stemPrefix w))).1 true).dom (vQ1 (stemPrefix w)-((0,1):Site)))
    (hH : CellsRot (regOdo cellData AO AE (regsAt (stemPrefix w)).1 true).dom
      (regOdo cellData AO AE (regsAt (swapW (stemPrefix w))).2 false).dom (altParP (stemPrefix w)).1) :
    CellsRot (evenLCells w plus elong) (oddLCells (swapW w) (plus != W1Odd w) elong)
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  apply CorrectedCellRotation.union
  change List.Forall₂ _ (evenLPieces cellData O E AO AE w plus elong)
    (oddLPieces cellData O E AO AE (swapW w) (plus != W1Odd w) elong)
  unfold enlarged at hd
  obtain ⟨hsw1, hsw2⟩ := swapW_strip_three w
  have hWw := W1Odd_swapW w
  have htrip : (!(swapW (stripTrailing Digit.three w)).isEmpty && (swapW (stripTrailing Digit.three w)).all (fun d => decide (d = Digit.three))) = false := by
    rw [isEmpty_swapW, all_swapW_three]; exact hd
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
  simp only [evenLPieces, oddLPieces, hsw1, hsw2, hWw, hd, htrip, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    List.append_nil]
  refine List.rel_append (List.rel_append ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)) ?_
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro j _
    apply CorrectedCellRotation.placed hS
    rcases hlast with hl|hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;>
      l_unfold <;> simp only [hdq] <;> simp only [hA,hB'] <;> l_ring
  · apply CorrectedCellRotation.placed hB
    rcases hlast with hl|hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;>
      l_unfold <;> simp only [hdq] <;> simp only [hA,hB'] <;> l_ring
  · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro i _
    apply CorrectedCellRotation.placed hH
    rcases hlast with hl|hl <;> cases hWs : W1Odd (stripTrailing Digit.three w) <;> cases plus <;>
      l_unfold <;> simp only [hdq] <;> simp only [hA,hB'] <;> l_ring

/-- The three register rotations hold for actual standard and alternate parent tiles at any non-base exit. -/
theorem at_exit (w u : Word) (one plus elong : Bool) (pre : stemPrefix w=u++[exit one])
    (hn : ¬IsBase (stemPrefix w)) :
    CellsRot (evenLCells w plus elong) (oddLCells (swapW w) (plus != W1Odd w) elong)
      (texV1Even ((parentsAt w).current .even)-((0,1):Site)) := by
  have hd : enlarged w=false := by
    cases hh : enlarged w
    · rfl
    · exfalso; apply hn; right; right
      simp only [enlarged,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh
      exact hh.2
  have last : (stemPrefix w).getLast?=some .one ∨ (stemPrefix w).getLast?=some .two := by
    rw [pre]; cases one <;> simp [exit]
  have S := regsAt_swapW (stemPrefix w)
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := regs_some _ hn
  obtain ⟨o,e⟩ := parents_of_regs (stemPrefix w)
  apply cells w plus elong hd last
  · simp only [S,hx,hy,Option.map_some,regOdo,domOdo,O,E,vP1,←o x hx]
    exact CorrectedCellRotation.odd x
  · simp only [S,hx,hy,Option.map_some,regOdo,domOdo,O,E,vQ1,←e y hy]
    exact CorrectedCellRotation.even y
  · have reg : (regsAt (stemPrefix w)).1=some u := by
      rw [pre,WeakStepPaper.regsAt_snoc]; cases one <;> rfl
    have d : exit one=.one ∨ exit one=.two := by cases one <;> simp [exit]
    have cf := altCf_odd_reg u (exit one) d
    rw [←pre] at cf
    simp only [S,reg,Option.map_some,regOdo,domOdo,AO,AE,←cf]
    exact CorrectedCellRotation.alt_odd u

end FLatticePaper.Tiles.CorrectedRegularRotation
