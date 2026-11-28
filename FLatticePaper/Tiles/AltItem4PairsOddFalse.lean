import FLatticePaper.Tiles.AltItem4Special

/-! # Item (4) of `lemma:alternate_tile_properties`: the pairs of standard copies, odd alternate child, `W₁` even

One lemma for each pair of a standard copy `J` of `T̂` and a standard copy `K` of `T̂` translated by a neighbour vector `v` of
the directions that the proof of the text treats directly (for the even child `v_2`, `v_1 + v_2`, `-v_1 + v_2`; for the odd
child `v_2`). Each lemma reads off its certificate (`AltItem4Defs`): a complete overlap on a copy, the midpoint of an
overlapping copy, two lattice-adjacent translates of a standard tile containing the two copies, two translates at a
non-neighbour lattice vector (no common point), or the boxes of the parents (no common point). The certificates were found
numerically on the Lean-faithful port and hold as identities of the parent entries; the lemmas check them for every word. -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.AltPieces

theorem pair_odd_false_01_00 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (_hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1) = AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [← e]; exact hK'
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_01 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_02 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_03 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    rw [mem_pCopy_iff hw] at hJ hK' ⊢
    have e1 : x - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) := by abel
    have e2 : x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [e1] at hJ; rw [e2] at hK'
    refine inH_mid (parentsAt w).odd _ _ ?_ hJ hK'
    obtain ⟨-, -, -, -, hpo, hqe, -⟩ := parents_facts hw
    simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2]; omega
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_04 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_05 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_10 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (_hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1) = AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [← e]; exact hK'
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_11 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_12 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    rw [mem_pCopy_iff hw] at hJ hK' ⊢
    have e1 : x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) := by abel
    have e2 : x - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [e1] at hJ; rw [e2] at hK'
    refine inH_mid (parentsAt w).odd _ _ ?_ hJ hK'
    obtain ⟨-, -, -, -, hpo, hqe, -⟩ := parents_facts hw
    simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2]; omega
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_13 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exact (sep_odd_false_01_14 hw ho x hJ hK').elim

theorem pair_odd_false_01_15 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_20 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (_hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1) = AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [← e]; exact hK'
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_21 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    rw [mem_pCopy_iff hw] at hJ hK' ⊢
    have e1 : x - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) := by abel
    have e2 : x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) = x - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus - (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [e1] at hJ; rw [e2] at hK'
    refine inH_mid (parentsAt w).odd _ _ ?_ hJ hK'
    obtain ⟨-, -, -, -, hpo, hqe, -⟩ := parents_facts hw
    simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2]; omega
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_22 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_23 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_24 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_25 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_30 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_31 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_32 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_33 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_34 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_35 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hJ, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_40 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (_hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1) = AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [← e]; exact hK'
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_41 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_42 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_43 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_44 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_45 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_50 {w : Word} (_hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (_hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have hc : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    have e : AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1) = AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus := by ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring
    rw [← e]; exact hK'
  simp only [oddCopies, ho]
  exact Or.inl ⟨shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus), List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus, by simp [oddPOffs], rfl⟩), hc, List.mem_append_left _ (List.mem_map.2 ⟨AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus, by simp [oddPOffs], (by rw [shift_shift']; congr 1; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)⟩)⟩

theorem pair_odd_false_01_51 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_odd_false_01_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exact (sep_odd_false_01_52 hw ho x hJ hK').elim

theorem pair_odd_false_01_53 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shP false (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .dsP1Minus + latV w false (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_odd_false_01_54 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := boxes_qq (parentsAt w).even hq hmq _ _ x h1 h2
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    ] at hb
  omega

theorem pair_odd_false_01_55 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) (hK : x - latV w false (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    Concl (oddCopies w) (latV w false (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus + latV w false (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offP0 false (parentsAt w).odd (parentsAt w).even .q1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

end FLatticePaper.Tiles.AltItem4
