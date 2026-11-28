import FLatticePaper.Tiles.AltItem4Special

/-! # Item (4) of `lemma:alternate_tile_properties`: the pairs of standard copies, even alternate child, `W₁` even

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

theorem pair_even_false_m11_00 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_m11_01 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_pCopy_iff hw _ x).1 hJ
  have h2 := (mem_pCopy_iff hw _ x).1 hK'
  have hb := boxes_pp (parentsAt w).odd hp hmp _ _ x h1 h2
  simp only [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    ] at hb
  omega

theorem pair_even_false_m11_02 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_03 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_04 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_m11_05 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_pCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h1 h2
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem pair_even_false_m11_10 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_11 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_12 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_13 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_15 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_20 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_m11_21 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_pCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h2 h1
  simp only [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    ] at hb
  omega

theorem pair_even_false_m11_22 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_23 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (-1) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (-1) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  exact (even_far (w ++ [Digit.one]) (-1) (1) (by simp [Nbr]) _ x cJ1 eK).elim

theorem pair_even_false_m11_24 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_m11_25 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := boxes_qq (parentsAt w).even hq hmq _ _ x h1 h2
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem pair_even_false_m11_30 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_31 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_32 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_33 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_34 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_35 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_40 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_41 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_42 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_43 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (-2) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (-2) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  exact (even_far w (-2) (1) (by simp [Nbr]) _ x cJ0 eK).elim

theorem pair_even_false_m11_44 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_45 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (-1) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (-1) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  exact (even_far (w ++ [Digit.one]) (-1) (1) (by simp [Nbr]) _ x cJ1 eK).elim

theorem pair_even_false_m11_50 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_51 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (-1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_53 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_54 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_m11_55 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (-1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (-1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (-1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_00 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_01 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.three])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_three hw, phase_snoc_three, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.three])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_three hw, phase_snoc_three, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.three])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.three]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.three]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_three] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.three]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_02 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_03 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_04 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_01_05 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_pCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h1 h2
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem pair_even_false_01_10 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_11 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_12 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_13 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_15 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_20 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_01_21 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_pCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h2 h1
  simp only [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    ] at hb
  omega

theorem pair_even_false_01_22 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_23 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_24 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_01_25 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := boxes_qq (parentsAt w).even hq hmq _ _ x h1 h2
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem pair_even_false_01_30 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_31 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_32 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_33 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_34 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_35 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_40 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_41 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_42 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_43 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_44 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_45 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (-1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))), -1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_50 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (0) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_51 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (0) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_53 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[3]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_54 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_01_55 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (0) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (0) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (0) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven]
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_00 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_01 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.three])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_three hw, phase_snoc_three, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.three])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_three hw, phase_snoc_three, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.three])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.three]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.three]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_three] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.three]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_02 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_03 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_04 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_11_05 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_pCopy_iff hw _ x).1 hJ
  have h2 := (mem_qCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h1 h2
  simp only [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    Prod.fst_neg, Prod.snd_neg] at hb
  omega

theorem pair_even_false_11_10 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_11 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_12 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_13 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_14 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), true, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_15 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_20 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

set_option maxHeartbeats 400000 in
theorem pair_even_false_11_21 {w : Word} (hw : ¬ IsBase w) (_ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exfalso
  obtain ⟨hp, hq, hmp, hmq⟩ := AltItem5.parent_hyps hw
  have h1 := (mem_qCopy_iff hw _ x).1 hJ
  have h2 := (mem_pCopy_iff hw _ x).1 hK'
  have hb := AltItem5.boxes (parentsAt w).odd (parentsAt w).even hp hq hmp hmq _ _ x h2 h1
  simp only [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, if_true, if_false, Bool.false_eq_true, Prod.fst_add, Prod.snd_add,
    ] at hb
  omega

theorem pair_even_false_11_22 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_23 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_24 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_25 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  exact (sep_even_false_11_25 hw ho x hJ hK').elim

theorem pair_even_false_11_30 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), true, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_31 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_32 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), true, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_33 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_34 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsEven]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), true, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsEven]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_35 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_40 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_41 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_42 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_43 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) + latV w true (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, Parents.current, Parents.combine, MixedPieces.qOffsetsEven] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, true, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_44 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_45 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.pOffsetsOdd]))) = (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_50 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Plus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_51 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tOdd (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .p1Minus + latV w true (1) (1)) - ((MixedPieces.pOffsetsEven false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.pOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.pOffsetsOdd, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.pOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_52 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (evenTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hJ (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cJ0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (oddTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) cK0 (by abel)
    rw [oddTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[0]'(by simp [MixedPieces.qOffsetsOdd]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))) + latV (w ++ [Digit.one]) false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), false, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsOdd (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_53 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Plus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_54 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cJ1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) (fun y hy => ?_) cJ0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_P _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (evenTile w) ((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) hK' (by abel)
    rw [evenTile_eq hw, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK1 : x ∈ shift (evenTile (w ++ [Digit.one])) (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) (fun y hy => ?_) cK0 (by abel)
    rw [evenTile_one, phase_snoc_one, ho]
    exact AltBounds.mem_evenChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (evenTile (w ++ [Digit.one])) ((((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0)) := by
    have e : (((AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsEven false (parentsAt w).odd (parentsAt w).even)[1]'(by simp [MixedPieces.qOffsetsEven]))) - ((MixedPieces.qOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[1]'(by simp [MixedPieces.qOffsetsEven]))) = (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))) + latV (w ++ [Digit.one]) true (1) (0) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd, MixedPieces.pOffsetsEven, MixedPieces.qOffsetsEven, CeilWords.parentsAt_snoc_one] <;> ring
    rw [← e]; exact cK1
  refine Or.inr ⟨(w ++ [Digit.one]), true, (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[2]'(by simp [MixedPieces.qOffsetsOdd]))) - ((MixedPieces.pOffsetsEven (!false) (SiteInduction.curO w) (SiteInduction.curE w))[2]'(by simp [MixedPieces.pOffsetsEven]))), 1, 0, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ1
  · simpa [SiteStrings.tileOf] using eK

theorem pair_even_false_11_55 {w : Word} (hw : ¬ IsBase w) (ho : (phase w == 1) = false) (x : Site)
    (hJ : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) (hK : x - latV w true (1) (1) ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus)) :
    Concl (evenCopies w) (latV w true (1) (1)) x := by
  have hK' : x ∈ shift (stateAt w).tEven (AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) := by rw [mem_shift_shift_iff]; exact hK
  have cJ0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hJ (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have cK0 : x ∈ shift (oddTile w) ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) := by
    refine mem_of_copy (e := ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) (fun y hy => ?_) hK' (by abel)
    rw [oddTile_eq hw, ho]
    exact AltBounds.mem_oddChildB_Q _ _ _ _ _ _ y (List.getElem_mem _) hy
  have eK : x ∈ shift (oddTile w) (((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1)) := by
    have e : ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus + latV w true (1) (1)) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[3]'(by simp [MixedPieces.qOffsetsOdd]))) = ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))) + latV w false (0) (1) := by
      ext <;> simp [AltRotStep.offQ0, AltRotStep.shQ, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, latV1, fracOf, SiteInduction.curE, SiteInduction.curO, Parents.current, Parents.combine, MixedPieces.qOffsetsOdd] <;> ring
    rw [← e]; exact cK0
  refine Or.inr ⟨w, false, ((AltRotStep.shQ false (parentsAt w).odd (parentsAt w).even + AltRotStep.offQ0 false (parentsAt w).odd (parentsAt w).even .dsQ1Minus) - ((MixedPieces.qOffsetsOdd false (parentsAt w).odd (parentsAt w).even)[0]'(by simp [MixedPieces.qOffsetsOdd]))), 0, 1, by simp [Nbr], ?_, ?_⟩
  · simpa [SiteStrings.tileOf] using cJ0
  · simpa [SiteStrings.tileOf] using eK

end FLatticePaper.Tiles.AltItem4
