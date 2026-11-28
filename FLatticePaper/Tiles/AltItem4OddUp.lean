import FLatticePaper.Tiles.AltItem4OddH

/-! # Item (4) of `lemma:alternate_tile_properties`, the odd alternate child, the direction `W = v₂`

Every point `x` of `T̂(p₀) ∩ (T̂(p₀) + W)` satisfies the conclusion of item (4). The pairs of standard copies are the pair
lemmas (`AltItem4PairsOdd*`); the pairs with the alternate parent piece `H` are `AltItem4OddH`, directly or through the
half-turn `z ↦ D + W - z` of `T̂(p₀) ∪ (T̂(p₀) + W)`, which permutes the standard copies (`pcopy_refl`, `qcopy_refl`). -/

namespace FLatticePaper.Tiles.AltItem4

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile oddChildB evenChildB)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### The half-turn on the standard copies -/

theorem pcopy_refl {w : Word} (hw : ¬ IsBase w) (c a z : Site) (hz : z ∈ shift (stateAt w).tOdd a) :
    c - z ∈ shift (stateAt w).tOdd (c - stdCentre (parentsAt w).odd - a) := by
  rw [mem_pCopy_iff hw] at hz ⊢
  have h := EncUpper.inH_refl _ _ hz
  rw [refl_eq] at h
  convert h using 1; abel

theorem qcopy_refl {w : Word} (hw : ¬ IsBase w) (c b z : Site) (hz : z ∈ shift (stateAt w).tEven b) :
    c - z ∈ shift (stateAt w).tEven (c - stdCentre (parentsAt w).even - b) := by
  rw [mem_qCopy_iff hw] at hz ⊢
  have h := EncUpper.inH_refl _ _ hz
  rw [refl_eq] at h
  convert h using 1; abel

theorem refl_P1 {w : Word} (hw : ¬ IsBase w) :
    centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - stdCentre (parentsAt w).odd - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus = AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus := by
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;> ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, centreOdd, stdCentre, Bool.false_eq_true, hmp] <;> ring

theorem refl_P2 {w : Word} (hw : ¬ IsBase w) :
    centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - stdCentre (parentsAt w).odd - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) = AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus := by
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;> ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, centreOdd, stdCentre, Bool.false_eq_true, hmp] <;> ring

theorem refl_M1 {w : Word} (hw : ¬ IsBase w) :
    centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - stdCentre (parentsAt w).odd - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus = AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus := by
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;> ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, centreOdd, stdCentre, Bool.false_eq_true, hmp] <;> ring

theorem refl_Qp {w : Word} (hw : ¬ IsBase w) :
    centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - stdCentre (parentsAt w).even - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus = AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus := by
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;> ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, centreOdd, stdCentre, Bool.false_eq_true, hmq] <;> ring

/-- `T(p₁)^{+,1} + W = T(p₁)^{-,2}`. -/
theorem overlap_id (w : Word) : AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus + latV w false 0 1 = AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus := by
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;> ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, SiteInduction.curO, Parents.current, Parents.combine, latV, latV1, fracOf, Bool.false_eq_true] <;> ring

/-- **The complete overlap**: a point of `T(p₁)^{-,2} = T(p₁)^{+,1} + W`. -/
theorem concl_overlap {w : Word} (x : Site) (hx : x ∈ shift (stateAt w).tOdd (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    Concl (oddCopies w) (latV w false 0 1) x := by
  have he : AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus + -latV w false 0 1 = AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus := by
    rw [← overlap_id]; abel
  refine Or.inl ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨_, by simp [oddPOffs], rfl⟩), hx, ?_⟩
  rw [shift_shift', he]
  exact List.mem_append_left _ (List.mem_map.2 ⟨_, by simp [oddPOffs], rfl⟩)

/-- The pairs of standard copies. -/
theorem odd_std_std {w : Word} (hw : ¬ IsBase w) (x : Site)
    (h1 : x ∈ AltRotStep.oddStd (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even)
    (h2 : x - latV w false 0 1 ∈ AltRotStep.oddStd (phase w == 1) (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even) :
    Concl (oddCopies w) (latV w false 0 1) x := by
  rw [mem_oddStd_iff] at h1 h2
  rcases AltBounds.phase_cases w with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at h1 h2
  · rcases h1 with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2 with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
      simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      · exact pair_odd_true_01_00 hw ho x hJ hK
      · exact pair_odd_true_01_01 hw ho x hJ hK
      · exact pair_odd_true_01_02 hw ho x hJ hK
      · exact pair_odd_true_01_03 hw ho x hJ hK
      · exact pair_odd_true_01_10 hw ho x hJ hK
      · exact pair_odd_true_01_11 hw ho x hJ hK
      · exact pair_odd_true_01_12 hw ho x hJ hK
      · exact pair_odd_true_01_13 hw ho x hJ hK
      · exact pair_odd_true_01_20 hw ho x hJ hK
      · exact pair_odd_true_01_21 hw ho x hJ hK
      · exact pair_odd_true_01_22 hw ho x hJ hK
      · exact pair_odd_true_01_23 hw ho x hJ hK
      · exact pair_odd_true_01_30 hw ho x hJ hK
      · exact pair_odd_true_01_31 hw ho x hJ hK
      · exact pair_odd_true_01_32 hw ho x hJ hK
      · exact pair_odd_true_01_33 hw ho x hJ hK
    · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
      · exact pair_odd_true_01_04 hw ho x hJ hK
      · exact pair_odd_true_01_05 hw ho x hJ hK
      · exact pair_odd_true_01_14 hw ho x hJ hK
      · exact pair_odd_true_01_15 hw ho x hJ hK
      · exact pair_odd_true_01_24 hw ho x hJ hK
      · exact pair_odd_true_01_25 hw ho x hJ hK
      · exact pair_odd_true_01_34 hw ho x hJ hK
      · exact pair_odd_true_01_35 hw ho x hJ hK
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      · exact pair_odd_true_01_40 hw ho x hJ hK
      · exact pair_odd_true_01_41 hw ho x hJ hK
      · exact pair_odd_true_01_42 hw ho x hJ hK
      · exact pair_odd_true_01_43 hw ho x hJ hK
      · exact pair_odd_true_01_50 hw ho x hJ hK
      · exact pair_odd_true_01_51 hw ho x hJ hK
      · exact pair_odd_true_01_52 hw ho x hJ hK
      · exact pair_odd_true_01_53 hw ho x hJ hK
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact pair_odd_true_01_44 hw ho x hJ hK
      · exact pair_odd_true_01_45 hw ho x hJ hK
      · exact pair_odd_true_01_54 hw ho x hJ hK
      · exact pair_odd_true_01_55 hw ho x hJ hK
  · rcases h1 with ⟨a, ha, hJ⟩ | ⟨a, ha, hJ⟩ <;> rcases h2 with ⟨b, hb, hK⟩ | ⟨b, hb, hK⟩ <;>
      simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      · exact pair_odd_false_01_00 hw ho x hJ hK
      · exact pair_odd_false_01_01 hw ho x hJ hK
      · exact pair_odd_false_01_02 hw ho x hJ hK
      · exact pair_odd_false_01_03 hw ho x hJ hK
      · exact pair_odd_false_01_10 hw ho x hJ hK
      · exact pair_odd_false_01_11 hw ho x hJ hK
      · exact pair_odd_false_01_12 hw ho x hJ hK
      · exact pair_odd_false_01_13 hw ho x hJ hK
      · exact pair_odd_false_01_20 hw ho x hJ hK
      · exact pair_odd_false_01_21 hw ho x hJ hK
      · exact pair_odd_false_01_22 hw ho x hJ hK
      · exact pair_odd_false_01_23 hw ho x hJ hK
      · exact pair_odd_false_01_30 hw ho x hJ hK
      · exact pair_odd_false_01_31 hw ho x hJ hK
      · exact pair_odd_false_01_32 hw ho x hJ hK
      · exact pair_odd_false_01_33 hw ho x hJ hK
    · rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl
      · exact pair_odd_false_01_04 hw ho x hJ hK
      · exact pair_odd_false_01_05 hw ho x hJ hK
      · exact pair_odd_false_01_14 hw ho x hJ hK
      · exact pair_odd_false_01_15 hw ho x hJ hK
      · exact pair_odd_false_01_24 hw ho x hJ hK
      · exact pair_odd_false_01_25 hw ho x hJ hK
      · exact pair_odd_false_01_34 hw ho x hJ hK
      · exact pair_odd_false_01_35 hw ho x hJ hK
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      · exact pair_odd_false_01_40 hw ho x hJ hK
      · exact pair_odd_false_01_41 hw ho x hJ hK
      · exact pair_odd_false_01_42 hw ho x hJ hK
      · exact pair_odd_false_01_43 hw ho x hJ hK
      · exact pair_odd_false_01_50 hw ho x hJ hK
      · exact pair_odd_false_01_51 hw ho x hJ hK
      · exact pair_odd_false_01_52 hw ho x hJ hK
      · exact pair_odd_false_01_53 hw ho x hJ hK
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact pair_odd_false_01_44 hw ho x hJ hK
      · exact pair_odd_false_01_45 hw ho x hJ hK
      · exact pair_odd_false_01_54 hw ho x hJ hK
      · exact pair_odd_false_01_55 hw ho x hJ hK

/-- The pairs `(H, K + W)`. -/
theorem odd_H_std (u : Word) (y : Digit) (hy : y ≠ Digit.two) (hw : ¬ IsBase (u ++ [y])) (x : Site)
    (h1 : x ∈ altOddTile AltRotStep.B (u ++ [y])) (hH : x ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even)) (h2 : x - latV (u ++ [y]) false 0 1 ∈ AltRotStep.oddStd (phase (u ++ [y]) == 1) (stateAt (u ++ [y])).tOdd (stateAt (u ++ [y])).tEven (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) :
    Concl (oddCopies (u ++ [y])) (latV (u ++ [y]) false 0 1) x := by
  rw [mem_oddStd_iff] at h2
  rcases h2 with ⟨a, ha, hK⟩ | ⟨b, hb, hK⟩
  · simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · have h := (mem_shift_shift_iff _ _ _ _).2 hK
      rw [overlap_id] at h
      exact concl_overlap x h
    · exact (sepq_P u y hy hw _ x (Or.inl rfl) hH hK).elim
    · exact (sepq_P u y hy hw _ x (Or.inr rfl) hH hK).elim
    · exact (sepr u y hy hw _ _ x (Or.inl ⟨rfl, rfl⟩) h1 hK).elim
  · simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · have hs := parent_odd_sym u y hy x hH
      have hq := qcopy_refl hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) _ _ hK
      rw [refl_Qp hw] at hq
      have hS := contact u y hy hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even + latV (u ++ [y]) false 0 1 - x) (by convert hq using 1; abel) (by convert hs using 1; abel)
      have h := stackedAt_halfTurn (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even + latV (u ++ [y]) false 0 1) _ hS
      exact Or.inr (by convert h using 1; abel)
    · exact (sepr u y hy hw _ _ x (Or.inr ⟨rfl, rfl⟩) h1 hK).elim

/-- The pairs `(J, H + W)`, through the half-turn `z ↦ D + W - z`. -/
theorem odd_std_H (u : Word) (y : Digit) (hy : y ≠ Digit.two) (hw : ¬ IsBase (u ++ [y])) (x : Site)
    (h2 : x - latV (u ++ [y]) false 0 1 ∈ altOddTile AltRotStep.B (u ++ [y])) (h1 : x ∈ AltRotStep.oddStd (phase (u ++ [y]) == 1) (stateAt (u ++ [y])).tOdd (stateAt (u ++ [y])).tEven (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) (hH : x - latV (u ++ [y]) false 0 1 ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even)) :
    Concl (oddCopies (u ++ [y])) (latV (u ++ [y]) false 0 1) x := by
  have hσH : centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even + latV (u ++ [y]) false 0 1 - x ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) := by
    convert parent_odd_sym u y hy _ hH using 1; abel
  have hσT : centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even + latV (u ++ [y]) false 0 1 - x ∈ altOddTile AltRotStep.B (u ++ [y]) := by
    convert (altOdd_halfTurn (u ++ [y]) _).1 h2 using 1; abel
  rw [mem_oddStd_iff] at h1
  rcases h1 with ⟨a, ha, hJ⟩ | ⟨b, hb, hJ⟩
  · simp only [oddPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · have h := pcopy_refl hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) _ _ hJ
      rw [refl_P1 hw] at h
      exact (sepr u y hy hw _ _ _ (Or.inl ⟨rfl, rfl⟩) hσT (by convert h using 1; abel)).elim
    · have h := pcopy_refl hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) _ _ hJ
      rw [refl_P2 hw] at h
      exact (sepq_P u y hy hw _ _ (Or.inr rfl) hσH (by convert h using 1; abel)).elim
    · have h := pcopy_refl hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) _ _ hJ
      rw [refl_M1 hw] at h
      exact (sepq_P u y hy hw _ _ (Or.inl rfl) hσH (by convert h using 1; abel)).elim
    · exact concl_overlap x hJ
  · simp only [oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · have h := qcopy_refl hw (centreOdd (phase (u ++ [y]) == 1) (parentsAt (u ++ [y])).odd (parentsAt (u ++ [y])).even) _ _ hJ
      rw [refl_Qp hw] at h
      exact (sepr u y hy hw _ _ _ (Or.inr ⟨rfl, rfl⟩) hσT (by convert h using 1; abel)).elim
    · exact Or.inr (contact u y hy hw x hJ hH)

/-- **Item (4), odd alternate child, `v = v₂`**: every point of `T̂(p₀) ∩ (T̂(p₀) + v₂)` lies in a copy `J` of the
decomposition with `J - v₂` a copy too (a complete overlap on a subtile), or in two lattice-adjacent translates of a standard
tile. -/
theorem item4_odd_up {w : Word} (hw : ¬ IsBase w) (x : Site)
    (h1 : x ∈ altOddTile AltRotStep.B w) (h2 : x - latV w false 0 1 ∈ altOddTile AltRotStep.B w) :
    Concl (oddCopies w) (latV w false 0 1) x := by
  obtain ⟨u, y, rfl⟩ := exists_snoc_of_not_base hw
  obtain ⟨y', hy', he⟩ := altOddTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have h1' := h1
  have h2' := h2
  by_cases hy2 : y = Digit.two
  · subst hy2
    rw [he, altQ1Part_two, Finset.union_empty] at h1' h2'
    exact odd_std_std hw x h1' h2'
  rw [he, altQ1Part_eq _ _ hy2, (parent_odd_eq u y hy2).1, Finset.mem_union] at h1' h2'
  rcases h2' with h2s | h2H <;> rcases h1' with h1s | h1H
  · exact odd_std_std hw x h1s h2s
  · exact odd_H_std u y hy2 hw x h1 h1H h2s
  · exact odd_std_H u y hy2 hw x h2 h1s h2H
  · exact (sepq_H u y hy2 hw x h1H h2H).elim

end FLatticePaper.Tiles.AltItem4
