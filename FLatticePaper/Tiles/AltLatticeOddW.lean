import FLatticePaper.Tiles.AltGlueOdd
import FLatticePaper.Tiles.AltItem3Exterior

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`, the odd child along `W = v_{p₀,2}`: the self-overlap

For `w = u x`, `x ∈ {1, 3}`, every `y` with `y, y + W ∈ T̂(p₀)` lies in `T(p₁)^{+,1}` (the complete overlap `T(p₁)^{-,2} = T(p₁)^{+,1} + W`),
or in one of four regions: `(Q^+, P^{-,1} + W)`, `(P^{+,2}, Q^- + W)`, the contact `(H, Q^- + W)` and `(Q^+, H + W)`
(`classify_W`). The other pairs of pieces do not meet: by `L_r` (`AltItem4OddH.sepr`) and its half-turn, by `L_q`
(`sepq_P`, `sepq_H`), by the midpoint of the closed form, by `L_p`, by the `N`-functional of `AltItem4Special`, and by the
boxes of the closed forms. -/

namespace FLatticePaper.Tiles.AltLatticeOddW

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.AltItem4 (latV hOdd)
open FLatticePaper.Tiles.SiteInduction (InH)

/-- Two points of a copy of `T(p₁)` differing by `W` do not exist (`L_p(W) = T_p + L_p(V)`). -/
theorem sep_pp {w : Word} (hw : ¬ IsBase w) (a y : Site) (h1 : y ∈ shift (stateAt w).tOdd a)
    (h2 : y + latV w false 0 1 ∈ shift (stateAt w).tOdd a) : False := by
  rw [mem_pCopy_iff hw] at h1 h2
  obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨i1, i2, -, -⟩ := h1
  obtain ⟨j1, j2, -, -⟩ := h2
  generalize decide (((y - a).1 + (y - a).2) % 2 = 0) = b1 at i1 i2
  generalize decide (((y + latV w false 0 1 - a).1 + (y + latV w false 0 1 - a).2) % 2 = 0) = b2 at j1 j2
  have A1 := AltItem3.aOf_bounds _ ⟨k1, k2⟩ b1 b2
  have A2 := AltItem3.aOf_bounds _ ⟨k1, k2⟩ b2 b1
  simp only [SiteInduction.tCo, SiteInduction.tOf, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO,
    Parents.current, Parents.combine, texV1Odd, texV2, Bool.false_eq_true, if_false, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub] at i1 i2 j1 j2
  nlinarith [mul_pos k1 k3, mul_pos (sub_pos.2 k2) (sub_pos.2 k4), mul_pos (sub_pos.2 k2) k3, mul_pos k1 (sub_pos.2 k4),
    mul_pos (sub_pos.2 k2) k1, mul_pos (sub_pos.2 k4) k3]

/-- The midpoint of the closed form: two copies of `T(p₁)` symmetric about a third contain no point outside it. -/
theorem mid_P {w : Word} (hw : ¬ IsBase w) (aJ aK a3 : Site) (hsum : aJ + aK + latV w false 0 1 = a3 + a3)
    (hpar : ((a3 - aJ).1 + (a3 - aJ).2) % 2 = 0) (y : Site) (h1 : y + latV w false 0 1 ∈ shift (stateAt w).tOdd aJ)
    (h2 : y ∈ shift (stateAt w).tOdd aK) : y + latV w false 0 1 ∈ shift (stateAt w).tOdd a3 := by
  rw [mem_pCopy_iff hw] at h1 h2 ⊢
  refine AltItem4.inH_mid _ _ (a3 - aJ) hpar ?_ ?_
  · convert h1 using 1; abel
  · convert h2 using 1
    have e : aK = a3 + a3 - aJ - latV w false 0 1 := by rw [← hsum]; abel
    rw [e]; abel

/-- `Q^- ` and `Q^+ + W` do not meet (the boxes of the closed form). -/
theorem sep_qq {w : Word} (hw : ¬ IsBase w) (y : Site)
    (h1 : y + latV w false 0 1 ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus))
    (h2 : y ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus)) :
    False := by
  rw [mem_qCopy_iff hw] at h1 h2
  obtain ⟨-, ⟨k3, k4⟩, -, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨k1, k2, -, -, -, -, -⟩ := parents_facts hw
  have b1 := inH_box _ k3 k4 _ h1
  have b2 := inH_box _ k3 k4 _ h2
  rw [hmq] at b1 b2
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] at b1 b2 <;>
    simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true] at b1 b2 <;> omega

theorem mid_data (w : Word) (hw : ¬ IsBase w) :
    (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) + latV w false 0 1 =
        (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) ∧
      ((AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) + (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + latV w false 0 1 =
        (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus)) ∧
      (((AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus).1 + ((AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus).2) % 2 = 0 ∧
      (((AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)).1 +
        ((AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)).2) % 2 = 0 := by
  obtain ⟨-, -, -, -, hpo, hqe, -⟩ := parents_facts hw
  rcases Bool.eq_false_or_eq_true (phase w == 1) with h | h <;> rw [h] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try (ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine] <;> ring)) <;>
    (try (simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2]; omega))

/-- **The classification of the self-overlap along `W`.** -/
theorem classify_W (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x])) (y : Site)
    (hy : y ∈ altOddTile AltRotStep.B (u ++ [x])) (hyW : y + latV (u ++ [x]) false 0 1 ∈ altOddTile AltRotStep.B (u ++ [x])) :
    y ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Plus) ∨ (y ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Plus) ∧ y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Minus)) ∨
      (y ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.shP (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even + AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Plus) ∧ y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus)) ∨ (y ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) ∧ y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus)) ∨
      (y ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Plus) ∧ y + latV (u ++ [x]) false 0 1 ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even)) := by
  have hzW : y + latV (u ++ [x]) false 0 1 - latV (u ++ [x]) false 0 1 = y := add_sub_cancel_right _ _
  -- the pieces that cannot carry `y` or `y + W`
  have hK3 : y ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.shP (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even + AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Minus) → False := fun h =>
    AltItem4.sepr u x hx hw _ _ (y + latV (u ++ [x]) false 0 1) (Or.inl ⟨rfl, rfl⟩) hyW (by rw [hzW]; exact h)
  have hK5 : y ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Minus) → False := fun h =>
    AltItem4.sepr u x hx hw _ _ (y + latV (u ++ [x]) false 0 1) (Or.inr ⟨rfl, rfl⟩) hyW (by rw [hzW]; exact h)
  have hD : centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even - y ∈ altOddTile AltRotStep.B (u ++ [x]) := (altOdd_halfTurn (u ++ [x]) y).1 hy
  have hJ0 : y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Plus) → False := fun h => by
    have h' := AltItem4.pcopy_refl hw (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) _ _ h
    rw [AltItem4.refl_P1 hw] at h'
    exact AltItem4.sepr u x hx hw _ _ (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even - y) (Or.inl ⟨rfl, rfl⟩) hD (by convert h' using 1; abel)
  have hJ4 : y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tEven (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .q1Plus) → False := fun h => by
    have h' := AltItem4.qcopy_refl hw (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) _ _ h
    rw [AltItem4.refl_Qp hw] at h'
    exact AltItem4.sepr u x hx hw _ _ (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even - y) (Or.inr ⟨rfl, rfl⟩) hD (by convert h' using 1; abel)
  have hJ3 : y + latV (u ++ [x]) false 0 1 ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.shP (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even + AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Minus) → y ∈ shift (stateAt (u ++ [x])).tOdd (AltRotStep.offP0 (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even .dsP1Plus) := fun h => by
    rw [← AltItem4.overlap_id, AltItem4.mem_shift_shift_iff] at h
    simpa using h
  -- the decompositions
  obtain ⟨y', hy', he⟩ := altOddTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have hy1 := hy
  have hy2 := hyW
  rw [he, AltItem4.altQ1Part_eq _ _ hx, (AltItem4.parent_odd_eq u x hx).1, Finset.mem_union] at hy1 hy2
  rcases hy1 with hy1 | hyH <;> rcases hy2 with hy2 | hzH
  · rw [mem_oddStd_iff] at hy1 hy2
    rcases hy1 with ⟨a, ha, hK⟩ | ⟨a, ha, hK⟩ <;> rcases hy2 with ⟨b, hb, hJ⟩ | ⟨b, hb, hJ⟩ <;>
      simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    · -- `y` and `y + W` in copies of `T(p₁)`
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl hK
      · rcases hb with rfl | rfl | rfl | rfl
        · exact (hJ0 hJ).elim
        · exact (sep_pp hw _ y hK hJ).elim
        · exact Or.inl (hJ3 (mid_P hw _ _ _ (mid_data _ hw).1 (mid_data _ hw).2.2.1 y hJ hK))
        · exact Or.inl (hJ3 hJ)
      · rcases hb with rfl | rfl | rfl | rfl
        · exact (hJ0 hJ).elim
        · exact Or.inl (hJ3 (mid_P hw _ _ _ (mid_data _ hw).2.1 (mid_data _ hw).2.2.2 y hJ hK))
        · exact (sep_pp hw _ y hK hJ).elim
        · exact Or.inl (hJ3 hJ)
      · exact (hK3 hK).elim
    · -- `y` in a copy of `T(p₁)`, `y + W` in a copy of `T(q₁)`
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl hK
      · rcases hb with rfl | rfl
        · exact (hJ4 hJ).elim
        · exact Or.inr (Or.inr (Or.inl ⟨hK, hJ⟩))
      · rcases hb with rfl | rfl
        · exact (hJ4 hJ).elim
        · rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hK hJ
          · exact (AltItem4.sep_odd_true_01_52 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
          · exact (AltItem4.sep_odd_false_01_52 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
      · exact (hK3 hK).elim
    · -- `y` in a copy of `T(q₁)`, `y + W` in a copy of `T(p₁)`
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl | rfl | rfl
        · exact (hJ0 hJ).elim
        · rcases AltBounds.phase_cases (u ++ [x]) with ⟨ho, -⟩ | ⟨ho, -⟩ <;> rw [ho] at hK hJ
          · exact (AltItem4.sep_odd_true_01_14 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
          · exact (AltItem4.sep_odd_false_01_14 hw ho _ hJ ((AltItem4.mem_shift_shift_iff _ _ _ _).2 (by rw [hzW]; exact hK))).elim
        · exact Or.inr (Or.inl ⟨hK, hJ⟩)
        · exact Or.inl (hJ3 hJ)
      · exact (hK5 hK).elim
    · -- both in copies of `T(q₁)`
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact (hJ4 hJ).elim
        · exact (sep_qq hw y hJ hK).elim
      · exact (hK5 hK).elim
  · -- `y + W` in the parent piece
    rw [mem_oddStd_iff] at hy1
    rcases hy1 with ⟨a, ha, hK⟩ | ⟨a, ha, hK⟩ <;> simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    · rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl hK
      · exact (AltItem4.sepq_P u x hx hw _ _ (Or.inl rfl) hzH (by rw [hzW]; exact hK)).elim
      · exact (AltItem4.sepq_P u x hx hw _ _ (Or.inr rfl) hzH (by rw [hzW]; exact hK)).elim
      · exact (hK3 hK).elim
    · rcases ha with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hK, hzH⟩)))
      · exact (hK5 hK).elim
  · -- `y` in the parent piece
    rw [mem_oddStd_iff] at hy2
    have hs := AltItem4.parent_odd_sym u x hx y hyH
    rcases hy2 with ⟨b, hb, hJ⟩ | ⟨b, hb, hJ⟩ <;> simp only [oddPOffs, oddQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
    · rcases hb with rfl | rfl | rfl | rfl
      · exact (hJ0 hJ).elim
      · have h' := AltItem4.pcopy_refl hw (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) _ _ hJ
        rw [AltItem4.refl_P2 hw] at h'
        exact (AltItem4.sepq_P u x hx hw _ _ (Or.inr rfl) hs (by convert h' using 1; abel)).elim
      · have h' := AltItem4.pcopy_refl hw (centreOdd (phase (u ++ [x]) == 1) (parentsAt (u ++ [x])).odd (parentsAt (u ++ [x])).even) _ _ hJ
        rw [AltItem4.refl_M1 hw] at h'
        exact (AltItem4.sepq_P u x hx hw _ _ (Or.inl rfl) hs (by convert h' using 1; abel)).elim
      · exact Or.inl (hJ3 hJ)
    · rcases hb with rfl | rfl
      · exact (hJ4 hJ).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyH, hJ⟩)))
  · exact (AltItem4.sepq_H u x hx hw _ hzH (by rw [hzW]; exact hyH)).elim

end FLatticePaper.Tiles.AltLatticeOddW
