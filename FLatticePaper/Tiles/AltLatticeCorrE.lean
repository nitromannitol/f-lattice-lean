import FLatticePaper.Tiles.AltLatticeCorrArith

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the corrected even child (after a `3`) along `v_{q₀,2}`, geometry

At `w = u 3` the self-overlap of `T̂(q₀)` along `v = v_{q₀,2}` consists of points `x ∈ T(q₁)^{+,1}` with `x + v ∈ T(q₁)^{-,2}`:
the five other pieces are excluded as at the other types (`AltLatticeEvenV`), and the pairs `(T(p₁)^+, T(p₁)^-)`,
`(T(p₁)^+, T(q₁)^{-,2})` (and by the half-turn `(T(q₁)^{+,1}, T(p₁)^-)`) are empty since `d_{q₁} > 2 d_{p₁}`. -/

namespace FLatticePaper.Tiles.AltLatticeCorrE

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1)
open FLatticePaper.Tiles.AltGlueEven (De)
open FLatticePaper.Tiles.SiteInduction (InH curE)

/-- Every point of `T̂(q₀)` at `u 3` lies in one of the six standard copies (no alternate parent at type three). -/
theorem mem_pieces3 (u : Word) (hw : ¬ IsBase (u ++ [Digit.three])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [Digit.three])) :
    y ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) ∨ y ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) ∨ y ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus)) ∨ y ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) ∨ y ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus)) ∨ y ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus)) := by
  obtain ⟨y', hy', he⟩ := AltPieces.altEvenTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have h3 : AltRotStep.altP1Part (phase (u ++ [Digit.three]) == 1) Digit.three (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [Digit.three])).1
      (parentsAt (u ++ [Digit.three])).odd (parentsAt (u ++ [Digit.three])).even = ∅ := by
    simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff]
  rw [he, h3, Finset.union_empty, AltPieces.mem_evenStd_iff] at hy
  rcases hy with ⟨a, ha, hK⟩ | ⟨b, hb, hK⟩
  · simp only [AltPieces.evenPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hK))))
  · simp only [AltPieces.evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl hK
    · exact Or.inr (Or.inl (by rw [add_comm]; exact hK))
    · exact Or.inr (Or.inr (Or.inl hK))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [add_comm]; exact hK))))

set_option maxHeartbeats 400000 in
/-- `(T(p₁)^+, T(q₁)^{-,2})` is empty at type three. -/
theorem sep_PQ3 (u : Word) (hw : ¬ IsBase (u ++ [Digit.three])) (y : Site) (hK : y ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))) (hJ : y + texV2 (curE (u ++ [Digit.three])) ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) : False := by
  obtain ⟨⟨h1, h2⟩, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨t1, t2, t3⟩ := AltLatticeCorrArith.type_three_rel u
  rw [mem_shift] at hK hJ
  have hp := (AltGlueOdd.mem_tOdd_iff hw _).1 hK
  have hq := (AltGlueOdd.mem_tEven_iff hw _).1 hJ
  rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
  · rw [if_pos hph] at hdet
    have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) = ((y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).1, (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).2) + (((parentsAt (u ++ [Digit.three])).even.num - (parentsAt (u ++ [Digit.three])).even.den) - (parentsAt (u ++ [Digit.three])).even.den, ((parentsAt (u ++ [Digit.three])).even.num + (parentsAt (u ++ [Digit.three])).even.den) - (parentsAt (u ++ [Digit.three])).even.num) := by
      ext <;> simp [ho, altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, W1Odd] <;> ring
    rw [e] at hq
    exact AltLatticeCorrArith.mix3_odd _ _ _ _ _ _ h1 h2 hqe hpo t1 t2 t3 hdet hmp hp hq
  · rw [if_neg (by omega)] at hdet
    have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) = ((y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).1, (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).2) + (((parentsAt (u ++ [Digit.three])).even.num - (parentsAt (u ++ [Digit.three])).even.den) + 2 * (parentsAt (u ++ [Digit.three])).even.den - 2 * (parentsAt (u ++ [Digit.three])).odd.den, ((parentsAt (u ++ [Digit.three])).even.num + (parentsAt (u ++ [Digit.three])).even.den) + 2 * (parentsAt (u ++ [Digit.three])).even.num - 2 * (parentsAt (u ++ [Digit.three])).odd.num) := by
      ext <;> simp [ho, altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true, W1Odd] <;> ring
    rw [e] at hq
    exact AltLatticeCorrArith.mix3_even _ _ _ _ _ _ h1 h2 hqe hpo t1 t2 t3 hdet hmq hp hq

set_option maxHeartbeats 400000 in
/-- `(T(p₁)^+, T(p₁)^-)` is empty at type three. -/
theorem sep_PP3 (u : Word) (hw : ¬ IsBase (u ++ [Digit.three])) (y : Site) (hK : y ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))) (hJ : y + texV2 (curE (u ++ [Digit.three])) ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus))) : False := by
  obtain ⟨⟨h1, h2⟩, -, hmp, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨t1, t2, -⟩ := AltLatticeCorrArith.type_three_rel u
  rw [mem_shift] at hK hJ
  have hp := (AltGlueOdd.mem_tOdd_iff hw _).1 hK
  have hq := (AltGlueOdd.mem_tOdd_iff hw _).1 hJ
  rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
  · have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus)) = ((y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).1, (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).2) + ((parentsAt (u ++ [Digit.three])).odd.num - (parentsAt (u ++ [Digit.three])).odd.den - 2 * (parentsAt (u ++ [Digit.three])).even.den, (parentsAt (u ++ [Digit.three])).odd.num + (parentsAt (u ++ [Digit.three])).odd.den - 2 * (parentsAt (u ++ [Digit.three])).even.num) := by
      ext <;> simp [ho, altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, W1Odd] <;> ring
    rw [e] at hq
    exact AltLatticeCorrArith.pp3_minus _ _ _ _ _ _ h1 h2 t1 t2 hmp hp hq
  · have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus)) = ((y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).1, (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus))).2) + ((parentsAt (u ++ [Digit.three])).odd.num - (parentsAt (u ++ [Digit.three])).odd.den + 2 * (parentsAt (u ++ [Digit.three])).even.den, (parentsAt (u ++ [Digit.three])).odd.num + (parentsAt (u ++ [Digit.three])).odd.den + 2 * (parentsAt (u ++ [Digit.three])).even.num) := by
      ext <;> simp [ho, altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true, W1Odd] <;> ring
    rw [e] at hq
    exact AltLatticeCorrArith.pp3_plus _ _ _ _ _ _ h1 h2 t1 t2 hmp hp hq

/-- **The classification at type three**: `x ∈ T(q₁)^{+,1}` and `x + v ∈ T(q₁)^{-,2}`. -/
theorem classify_V3 (u : Word) (hw : ¬ IsBase (u ++ [Digit.three])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [Digit.three])) (hyv : y + texV2 (curE (u ++ [Digit.three])) ∈ altEvenTile AltRotStep.B (u ++ [Digit.three])) :
    y ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) ∧ y + texV2 (curE (u ++ [Digit.three])) ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) := by
  have hJ : y + texV2 (curE (u ++ [Digit.three])) ∈ shift (stateAt (u ++ [Digit.three])).tOdd (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus)) ∨ y + texV2 (curE (u ++ [Digit.three])) ∈ shift (stateAt (u ++ [Digit.three])).tEven (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) := by
    rcases mem_pieces3 u hw _ hyv with h | h | h | h | h | h
    · exact (AltLatticeEvenV.sepJ_0 u Digit.three hw y hy h).elim
    · exact (AltLatticeEvenV.sepJ_1 u Digit.three hw y hy h).elim
    · exact (AltLatticeEvenV.sepJ_2 u Digit.three hw y hy h).elim
    · exact Or.inr h
    · exact (AltLatticeEvenV.sepJ_4 u Digit.three hw y hy h).elim
    · exact Or.inl h
  rcases mem_pieces3 u hw y hy with h | h | h | h | h | h
  · refine ⟨h, ?_⟩
    rcases hJ with hJ | hJ
    · -- `(Q⁺¹, P⁻)`: its half-turn image is `(P⁺, Q⁻²)`
      exfalso
      have e1 := AltItem4.pcopy_refl hw (De (u ++ [Digit.three])) _ _ hJ
      have e2 := AltItem4.qcopy_refl hw (De (u ++ [Digit.three])) _ _ h
      have k1 : De (u ++ [Digit.three]) - AltItem4.stdCentre (parentsAt (u ++ [Digit.three])).odd - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Minus)) = altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .p1Plus) := by
        rw [AltGlueEven.off_45e, AltLatticeOddWMain.Cp_eq hw]; abel
      have k2 : De (u ++ [Digit.three]) - AltItem4.stdCentre (parentsAt (u ++ [Digit.three])).even - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) = altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2 := by
        rw [AltGlueEven.off_03e, AltLatticeOddWMain.Cq_eq hw]
      rw [k1] at e1
      rw [k2] at e2
      refine sep_PQ3 u hw (De (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three])))) e1 ?_
      rw [show De (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three]))) + texV2 (curE (u ++ [Digit.three])) = De (u ++ [Digit.three]) - y by abel]; exact e2
    · exact hJ
  · exact (AltLatticeEvenV.sep_Q1 hw y h hyv).elim
  · exact (AltLatticeEvenV.sep_Q2 hw y h hyv).elim
  · exact (AltLatticeEvenV.sep_Q3 hw y h hyv).elim
  · rcases hJ with hJ | hJ
    · exact (sep_PP3 u hw y h hJ).elim
    · exact (sep_PQ3 u hw y h hJ).elim
  · exact (AltLatticeEvenV.sep_P5 hw y h hyv).elim

theorem aff0_zero (u : Word) : altAff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus) = 0 := by
  rcases Bool.eq_false_or_eq_true (W1Odd (u ++ [Digit.three])) with h | h <;> simp only [h] <;> ext <;> simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, Bool.false_eq_true]

theorem a_eq_E (u : Word) : offsetA (curE (u ++ [Digit.three])).num (curE (u ++ [Digit.three])).den true = JointFamily.altE (u ++ [Digit.three]) := by
  ext <;> simp [aP2, aQ2, offsetA, curE, Parents.current, Parents.combine, JointFamily.altE]; ring

set_option maxHeartbeats 400000 in
/-- **Item (b) at the corrected even child (after a `3`), along `v_{q₀,2}`** (the second-period argument of Case 4): an odometer
on `T̂(q₀)` with the normalised half-turn, which on `T(q₁)^{+,1}` is the elongated `L⁺` placed there, with `L⁺ = β` on the bottom
walk of `T(q₁)` (`l_correct_existence`), is lattice self-compatible along `v_{q₀,2}` with the factor `a_{q₀,2}`: a point of
the overlap and the half-turn image of its translate are both on that bottom walk, so `g = Eᵀ(v - D̂/2)`. -/
theorem even_V_corr (u : Word) (hw : ¬ IsBase (u ++ [Digit.three])) (L o : PartialOdometer) (βL κ0 : ℤ)
    (botL : ∀ y, y ∈ (stateAt (u ++ [Digit.three])).tEven → y + texV2 (parentsAt (u ++ [Digit.three])).even ∈ (stateAt (u ++ [Digit.three])).tEven → y ∈ L.dom ∧ L.val y = βL)
    (hv0 : ∀ y, y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) ∈ L.dom → o.val y = L.val (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) + dotS (altAff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) y + κ0)
    (HT : AltLatticeCore.HalfTurnId o (De (u ++ [Digit.three])) (-(2 : ℤ) • JointFamily.altE (u ++ [Digit.three])) (dotS (JointFamily.altE (u ++ [Digit.three])) (De (u ++ [Digit.three]))))
    (hdom : o.dom = altEvenTile AltRotStep.B (u ++ [Digit.three])) :
    JointFamily.LatticeSelfCompatible o (texV2 (curE (u ++ [Digit.three]))) (offsetA (curE (u ++ [Digit.three])).num (curE (u ++ [Digit.three])).den true) := by
  obtain ⟨-, ⟨k2', k3'⟩, -, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, hqe, hdet⟩ := AltPieces.parents_facts hw
  refine AltLatticeCore.latticeSelfCompatible_of_four o _ _
    (-dotS (-(2 : ℤ) • JointFamily.altE (u ++ [Digit.three])) (texV2 (curE (u ++ [Digit.three]))) - 2 * dotS (offsetA (curE (u ++ [Digit.three])).num (curE (u ++ [Digit.three])).den true) (De (u ++ [Digit.three]) - texV2 (curE (u ++ [Digit.three])))) (fun y hy hyv => ?_)
  have hy' := hy
  have hyv' := hyv
  rw [hdom] at hy' hyv'
  obtain ⟨hK, hJ⟩ := classify_V3 u hw y hy' hyv'
  have hz1 : InH (parentsAt (u ++ [Digit.three])).even (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) := by rw [mem_shift] at hK; exact (AltGlueOdd.mem_tEven_iff hw _).1 hK
  have hz2 : InH (parentsAt (u ++ [Digit.three])).even (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) := by rw [mem_shift] at hJ; exact (AltGlueOdd.mem_tEven_iff hw _).1 hJ
  have hdiff : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) - (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) = texV2 (parentsAt (u ++ [Digit.three])).even +
      (if phase (u ++ [Digit.three]) = 1 then texV1Odd (parentsAt (u ++ [Digit.three])).odd - texV1Even (parentsAt (u ++ [Digit.three])).even else texV1Even (parentsAt (u ++ [Digit.three])).even - texV1Odd (parentsAt (u ++ [Digit.three])).odd) := by
    rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> simp only [hph] <;> norm_num <;>
      ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true, W1Odd, ho] <;> ring
  have ht : SiteInduction.tCo (parentsAt (u ++ [Digit.three])).even (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) = SiteInduction.tCo (parentsAt (u ++ [Digit.three])).even (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) -
      SiteInduction.tOf (parentsAt (u ++ [Digit.three])).even - 2 := by
    have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) = (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) + (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) - (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)))) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨-, hph⟩ | ⟨-, hph⟩ <;> rw [hph] at hdet <;> simp only [hph] at hdet ⊢ <;>
      norm_num at hdet ⊢ <;>
      simp only [SiteInduction.tCo, SiteInduction.tOf, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
        Prod.fst_sub, Prod.snd_sub] <;> linarith
  have hpar : ((y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)).1 + (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)).2) % 2 = ((y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))).1 + (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))).2) % 2 := by
    have e : y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) = (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus))) + (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2) - (y - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)))) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases (u ++ [Digit.three]) with ⟨-, hph⟩ | ⟨-, hph⟩ <;> simp only [hph] <;> norm_num <;>
      simp only [texV1Odd, texV1Even, texV2] <;> omega
  have cc := AltLatticeOddW.contact_c_facts (parentsAt (u ++ [Digit.three])).even.num (parentsAt (u ++ [Digit.three])).even.den ⟨k2', k3'⟩ hqe hmq _ _ hz1 hz2 ht hpar
  obtain ⟨m1, e1⟩ := botL _ ((AltGlueOdd.mem_tEven_iff hw _).2 hz1) ((AltGlueOdd.mem_tEven_iff hw _).2 cc.1)
  have hr1 : AltGlueOdd.Cq (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) ∈ (stateAt (u ++ [Digit.three])).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, AltLatticeOddWMain.Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hz2
  have hr2 : AltGlueOdd.Cq (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) + texV2 (parentsAt (u ++ [Digit.three])).even ∈ (stateAt (u ++ [Digit.three])).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, AltLatticeOddWMain.Cq_eq hw]; exact cc.2
  obtain ⟨m2, e2⟩ := botL _ hr1 hr2
  have k30 : De (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three]))) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Plus)) = AltGlueOdd.Cq (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three])) - (altOff (u ++ [Digit.three]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [Digit.three])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [Digit.three])) (vP2 (u ++ [Digit.three])) (vQ1 (u ++ [Digit.three]))).2)) := by
    have e := AltGlueEven.off_03e (u ++ [Digit.three])
    rw [e]; abel
  have o1 := hv0 y m1
  have o2 := hv0 (De (u ++ [Digit.three]) - (y + texV2 (curE (u ++ [Digit.three])))) (by rw [k30]; exact m2)
  rw [k30, e2] at o2
  rw [e1] at o1
  have h := (HT _ hyv).2
  rw [aff0_zero, a_eq_E] at *
  unfold AltLatticeCore.defect
  simp only [dotS, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] at o1 o2 h ⊢
  linarith

end FLatticePaper.Tiles.AltLatticeCorrE
