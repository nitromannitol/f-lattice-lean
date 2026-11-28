import FLatticePaper.Tiles.AltGlueHalfTurn
import FLatticePaper.Tiles.AltItem4OddUp

/-! # The half-turn of the glued weak alternate odometer of the odd child (uncorrected words)

At a non-base word `w = u x` with `x ≠ 2`, the decomposition of the odd alternate child has seven pieces: four copies of
`T(p₁)`, two of `T(q₁)`, and the alternate parent `T̂(q₁)` of `u` (`pieces7`, the entries of `tileAltOddPieces` without
L-corrections). The half-turn `y ↦ D - y` about the centre `D` of `T̂(p₀)` permutes them (`T(p₁)^{+,1} ↔ T(p₁)^{-,2}`,
`T(p₁)^{+,2} ↔ T(p₁)^{-,1}`, `T(q₁)^+ ↔ T(q₁)^-`, the parent piece to itself), with affine factors adding up to `E - a` of the
register (`E = 2a_{p₁,2} + a_{q₁,2}`). An odometer respecting the pieces has `Φ(y) = 2(o(D - y) - o(y)) + 2Eᵀy` constant on
each piece; `Φ(D - y) = 2EᵀD - Φ(y)`, so `Φ = EᵀD` on the parent piece, and three overlaps of pieces (one with the parent
piece, at its corner `h`) carry this to one piece of each pair (`glue_halfTurn_odd`). The numerical check on the glued odometers
(the value oracle of the joint family) gives the same identity. -/

namespace FLatticePaper.Tiles.AltGlueOdd

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.AltLatticeCore (HalfTurnId)
open FLatticePaper.Tiles.SiteInduction (InH)

/-! ### Membership in the parent tiles through the closed form -/

theorem mem_tOdd_iff {w : Word} (hw : ¬ IsBase w) (z : Site) : z ∈ (stateAt w).tOdd ↔ InH (parentsAt w).odd z := by
  have h := AltPieces.mem_pCopy_iff hw 0 z
  rwa [AltRotStep.shift_zero, sub_zero] at h

theorem mem_tEven_iff {w : Word} (hw : ¬ IsBase w) (z : Site) : z ∈ (stateAt w).tEven ↔ InH (parentsAt w).even z := by
  have h := AltPieces.mem_qCopy_iff hw 0 z
  rwa [AltRotStep.shift_zero, sub_zero] at h

/-- `InH` from the two parity cases. -/
theorem inH_of (f : Fraction) (z : Site)
    (hev : (z.1 + z.2) % 2 = 0 → SiteInduction.aOf f true - SiteInduction.tOf f ≤ SiteInduction.tCo f z ∧
      SiteInduction.tCo f z ≤ f.den + f.num - SiteInduction.aOf f true ∧ SiteInduction.lOf f true ≤ SiteInduction.sCo f z ∧
      SiteInduction.sCo f z ≤ SiteInduction.muOf f * SiteInduction.tOf f + 2 * f.num - SiteInduction.lOf f true)
    (hodd : (z.1 + z.2) % 2 = 1 → SiteInduction.aOf f false - SiteInduction.tOf f ≤ SiteInduction.tCo f z ∧
      SiteInduction.tCo f z ≤ f.den + f.num - SiteInduction.aOf f false ∧ SiteInduction.lOf f false ≤ SiteInduction.sCo f z ∧
      SiteInduction.sCo f z ≤ SiteInduction.muOf f * SiteInduction.tOf f + 2 * f.num - SiteInduction.lOf f false) :
    InH f z := by
  unfold InH
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with h | h
  · have hb : decide ((z.1 + z.2) % 2 = 0) = true := by simp [h]
    rw [hb]; exact hev h
  · have hb : decide ((z.1 + z.2) % 2 = 0) = false := by simp [h]
    rw [hb]; exact hodd h

/-! ### The common points of the spanning overlaps -/

theorem cert_p_zero {w : Word} (hw : ¬ IsBase w) : ((0 : ℤ), (0 : ℤ)) ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, if_true, if_false, Bool.false_eq_true, hmp] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n1) (d1 - n1),
        min_le_right (2 * n1) (d1 - n1),
        min_le_left (d1 - n1) (3 * n1 - d1),
        min_le_right (d1 - n1) (3 * n1 - d1),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

theorem cert_p_one {w : Word} (hw : ¬ IsBase w) : ((1 : ℤ), (0 : ℤ)) ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, if_true, if_false, Bool.false_eq_true, hmp] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n1) (d1 - n1),
        min_le_right (2 * n1) (d1 - n1),
        min_le_left (d1 - n1) (3 * n1 - d1),
        min_le_right (d1 - n1) (3 * n1 - d1),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

theorem cert_p_A {w : Word} (hw : ¬ IsBase w) : texV1Odd (parentsAt w).odd ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Odd, if_true, if_false, Bool.false_eq_true, hmp] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n1) (d1 - n1),
        min_le_right (2 * n1) (d1 - n1),
        min_le_left (d1 - n1) (3 * n1 - d1),
        min_le_right (d1 - n1) (3 * n1 - d1),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

theorem cert_p_B1 {w : Word} (hw : ¬ IsBase w) : texV2 (parentsAt w).odd + ((1 : ℤ), (0 : ℤ)) ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV2, Prod.fst_add, Prod.snd_add, if_true, if_false, Bool.false_eq_true, hmp] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n1) (d1 - n1),
        min_le_right (2 * n1) (d1 - n1),
        min_le_left (d1 - n1) (3 * n1 - d1),
        min_le_right (d1 - n1) (3 * n1 - d1),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

theorem cert_q_one {w : Word} (hw : ¬ IsBase w) : ((1 : ℤ), (0 : ℤ)) ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n2) (d2 - n2),
        min_le_right (2 * n2) (d2 - n2),
        min_le_left (d2 - n2) (3 * n2 - d2),
        min_le_right (d2 - n2) (3 * n2 - d2),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

set_option maxHeartbeats 400000 in
theorem cert_q_UVB {w : Word} (hw : ¬ IsBase w) (hdd : (parentsAt w).odd.den < (parentsAt w).even.den) (ho : phase w = 1) : texV1Even (parentsAt w).even + texV2 (parentsAt w).even - texV2 (parentsAt w).odd ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rw [if_pos ho] at hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n2) (d2 - n2),
        min_le_right (2 * n2) (d2 - n2),
        min_le_left (d2 - n2) (3 * n2 - d2),
        min_le_right (d2 - n2) (3 * n2 - d2),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hdd) h3, mul_pos (sub_pos.2 hdd) h1, mul_pos (sub_pos.2 hdd) (sub_pos.2 h4), mul_pos (sub_pos.2 hdd) (sub_pos.2 h2)])

set_option maxHeartbeats 400000 in
theorem cert_q_BU {w : Word} (hw : ¬ IsBase w) (hdd : (parentsAt w).odd.den < (parentsAt w).even.den) (ho : phase w ≠ 1) : texV2 (parentsAt w).odd + texV1Even (parentsAt w).even ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rw [if_neg ho] at hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Even, texV2, Prod.fst_add, Prod.snd_add, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n2) (d2 - n2),
        min_le_right (2 * n2) (d2 - n2),
        min_le_left (d2 - n2) (3 * n2 - d2),
        min_le_right (d2 - n2) (3 * n2 - d2),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 hdd) h3, mul_pos (sub_pos.2 hdd) h1, mul_pos (sub_pos.2 hdd) (sub_pos.2 h4), mul_pos (sub_pos.2 hdd) (sub_pos.2 h2)])

theorem cert_q_U {w : Word} (hw : ¬ IsBase w) : texV1Even (parentsAt w).even ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Even, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n2) (d2 - n2),
        min_le_right (2 * n2) (d2 - n2),
        min_le_left (d2 - n2) (3 * n2 - d2),
        min_le_right (d2 - n2) (3 * n2 - d2),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

theorem cert_q_V1 {w : Word} (hw : ¬ IsBase w) : texV2 (parentsAt w).even + ((1 : ℤ), (0 : ℤ)) ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV2, Prod.fst_add, Prod.snd_add, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at * <;>
    first
    | omega
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [min_le_left (2 * n2) (d2 - n2),
        min_le_right (2 * n2) (d2 - n2),
        min_le_left (d2 - n2) (3 * n2 - d2),
        min_le_right (d2 - n2) (3 * n2 - d2),
        mul_pos h1 h3, mul_pos h1 h1, mul_pos h3 h3, mul_pos (sub_pos.2 h2) (sub_pos.2 h4),
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3])

/-! ### The seven pieces and their half-turn partners -/

/-- The centre `v_{p₁,1} + v_{p₁,2} + 1 - i` of the half-turn of `T(p₁)`. -/
def Cp (w : Word) : Site := texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd + ((1 : ℤ), (-1 : ℤ))
/-- The centre of the half-turn of `T(q₁)`. -/
def Cq (w : Word) : Site := texV1Even (parentsAt w).even + texV2 (parentsAt w).even + ((1 : ℤ), (-1 : ℤ))
/-- The centre `D` of the half-turn of `T̂(p₀)` (item (1)). -/
def Dw (w : Word) : Site := AltPieces.centreOdd (W1Odd w) (parentsAt w).odd (parentsAt w).even
/-- The coefficient vector of the alternate parent piece (types one and three). -/
def cH (w : Word) : SurgicalAlt.AltCoeff := if W1Odd w then (1, 1, -1, 0) else (0, 1, 1, 0)

/-- The seven pieces of the odd alternate child of a word of type one or three (the entries of `tileAltOddPieces`). -/
def pieces7 (w : Word) (P Q Qh : PartialOdometer) : List Piece :=
  let Sp := (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1
  let cP := SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus
  let cM := SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus
  let c1 := SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus
  let c2 := SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus
  [stdPiece P (altOff w cP) (altAff w cP), stdPiece P (altOff w cP + Sp) (altAff w cP + aP2 w),
    stdPiece P (altOff w cM) (altAff w cM), stdPiece P (altOff w cM + Sp) (altAff w cM + aP2 w),
    stdPiece Q (altOff w c1) (altAff w c1), stdPiece Q (altOff w c2) (altAff w c2),
    stdPiece Qh (altOff w (cH w)) (altAff w (cH w))]

theorem pieces7_mem (w : Word) (P Q Qh : PartialOdometer) :
    stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) ∈ pieces7 w P Q Qh ∧
    stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1)
      (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w) ∈ pieces7 w P Q Qh ∧
    stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) ∈ pieces7 w P Q Qh ∧
    stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1)
      (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w) ∈ pieces7 w P Q Qh ∧
    stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) ∈ pieces7 w P Q Qh ∧
    stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) ∈ pieces7 w P Q Qh ∧
    stdPiece Qh (altOff w (cH w)) (altAff w (cH w)) ∈ pieces7 w P Q Qh := by
  simp [pieces7]

theorem off_03 (w : Word) :
    altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1 =
      Dw w - Cp w - altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [Dw, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreOdd, Cp] <;> ring

theorem off_12 (w : Word) :
    altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) =
      Dw w - Cp w - (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [Dw, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreOdd, Cp] <;> ring

theorem off_45 (w : Word) :
    altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus) =
      Dw w - Cq w - altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [Dw, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreOdd, Cq] <;> ring

theorem aff_03 (w : Word) :
    altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w) =
      JointFamily.altE w - aP2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, aP2, aQ2, JointFamily.altE, offsetA] <;> ring

theorem aff_12 (w : Word) :
    (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w) + altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) =
      JointFamily.altE w - aP2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, aP2, aQ2, JointFamily.altE, offsetA] <;> ring

theorem aff_45 (w : Word) :
    altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus) + altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus) =
      JointFamily.altE w - aQ2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, aP2, aQ2, JointFamily.altE, offsetA]

theorem off_66 (u : Word) (x : Digit) (hx : x ≠ Digit.two) :
    altOff (u ++ [x]) (cH (u ++ [x])) = Dw (u ++ [x]) - JointFamily.altD u false - altOff (u ++ [x]) (cH (u ++ [x])) := by
  cases x with
  | two => exact absurd rfl hx
  | one =>
    simp only [Dw, cH, W1Odd, AltItem4.phase_snoc_one, altOff, CeilWords.parentsAt_snoc_one]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.altD, texV1Odd, texV1Even, texV2, AltPieces.centreOdd, W1Odd, Parents.current, Parents.combine, h, CeilWords.parentsAt_snoc_one] <;> ring
  | three =>
    simp only [Dw, cH, W1Odd, AltItem4.phase_snoc_three, altOff, CeilWords.parentsAt_snoc_three]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.altD, texV1Odd, texV1Even, texV2, AltPieces.centreOdd, W1Odd, Parents.current, Parents.combine, h, CeilWords.parentsAt_snoc_three] <;> ring

theorem aff_66 (u : Word) (x : Digit) (hx : x ≠ Digit.two) :
    altAff (u ++ [x]) (cH (u ++ [x])) + altAff (u ++ [x]) (cH (u ++ [x])) = JointFamily.altE (u ++ [x]) - JointFamily.altE u := by
  cases x with
  | two => exact absurd rfl hx
  | one =>
    simp only [cH, W1Odd, AltItem4.phase_snoc_one, altAff, JointFamily.altE, aP2, aQ2, CeilWords.parentsAt_snoc_one]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring
  | three =>
    simp only [cH, W1Odd, AltItem4.phase_snoc_three, altAff, JointFamily.altE, aP2, aQ2, CeilWords.parentsAt_snoc_three]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring

/-! ### The half-turn of the glue -/

/-- `Φ(y) = 2(o(D - y) - o(y)) + 2Eᵀy`. -/
def phi (o : PartialOdometer) (D E y : Site) : ℤ := 2 * (o.val (D - y) - o.val y) + 2 * dotS E y

theorem phi_mirror (o : PartialOdometer) (D E y : Site) : phi o D E (D - y) = 2 * dotS E D - phi o D E y := by
  unfold phi
  rw [sub_sub_cancel, AltLatticeCore.dotS_sub]
  ring

/-- On a piece whose half-turn partner is known, `Φ` is constant. -/
theorem phi_of_pieces (o : PartialOdometer) (p q : Piece) (D E : Site) (M bp bq : ℤ)
    (hp : ∀ y ∈ p.placed, o.val y = pieceVal p y + bp) (hq : ∀ y ∈ q.placed, o.val y = pieceVal q y + bq)
    (hr : ∀ y ∈ p.placed, D - y ∈ q.placed ∧
      2 * (pieceVal q (D - y) - pieceVal p y) = dotS (-(2 : ℤ) • E) y + M) :
    ∀ y ∈ p.placed, D - y ∈ q.placed ∧ phi o D E y = M + 2 * (bq - bp) := by
  intro y hy
  obtain ⟨h1, h2⟩ := hr y hy
  refine ⟨h1, ?_⟩
  unfold phi
  rw [hq _ h1, hp _ hy]
  simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h2 ⊢
  linarith

theorem respects_std (o : PartialOdometer) (ps : List Piece) (hR : RespectsPieces o ps) (T : PartialOdometer)
    (off aff : Site) (hm : stdPiece T off aff ∈ ps) :
    ∃ b, ∀ y ∈ (stdPiece T off aff).placed, o.val y = pieceVal (stdPiece T off aff) y + b := by
  obtain ⟨b, hb⟩ := hR.2 _ hm
  exact ⟨b, fun y hy => by rw [hb y hy (by simp [stdPiece])]; rfl⟩

/-- **The half-turn of the glued odd alternate odometer** at a word of type one or three: with the normalised half-turn
identities of the parents, an odometer respecting the seven pieces satisfies `2(o(D - y) - o(y)) = EᵀD - 2Eᵀy`. -/
theorem glue_halfTurn_odd (u : Word) (x : Digit) (hx : x ≠ Digit.two) (hw : ¬ IsBase (u ++ [x]))
    (P Q Qh : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [x])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [x])).tEven)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ Qh.dom)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [x]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [x]) - z) - P.val z) = dotS (aP2 (u ++ [x])) (Cp (u ++ [x])) - 2 * dotS (aP2 (u ++ [x])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [x]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [x]) - z) - Q.val z) = dotS (aQ2 (u ++ [x])) (Cq (u ++ [x])) - 2 * dotS (aQ2 (u ++ [x])) z)
    (HH : ∀ z ∈ Qh.dom, JointFamily.altD u false - z ∈ Qh.dom ∧
      2 * (Qh.val (JointFamily.altD u false - z) - Qh.val z) =
        dotS (JointFamily.altE u) (JointFamily.altD u false) - 2 * dotS (JointFamily.altE u) z)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces7 (u ++ [x]) P Q Qh)) :
    HalfTurnId o (Dw (u ++ [x])) (-(2 : ℤ) • JointFamily.altE (u ++ [x]))
      (dotS (JointFamily.altE (u ++ [x])) (Dw (u ++ [x]))) := by
  set w := u ++ [x] with hwdef
  have hdd := AltItem4.odd_dd u x hx
  -- the constants of the seven pieces
  obtain ⟨b0, hb0⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).1
  obtain ⟨b1, hb1⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.1
  obtain ⟨b2, hb2⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.2.1
  obtain ⟨b3, hb3⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.2.2.1
  obtain ⟨b4, hb4⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.2.2.2.1
  obtain ⟨b5, hb5⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.2.2.2.2.1
  obtain ⟨b6, hb6⟩ := respects_std o _ hR _ _ _ (pieces7_mem w P Q Qh).2.2.2.2.2.2
  -- `Φ` on each piece
  have r0 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b0 b3 hb0 hb3 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (Dw w) _ _ _ _ (JointFamily.altE w)
    (off_03 w) (aff_03 w))
  have r3 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b3 b0 hb3 hb0 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (Dw w) _ _ _ _ (JointFamily.altE w)
    (by rw [off_03 w]; abel) (by rw [add_comm]; exact aff_03 w))
  have r1 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b1 b2 hb1 hb2 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (Dw w) _ _ _ _ (JointFamily.altE w)
    (off_12 w) (aff_12 w))
  have r2 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b2 b1 hb2 hb1 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (Dw w) _ _ _ _ (JointFamily.altE w)
    (by rw [off_12 w]; abel) (by rw [add_comm]; exact aff_12 w))
  have r4 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b4 b5 hb4 hb5 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (Dw w) _ _ _ _ (JointFamily.altE w)
    (off_45 w) (aff_45 w))
  have r5 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b5 b4 hb5 hb4 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (Dw w) _ _ _ _ (JointFamily.altE w)
    (by rw [off_45 w]; abel) (by rw [add_comm]; exact aff_45 w))
  have r6 := phi_of_pieces o _ _ (Dw w) (JointFamily.altE w) _ b6 b6 hb6 hb6 (AltGlueHalfTurn.piece_halfTurn Qh _ _ HH (Dw w) _ _ _ _ (JointFamily.altE w)
    (off_66 u x hx) (by rw [aff_66 u x hx]))
  -- the parent piece is mapped to itself: `Φ = EᵀD` there
  have m6 : altOff w (cH w) ∈ (stdPiece Qh (altOff w (cH w)) (altAff w (cH w))).placed := by
    rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, sub_self]; exact h0
  have N6 : ∀ y ∈ (stdPiece Qh (altOff w (cH w)) (altAff w (cH w))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := by
    intro y hy
    obtain ⟨hy', e1⟩ := r6 y hy
    have e2 := (r6 _ hy').2
    rw [phi_mirror] at e2
    omega
  have final : (∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) → (∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) →
      (∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) → (∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) →
      (∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) → (∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) →
      (∀ y ∈ (stdPiece Qh (altOff w (cH w)) (altAff w (cH w))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w)) →
      HalfTurnId o (Dw w) (-(2 : ℤ) • JointFamily.altE w) (dotS (JointFamily.altE w) (Dw w)) := by
    intro P0 P1 P2 P3 P4 P5 P6 y hy
    have hdom := hR.1
    rw [hdom, JointGlue.mem_pieceUnion] at hy
    obtain ⟨p, hp, hyp⟩ := hy
    have key : Dw w - y ∈ JointFamily.pieceUnion (pieces7 w P Q Qh) ∧ phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := by
      simp only [pieces7, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.2.2.1, (r0 y hyp).1⟩, P0 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.2.1, (r1 y hyp).1⟩, P1 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.1, (r2 y hyp).1⟩, P2 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).1, (r3 y hyp).1⟩, P3 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.2.2.2.2.1, (r4 y hyp).1⟩, P4 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.2.2.2.1, (r5 y hyp).1⟩, P5 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7_mem w P Q Qh).2.2.2.2.2.2, (r6 y hyp).1⟩, P6 y hyp⟩
    refine ⟨by rw [hdom]; exact key.1, ?_⟩
    have k2 := key.2
    unfold phi at k2
    simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at k2 ⊢
    linarith
  rcases Bool.eq_false_or_eq_true (W1Odd w) with ho | ho
  · -- `W₁` odd
    have hph : phase w = 1 := by simpa [W1Odd] using ho
    have ya1 : altOff w (cH w) ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w)).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]; convert cert_p_A hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cH, ho] <;> ring)
    have yb1 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w)).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]; convert cert_p_B1 hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho] <;> ring)
    have yb5 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]; convert cert_q_one hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho])
    have yc3 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1 ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w)).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, sub_self]; rw [hdP]; exact AltGlueOdd.cert_p_zero hw)
    have yc5 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1 ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]; convert cert_q_UVB hw hdd hph using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho] <;> ring)
    have P1 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r1 y hy).2.trans ((r1 _ ya1).2.symm.trans (N6 _ m6))
    have P5 : ∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r5 y hy).2.trans ((r5 _ yb5).2.symm.trans (P1 _ yb1))
    have P3 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r3 y hy).2.trans ((r3 _ yc3).2.symm.trans (P5 _ yc5))
    have P2 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r2 y hy).2.trans ((r2 _ (r1 _ ya1).1).2.symm.trans (by rw [phi_mirror, P1 _ ya1]; ring))
    have P4 : ∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r4 y hy).2.trans ((r4 _ (r5 _ yb5).1).2.symm.trans (by rw [phi_mirror, P5 _ yb5]; ring))
    have P0 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r0 y hy).2.trans ((r0 _ (r3 _ yc3).1).2.symm.trans (by rw [phi_mirror, P3 _ yc3]; ring))
    exact final P0 P1 P2 P3 P4 P5 N6
  · -- `W₁` even
    have hph : phase w ≠ 1 := by simpa [W1Odd] using ho
    have ya4 : altOff w (cH w) ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]; convert cert_q_BU hw hdd hph using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cH, ho])
    have yb0 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, sub_self]; rw [hdP]; exact AltGlueOdd.cert_p_zero hw)
    have yb4 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]; convert cert_q_U hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho])
    have yc2 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]; convert cert_p_one hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho])
    have yc4 : altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed := (by rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]; convert cert_q_V1 hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho])
    have P4 : ∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r4 y hy).2.trans ((r4 _ ya4).2.symm.trans (N6 _ m6))
    have P0 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r0 y hy).2.trans ((r0 _ yb0).2.symm.trans (P4 _ yb4))
    have P2 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r2 y hy).2.trans ((r2 _ yc2).2.symm.trans (P4 _ yc4))
    have P5 : ∀ y ∈ (stdPiece Q (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r5 y hy).2.trans ((r5 _ (r4 _ ya4).1).2.symm.trans (by rw [phi_mirror, P4 _ ya4]; ring))
    have P3 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r3 y hy).2.trans ((r3 _ (r0 _ yb0).1).2.symm.trans (by rw [phi_mirror, P0 _ yb0]; ring))
    have P1 : ∀ y ∈ (stdPiece P (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w)).placed, phi o (Dw w) (JointFamily.altE w) y = dotS (JointFamily.altE w) (Dw w) := fun y hy =>
      (r1 y hy).2.trans ((r1 _ (r2 _ yc2).1).2.symm.trans (by rw [phi_mirror, P2 _ yc2]; ring))
    exact final P0 P1 P2 P3 P4 P5 N6

end FLatticePaper.Tiles.AltGlueOdd
