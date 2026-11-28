import FLatticePaper.Tiles.AltLatticeCorrO
import FLatticePaper.Tiles.AltLatticeOddWMain

/-! # Item (b) of `lemma:weak_alternate_odometer_properties` at the corrected odd child (after a `2`): assembly

At `w = u 2` the odd alternate tile odometer is the glue of six pieces: `P` on `T(p₁)^{+,1}` and `T(p₁)^{-,2}`, the elongated
L-corrections `o^{L,-}` on `T(p₁)^{+,2}` and `o^{L,+}` on `T(p₁)^{-,1}`, and `Q` on `T(q₁)^±`. With its half-turn, it is lattice
self-compatible along `W = v_{p₀,2}`: on the complete overlap by the half-turn (`AltLatticeOddWMain.R_case`), and on the two
mixed regions as at the other types, the L-correction taking the place of `P` at the contact. When `W₁` is even the contact
`(Q^+, P^{-,1} + W)` is on the top walk of `P`, where `o^{L,+} = P + c₊`; when `W₁` is odd the contact `(P^{+,2}, Q^- + W)` is on
the bottom walk, where `o^{L,-} = P + c₋`. The constants are read off at a point of the vertical side of the L-correction
(`kd_a2`, `kd_b2`), and the other region of each orientation follows by the half-turn. -/

namespace FLatticePaper.Tiles.AltLatticeCorrOMain

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.AltItem4 (latV hOdd)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1 pieceUnion)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.AltGlueOdd (Cp Cq)
open FLatticePaper.Tiles.AltLatticeCore (defect HalfTurnId)
open FLatticePaper.Tiles.SiteInduction (InH)
open FLatticePaper.Tiles.AltLatticeOddWMain (four_partner Cp_eq Cq_eq)

/-- The six pieces of the odd alternate tile odometer at a word ending in `2`. -/
def pieces6c (w : Word) (P Q Lm Lp : PartialOdometer) : List Piece :=
  let Sp := (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1
  let cP := SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus
  let cM := SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus
  let c1 := SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus
  let c2 := SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus
  [stdPiece P (altOff w cP) (altAff w cP), stdPiece Lm (altOff w cP + Sp) (altAff w cP + aP2 w),
    stdPiece Lp (altOff w cM) (altAff w cM), stdPiece P (altOff w cM + Sp) (altAff w cM + aP2 w),
    stdPiece Q (altOff w c1) (altAff w c1), stdPiece Q (altOff w c2) (altAff w c2)]

set_option maxHeartbeats 400000 in
/-- **The mixed contact, `W₁` even, with a correction on `P^{-,1}`**: on `(Q^+, P^{-,1} + W)` the defect is `K₀/4` when the
odometer `L` of `P^{-,1}` is `P + c_L` on the top walk of `P`. -/
theorem regionA_even2 {w : Word} (hw : ¬ IsBase w) (hph : phase w ≠ 1) (P Q L o : PartialOdometer) (βP βQ cL k2 k4 : ℤ)
    (HP : ∀ z ∈ P.dom, Cp w - z ∈ P.dom ∧
      2 * (P.val (Cp w - z) - P.val z) = dotS (aP2 w) (Cp w) - 2 * dotS (aP2 w) z)
    (hdP : P.dom = (stateAt w).tOdd)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hLtop : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd →
      Cp w - y ∈ L.dom ∧ L.val (Cp w - y) = P.val (Cp w - y) + cL)
    (hv2 : ∀ y, y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus ∈ L.dom →
      o.val y = L.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) y + k2)
    (hv4 : ∀ y ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus),
      o.val y = Q.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) y + k4)
    (hk : k2 - k4 = -JointFamily.h0 (texV2 (parentsAt w).even) +
      ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) - βP - cL + βQ)
    (x : Site) (hx : x ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus)) (hxW : x + latV w false 0 1 ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus)) :
    4 * defect o (latV w false 0 1) (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) x = -dotS (-(2 : ℤ) • JointFamily.altE w) (latV w false 0 1) - 2 * dotS (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) (centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - latV w false 0 1) := by
  obtain ⟨⟨k1, k1'⟩, ⟨k2', k3⟩, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  rw [if_neg hph] at hdet
  have ho : (phase w == 1) = false := by simpa using hph
  -- the point in the two parents
  obtain ⟨z, rfl⟩ : ∃ z, x = z + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus := ⟨x - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus, by abel⟩
  have hzq : InH (parentsAt w).even z := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tEven_iff hw z).1 hx
  have hzB : z + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false 0 1 - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus = z + texV2 (parentsAt w).odd := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  have hzp : InH (parentsAt w).odd (z + texV2 (parentsAt w).odd) := by
    rw [mem_shift, hzB] at hxW; exact (AltGlueOdd.mem_tOdd_iff hw _).1 hxW
  have cf := AltLatticeOddW.contact_facts (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den ⟨k1, k1'⟩ ⟨k2', k3⟩
    (by linarith) z.1 z.2 hzq hzp
  -- `Q` on its bottom walk at `z`
  have eQ : Q.val z = βQ := botQ z ((AltGlueOdd.mem_tEven_iff hw z).2 hzq) ((AltGlueOdd.mem_tEven_iff hw _).2 cf.1)
  -- `P` on its top walk at `z + B`, by the half-turn
  obtain ⟨y, hydef⟩ : ∃ y, y = Cp w - (z + texV2 (parentsAt w).odd) := ⟨_, rfl⟩
  have hy1 : y ∈ (stateAt w).tOdd := by
    rw [AltGlueOdd.mem_tOdd_iff hw, hydef, Cp_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hzp
  have hy2 : y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := by
    have e : y + texV2 (parentsAt w).odd = Cp w - z := by rw [hydef]; abel
    rw [e, AltGlueOdd.mem_tOdd_iff hw, Cp_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ cf.2
  have eP := botP y hy1 hy2
  have hLv := hLtop y hy1 hy2
  rw [show Cp w - y = z + texV2 (parentsAt w).odd by rw [hydef]; abel] at hLv
  have hHT := (HP y (by rw [hdP]; exact hy1)).2
  rw [show Cp w - y = z + texV2 (parentsAt w).odd by rw [hydef]; abel, eP, hydef] at hHT
  have h0V := AltSixEven.h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  -- the defect
  unfold defect
  have hm2 : z + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus + latV w false 0 1 - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus ∈ L.dom := by
    rw [hzB]; exact hLv.1
  rw [hv2 _ hm2, hv4 _ hx, hzB, add_sub_cancel_right, eQ, hLv.2]
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cp, JointFamily.altE, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, W1Odd, ho, if_false, Bool.false_eq_true] at hHT hk h0V ⊢
  linarith [hHT, hk, h0V]

set_option maxHeartbeats 400000 in
/-- **The mixed contact, `W₁` odd, for an odometer on `P^{+,2}` known on the bottom walk only**: on `(P^{+,2}, Q^- + W)` the
defect is `K₀/4`. -/
theorem regionB_odd2 {w : Word} (hw : ¬ IsBase w) (hph : phase w = 1) (P Q o : PartialOdometer) (βP βQ k1 k5 : ℤ)
    (HQ : ∀ z ∈ Q.dom, Cq w - z ∈ Q.dom ∧
      2 * (Q.val (Cq w - z) - Q.val z) = dotS (aQ2 w) (Cq w) - 2 * dotS (aQ2 w) z)
    (hdQ : Q.dom = (stateAt w).tEven)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → y ∈ P.dom ∧ P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv1 : ∀ y, y - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) ∈ P.dom →
      o.val y = P.val (y - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w) y + k1)
    (hv5 : ∀ y ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus),
      o.val y = Q.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus)) y + k5)
    (hk : k5 - k1 = JointFamily.h0 (texV2 (parentsAt w).odd) + ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.den * (parentsAt w).even.num -
      (parentsAt w).odd.den + (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2 - (parentsAt w).odd.num) - βQ + βP)
    (x : Site) (hx : x ∈ shift (stateAt w).tOdd (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (hxW : x + latV w false 0 1 ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus)) :
    4 * defect o (latV w false 0 1) (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) x = -dotS (-(2 : ℤ) • JointFamily.altE w) (latV w false 0 1) - 2 * dotS (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) (centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - latV w false 0 1) := by
  obtain ⟨⟨k1', k1''⟩, ⟨k2', k3⟩, hmp, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, hpo, hqe, hdet⟩ := parents_facts hw
  rw [if_pos hph] at hdet
  have ho : (phase w == 1) = true := by simpa using hph
  -- the point in the two parents
  obtain ⟨z, rfl⟩ : ∃ z, x = z + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) := ⟨x - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus), by abel⟩
  have hzp : InH (parentsAt w).odd z := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tOdd_iff hw z).1 hx
  have hzV : z + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) + latV w false 0 1 - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus = z + texV2 (parentsAt w).even := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  have hzq : InH (parentsAt w).even (z + texV2 (parentsAt w).even) := by
    rw [mem_shift, hzV] at hxW; exact (AltGlueOdd.mem_tEven_iff hw _).1 hxW
  have cf := AltLatticeOddW.contact_facts (parentsAt w).even.num (parentsAt w).even.den (parentsAt w).odd.num (parentsAt w).odd.den ⟨k2', k3⟩ ⟨k1', k1''⟩
    (by linarith) z.1 z.2 hzp hzq
  -- `P` on its bottom walk at `z`
  have eP := botP z ((AltGlueOdd.mem_tOdd_iff hw z).2 hzp) ((AltGlueOdd.mem_tOdd_iff hw _).2 cf.1)
  -- `Q` on its top walk at `z + V`, by the half-turn
  obtain ⟨y, hydef⟩ : ∃ y, y = Cq w - (z + texV2 (parentsAt w).even) := ⟨_, rfl⟩
  have hy1 : y ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hydef, Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hzq
  have hy2 : y + texV2 (parentsAt w).even ∈ (stateAt w).tEven := by
    have e : y + texV2 (parentsAt w).even = Cq w - z := by rw [hydef]; abel
    rw [e, AltGlueOdd.mem_tEven_iff hw, Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ cf.2
  have eQ := botQ y hy1 hy2
  have hHT := (HQ y (by rw [hdQ]; exact hy1)).2
  rw [show Cq w - y = z + texV2 (parentsAt w).even by rw [hydef]; abel, eQ, hydef] at hHT
  have h0B := AltSixEven.h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  -- the defect
  unfold defect
  rw [hv5 _ hxW, hv1 (z + (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)) (by rw [add_sub_cancel_right]; exact eP.1), hzV, add_sub_cancel_right, eP.2]
  simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cq, JointFamily.altE, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, W1Odd, ho, if_true, if_false,
    Bool.false_eq_true] at hHT hk h0B ⊢
  linarith [hHT, hk, h0B]

set_option maxHeartbeats 400000 in
/-- The first difference (`W₁` even) for any odometer `P` on `P^{-,1}` with `P(1) = β_P`: `Q^+` and `P^{-,1}` meet at `P^{-,1}`'s point `1`, on the bottom walk of `P`
and the top walk of `Q`. -/
theorem kd_a2 {u : Word} {xd : Digit} (hw : ¬ IsBase (u ++ [xd])) (hph : phase (u ++ [xd]) ≠ 1)
    (P Q : PartialOdometer) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (βP βQ : ℤ)
    (hpin : ((1 : ℤ), (0 : ℤ)) ∈ P.dom ∧ P.val ((1 : ℤ), (0 : ℤ)) = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ) (o : PartialOdometer) (κ : ℕ → ℤ)
    (hv2 : ∀ y, y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) ∈ P.dom → o.val y = P.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Minus)) y + κ 2)
    (hv4 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus), o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Plus)) y + κ 4) :
    κ 2 - κ 4 = -JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).even) +
      ((parentsAt (u ++ [xd])).even.den ^ 2 + 2 * (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).even.num ^ 2) - βP + βQ := by
  have ho : (phase (u ++ [xd]) == 1) = false := by simpa using hph
  have mq1 := AltGlueOdd.cert_q_one hw
  have mV1 := AltGlueOdd.cert_q_V1 hw
  have e4 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ)) - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus = texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)) := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
  have m4 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) := by rw [mem_shift, e4]; exact mV1
  have v2 := hv2 (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ))) (by rw [add_sub_cancel_left]; exact hpin.1)
  have v4 := hv4 _ m4
  rw [add_sub_cancel_left] at v2
  rw [e4] at v4
  have eP := hpin.2
  -- `Q` at `V + 1`, on its top walk
  have hy1 : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) ∈ (stateAt (u ++ [xd])).tEven := by
    rw [← hdQ]; exact (HQ _ (by rw [hdQ]; exact mV1)).1
  have hy2 : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven := by
    have e : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).even = Cq (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) := by abel
    rw [e, ← hdQ]; exact (HQ _ (by rw [hdQ]; exact mq1)).1
  have eQ := botQ _ hy1 hy2
  have hHT := (HQ _ (by rw [hdQ]; exact hy1)).2
  rw [sub_sub_cancel, eQ] at hHT
  have h0V := AltSixEven.h0_even (texV2 (parentsAt (u ++ [xd])).even) (by simp only [texV2]; omega)
  rw [eP] at v2
  rw [v2] at v4
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, altAff, SurgicalAlt.coeffAffine, aQ2, offsetA, Cq, dotS, W1Odd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_false, Bool.false_eq_true, ho] at hHT h0V v4 ⊢
  linarith [hHT, h0V, v4]

set_option maxHeartbeats 400000 in
/-- The second difference (`W₁` odd) with the odometer `L` of `P^{+,2}`, equal to `P + c_L` at `B + 1`: `P^{+,2}` and `Q^-` meet at `Q^-`'s point `1`. -/
theorem kd_b2 {u : Word} {xd : Digit} (hw : ¬ IsBase (u ++ [xd])) (hph : phase (u ++ [xd]) = 1)
    (P Q L : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (βP βQ cL : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ) (o : PartialOdometer) (κ : ℕ → ℤ)
    (hLpin : texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ)) ∈ L.dom ∧
      L.val (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) = P.val (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) + cL)
    (hv1 : ∀ y, y - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) ∈ L.dom → o.val y = L.val (y - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus) + aP2 (u ++ [xd])) y + κ 1)
    (hv5 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus), o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) y + κ 5) :
    κ 5 - κ 1 = JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).odd) +
      ((parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den + (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num -
        (parentsAt (u ++ [xd])).odd.num ^ 2 - (parentsAt (u ++ [xd])).odd.num) - βQ + βP + cL := by
  have ho : (phase (u ++ [xd]) == 1) = true := by simpa using hph
  have m1 := AltGlueOdd.cert_p_one hw
  have mB1 := AltGlueOdd.cert_p_B1 hw
  have mq1 := AltGlueOdd.cert_q_one hw
  have mV1 := AltGlueOdd.cert_q_V1 hw
  have m5 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) := by
    rw [mem_shift, add_sub_cancel_left]; exact mq1
  have e1 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ)) - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) = texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ)) := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2] <;> ring
  have v5 := hv5 _ m5
  have v1 := hv1 (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ))) (by rw [e1]; exact hLpin.1)
  rw [add_sub_cancel_left] at v5
  rw [e1, hLpin.2] at v1
  have eQ : Q.val ((1 : ℤ), (0 : ℤ)) = βQ := botQ _ mq1 (by rw [add_comm]; exact mV1)
  -- `P` at `B + 1`, on its top walk
  have hy1 : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) ∈ (stateAt (u ++ [xd])).tOdd := by
    rw [← hdP]; exact (HP _ (by rw [hdP]; exact mB1)).1
  have hy2 : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd := by
    have e : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).odd = Cp (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) := by abel
    rw [e, ← hdP]; exact (HP _ (by rw [hdP]; exact m1)).1
  have eP := botP _ hy1 hy2
  have hHT := (HP _ (by rw [hdP]; exact hy1)).2
  rw [sub_sub_cancel, eP] at hHT
  have h0B := AltSixEven.h0_even (texV2 (parentsAt (u ++ [xd])).odd) (by simp only [texV2]; omega)
  rw [eQ] at v5
  rw [v5] at v1
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, altAff, SurgicalAlt.coeffAffine, aP2, offsetA, Cp, dotS, W1Odd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, ho] at hHT h0B v1 ⊢
  linarith [hHT, h0B, v1]

set_option maxHeartbeats 400000 in
/-- **Item (b) at the corrected odd child, along `W = v_{p₀,2}`, from the parents** (`w = u 2`): an odometer `o` respecting the six
pieces on `T̂(p₀)`, with the normalised half-turn of `o`, over normalised parents (the half-turns `HP`, `HQ`, the values `β` on the
bottom walks in overlap form), with `o^{L,-} = P + c₋` on the bottom walk of `P` and at `B + 1` when `W₁` is odd, and
`o^{L,+} = P + c₊` on the top walk of `P` and at `1` when `W₁` is even, is lattice self-compatible along `W` with the factor
`a_{p₀,2}`. -/
theorem odd_W_corr (u : Word) (hw : ¬ IsBase (u ++ [Digit.two]))
    (P Q Lm Lp : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [Digit.two])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [Digit.two])).tEven)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [Digit.two]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [Digit.two]) - z) - P.val z) = dotS (aP2 (u ++ [Digit.two])) (Cp (u ++ [Digit.two])) - 2 * dotS (aP2 (u ++ [Digit.two])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [Digit.two]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [Digit.two]) - z) - Q.val z) = dotS (aQ2 (u ++ [Digit.two])) (Cq (u ++ [Digit.two])) - 2 * dotS (aQ2 (u ++ [Digit.two])) z)
    (βP βQ cm cp : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [Digit.two])).tOdd → y + texV2 (parentsAt (u ++ [Digit.two])).odd ∈ (stateAt (u ++ [Digit.two])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [Digit.two])).tEven → y + texV2 (parentsAt (u ++ [Digit.two])).even ∈ (stateAt (u ++ [Digit.two])).tEven → Q.val y = βQ)
    (hLm : ∀ y, y ∈ (stateAt (u ++ [Digit.two])).tOdd → y + texV2 (parentsAt (u ++ [Digit.two])).odd ∈ (stateAt (u ++ [Digit.two])).tOdd → y ∈ Lm.dom ∧ Lm.val y = P.val y + cm)
    (hLmpin : phase (u ++ [Digit.two]) = 1 → texV2 (parentsAt (u ++ [Digit.two])).odd + ((1 : ℤ), (0 : ℤ)) ∈ Lm.dom ∧
      Lm.val (texV2 (parentsAt (u ++ [Digit.two])).odd + ((1 : ℤ), (0 : ℤ))) = P.val (texV2 (parentsAt (u ++ [Digit.two])).odd + ((1 : ℤ), (0 : ℤ))) + cm)
    (hLp : ∀ y, y ∈ (stateAt (u ++ [Digit.two])).tOdd → y + texV2 (parentsAt (u ++ [Digit.two])).odd ∈ (stateAt (u ++ [Digit.two])).tOdd → Cp (u ++ [Digit.two]) - y ∈ Lp.dom ∧ Lp.val (Cp (u ++ [Digit.two]) - y) = P.val (Cp (u ++ [Digit.two]) - y) + cp)
    (hLppin : phase (u ++ [Digit.two]) ≠ 1 → ((1 : ℤ), (0 : ℤ)) ∈ Lp.dom ∧ Lp.val ((1 : ℤ), (0 : ℤ)) = P.val ((1 : ℤ), (0 : ℤ)) + cp)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces6c (u ++ [Digit.two]) P Q Lm Lp)) (hdom : o.dom = altOddTile AltRotStep.B (u ++ [Digit.two]))
    (M : ℤ) (HT : HalfTurnId o (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even) (-(2 : ℤ) • JointFamily.altE (u ++ [Digit.two])) M) :
    JointFamily.LatticeSelfCompatible o (latV (u ++ [Digit.two]) false 0 1) (offsetA ((parentsAt (u ++ [Digit.two])).current .odd).num ((parentsAt (u ++ [Digit.two])).current .odd).den true) := by
  obtain ⟨κ, hval⟩ := AltLatticeOddWMain.respects_kappa o _ hR (fun pc hpc => by
    simp only [pieces6c, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  -- the values on the six pieces
  have pv : ∀ (i : ℕ) (T : PartialOdometer) (of af : Site), (pieces6c (u ++ [Digit.two]) P Q Lm Lp)[i]? = some (stdPiece T of af) →
      ∀ y, y - of ∈ T.dom → y ∈ o.dom ∧ o.val y = T.val (y - of) + dotS af y + κ i := by
    intro i T of af hi y hy
    have hy' : y ∈ (stdPiece T of af).placed := (AltLatticeOddWMain.placed_std T of af y).2 (mem_shift.2 hy)
    refine ⟨?_, by rw [hval i _ hi y hy']; rfl⟩
    rw [hR.1, JointGlue.mem_pieceUnion]
    exact ⟨_, List.mem_of_getElem? hi, hy'⟩
  have esh : AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus + AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even = AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus := add_comm _ _
  have esh' : AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus + AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even = AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus := add_comm _ _
  have hv0 := pv 0 P (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Plus)) rfl
  have hv1 := pv 1 Lm (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus + AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Plus) + aP2 (u ++ [Digit.two])) rfl
  have hv2 := pv 2 Lp (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Minus)) rfl
  have hv3 := pv 3 P (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus + AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Minus) + aP2 (u ++ [Digit.two])) rfl
  have hv4 := pv 4 Q (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .q1Plus)) rfl
  have hv5 := pv 5 Q (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus) (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .q1Minus)) rfl
  rw [esh] at hv1
  rw [esh'] at hv3
  have hv0' : ∀ y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus), y ∈ o.dom ∧ o.val y = P.val (y - AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) + dotS (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Plus)) y + κ 0 :=
    fun y hy => hv0 y (by rw [hdP]; exact mem_shift.1 hy)
  have hv3' : ∀ y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus), y ∈ o.dom ∧ o.val y = P.val (y - (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus)) + dotS (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .dsP1Minus) + aP2 (u ++ [Digit.two])) y + κ 3 :=
    fun y hy => hv3 y (by rw [hdP]; exact mem_shift.1 hy)
  have hv4' : ∀ y ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus), o.val y = Q.val (y - AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) + dotS (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .q1Plus)) y + κ 4 :=
    fun y hy => (hv4 y (by rw [hdQ]; exact mem_shift.1 hy)).2
  have hv5' : ∀ y ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus), o.val y = Q.val (y - AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus) + dotS (altAff (u ++ [Digit.two]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [Digit.two])) .q1Minus)) y + κ 5 :=
    fun y hy => (hv5 y (by rw [hdQ]; exact mem_shift.1 hy)).2
  -- `o^{L,-}` on the bottom walk of `P`
  have botLm : ∀ y, y ∈ (stateAt (u ++ [Digit.two])).tOdd → y + texV2 (parentsAt (u ++ [Digit.two])).odd ∈ (stateAt (u ++ [Digit.two])).tOdd → y ∈ Lm.dom ∧ Lm.val y = βP + cm := fun y h1 h2 =>
    ⟨(hLm y h1 h2).1, by rw [(hLm y h1 h2).2, botP y h1 h2]⟩
  -- the constants
  have hKa : phase (u ++ [Digit.two]) ≠ 1 → κ 2 - κ 4 = -JointFamily.h0 (texV2 (parentsAt (u ++ [Digit.two])).even) +
      ((parentsAt (u ++ [Digit.two])).even.den ^ 2 + 2 * (parentsAt (u ++ [Digit.two])).even.den * (parentsAt (u ++ [Digit.two])).even.num - (parentsAt (u ++ [Digit.two])).even.num ^ 2) - (βP + cp) + βQ := by
    intro hph
    refine kd_a2 hw hph Lp Q hdQ HQ (βP + cp) βQ ⟨(hLppin hph).1, ?_⟩ botQ o κ (fun y hy => (hv2 y hy).2) hv4'
    rw [(hLppin hph).2, botP _ (AltGlueOdd.cert_p_one hw) (by rw [add_comm]; exact AltGlueOdd.cert_p_B1 hw)]
  have hKb : phase (u ++ [Digit.two]) = 1 → κ 5 - κ 1 = JointFamily.h0 (texV2 (parentsAt (u ++ [Digit.two])).odd) + ((parentsAt (u ++ [Digit.two])).odd.den ^ 2 + 2 * (parentsAt (u ++ [Digit.two])).odd.den * (parentsAt (u ++ [Digit.two])).odd.num - (parentsAt (u ++ [Digit.two])).odd.den * (parentsAt (u ++ [Digit.two])).even.num -
      (parentsAt (u ++ [Digit.two])).odd.den + (parentsAt (u ++ [Digit.two])).even.den * (parentsAt (u ++ [Digit.two])).odd.num - (parentsAt (u ++ [Digit.two])).odd.num ^ 2 - (parentsAt (u ++ [Digit.two])).odd.num) - βQ + βP + cm := fun hph =>
    kd_b2 hw hph P Q Lm hdP HP βP βQ cm botP botQ o κ (hLmpin hph) (fun y hy => (hv1 y hy).2) hv5'
  refine AltLatticeCore.latticeSelfCompatible_of_four o _ _ (-dotS (-(2 : ℤ) • JointFamily.altE (u ++ [Digit.two])) (latV (u ++ [Digit.two]) false 0 1) - 2 * dotS (offsetA ((parentsAt (u ++ [Digit.two])).current .odd).num ((parentsAt (u ++ [Digit.two])).current .odd).den true) (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1)) (fun y hy hyW => ?_)
  have hy' := hy
  have hyW' := hyW
  rw [hdom] at hy' hyW'
  -- the half-turn images of the pieces
  have rP : ∀ a z, z ∈ shift (stateAt (u ++ [Digit.two])).tOdd a → centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - z ∈ shift (stateAt (u ++ [Digit.two])).tOdd (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).odd - a) :=
    fun a z hz => AltItem4.pcopy_refl hw _ a z hz
  have rQ : ∀ b z, z ∈ shift (stateAt (u ++ [Digit.two])).tEven b → centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - z ∈ shift (stateAt (u ++ [Digit.two])).tEven (centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).even - b) :=
    fun b z hz => AltItem4.qcopy_refl hw _ b z hz
  have e45 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).even - (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) = AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus := AltItem4.refl_Qp hw
  have e54 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).even - (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus) = AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus := by rw [← AltItem4.refl_Qp hw]; abel
  have e12 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).odd - (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) = AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus := AltItem4.refl_P2 hw
  have e21 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - AltItem4.stdCentre (parentsAt (u ++ [Digit.two])).odd - (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) = AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus := AltItem4.refl_M1 hw
  have es : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y + latV (u ++ [Digit.two]) false 0 1 = centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - y := by abel
  have es' : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - (y + latV (u ++ [Digit.two]) false 0 1) = centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y := by abel
  rcases AltLatticeCorrO.classify_W2 u hw y hy' hyW' with hr | ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩
  · -- the complete overlap
    exact AltLatticeOddWMain.R_case hw P o _ _ HT (κ 0) (κ 3) hv0' (fun z hz => by
      obtain ⟨h1, h2⟩ := hv3' z hz; exact ⟨h1, by rw [h2]⟩) y hr
  · -- `(Q^+, P^{-,1} + W)`
    rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
    · refine four_partner o _ _ _ _ _ HT y hy hyW ?_
      have m1 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.shP (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even + AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Plus) := by
        have := rP _ _ ha2; rw [e21, es'] at this; exact this
      have m2 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Minus) := by
        have := rQ _ _ ha1; rw [e45, ← es] at this; exact this
      exact regionB_odd2 hw hph Lm Q o (βP + cm) βQ (κ 1) (κ 5) HQ hdQ botLm botQ (fun z hz => (hv1 z hz).2)
        hv5' (by linarith [hKb hph]) _ m1 m2
    · exact regionA_even2 hw (by omega) P Q Lp o βP βQ cp (κ 2) (κ 4) HP hdP botP botQ hLp (fun z hz => (hv2 z hz).2)
        hv4' (by linarith [hKa (by omega)]) y ha1 ha2
  · -- `(P^{+,2}, Q^- + W)`
    rcases AltBounds.phase_cases (u ++ [Digit.two]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
    · exact regionB_odd2 hw hph Lm Q o (βP + cm) βQ (κ 1) (κ 5) HQ hdQ botLm botQ (fun z hz => (hv1 z hz).2)
        hv5' (by linarith [hKb hph]) y hb1 hb2
    · refine four_partner o _ _ _ _ _ HT y hy hyW ?_
      have m1 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y ∈ shift (stateAt (u ++ [Digit.two])).tEven (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .q1Plus) := by
        have := rQ _ _ hb2; rw [e54, es'] at this; exact this
      have m2 : centreOdd (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even - latV (u ++ [Digit.two]) false 0 1 - y + latV (u ++ [Digit.two]) false 0 1 ∈ shift (stateAt (u ++ [Digit.two])).tOdd (AltRotStep.offP0 (phase (u ++ [Digit.two]) == 1) (parentsAt (u ++ [Digit.two])).odd (parentsAt (u ++ [Digit.two])).even .dsP1Minus) := by
        have := rP _ _ hb1; rw [e12, ← es] at this; exact this
      exact regionA_even2 hw (by omega) P Q Lp o βP βQ cp (κ 2) (κ 4) HP hdP botP botQ hLp (fun z hz => (hv2 z hz).2)
        hv4' (by linarith [hKa (by omega)]) _ m1 m2

end FLatticePaper.Tiles.AltLatticeCorrOMain
