import FLatticePaper.Tiles.AltLatticeOddW
import FLatticePaper.Tiles.AltSixOdd

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the odd alternate child along its second period

Assembly for a word `w = u x` of type one or three (no L-correction): an odometer `o` on `T̂(p₀)` that is the glue of the
seven pieces with the explicit constants of the decomposition is lattice self-compatible along `W = v_{p₀,2}` with the
affine factor `a_{p₀,2}`. The defect is `K₀/4` on the complete overlap by the half-turn, and on the four regions by the
values of the parent odometers on their boundary walks. -/

namespace FLatticePaper.Tiles.AltLatticeOddWMain

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.AltPieces
open FLatticePaper.Tiles.AltItem4 (latV hOdd)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1 pieceUnion)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.AltGlueOdd (pieces7 cH Dw Cp Cq)
open FLatticePaper.Tiles.AltLatticeCore (defect HalfTurnId)
open FLatticePaper.Tiles.SiteInduction (InH)

theorem placed_std (T : PartialOdometer) (off aff : Site) (y : Site) :
    y ∈ (stdPiece T off aff).placed ↔ y ∈ shift T.dom off := by
  rw [AltGlueHalfTurn.mem_placed_iff, mem_shift]; rfl

/-- The affine factors of the complete overlap differ by `a_{p₀,2}`. -/
theorem aff_30 (w : Word) :
    (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w) - altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) =
      offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;> simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altP0Coeff, aP2, offsetA, Parents.current, Parents.combine] <;> ring

/-- **The complete overlap**: on `T(p₁)^{+,1}`, whose translate by `W` is `T(p₁)^{-,2}`, the defect is `K₀/4`. -/
theorem R_case {w : Word} (hw : ¬ IsBase w) (P o : PartialOdometer) (L : Site) (M : ℤ)
    (HT : HalfTurnId o (centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even) L M) (k0 k3 : ℤ)
    (hv0 : ∀ y ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus), y ∈ o.dom ∧
      o.val y = P.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)) y + k0)
    (hv3 : ∀ y ∈ shift (stateAt w).tOdd (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus), y ∈ o.dom ∧
      o.val y = P.val (y - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus)) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w) y + k3)
    (y : Site) (hy : y ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)) :
    4 * defect o (latV w false 0 1) (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) y = -dotS L (latV w false 0 1) - 2 * dotS (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) (centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - latV w false 0 1) := by
  have e := AltItem4.overlap_id w
  have hsh : ∀ z, z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus) → z + latV w false 0 1 ∈ shift (stateAt w).tOdd (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) := by
    intro z hz
    rw [← e, AltItem4.mem_shift_shift_iff, add_sub_cancel_right]; exact hz
  refine AltLatticeCore.four_of_invariant o _ L _ _ M HT {z | z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)}
    (fun z hz => ⟨(hv0 z hz).1, (hv3 _ (hsh z hz)).1⟩) (fun z hz => ?_)
    (dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w) (latV w false 0 1) + k3 - k0) (fun z hz => ?_) y hy
  · -- the half-turn maps the complete overlap to itself
    have h' := AltItem4.pcopy_refl hw (centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even) _ _ (hsh z hz)
    have hr : centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - AltItem4.stdCentre (parentsAt w).odd - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) = AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus := by rw [← AltItem4.refl_P1 hw]; abel
    rw [hr] at h'
    show centreOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even - latV w false 0 1 - z ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus)
    convert h' using 1; abel
  · -- the defect is constant there
    show defect o (latV w false 0 1) (offsetA ((parentsAt w).current .odd).num ((parentsAt w).current .odd).den true) z = _
    unfold defect
    rw [(hv3 _ (hsh z hz)).2, (hv0 z hz).2]
    have e2 : z + latV w false 0 1 - (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) = z - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus := by rw [← e]; abel
    rw [e2, ← aff_30 w]
    simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
    ring

theorem Cp_eq {w : Word} (hw : ¬ IsBase w) : Cp w = AltItem4.stdCentre (parentsAt w).odd := by
  obtain ⟨-, -, hmp, -⟩ := AltItem5.parent_hyps hw
  simp only [Cp, AltItem4.stdCentre, hmp, texV1Odd, texV2]; ext <;> simp <;> ring

theorem Cq_eq {w : Word} (hw : ¬ IsBase w) : Cq w = AltItem4.stdCentre (parentsAt w).even := by
  obtain ⟨-, -, -, hmq⟩ := AltItem5.parent_hyps hw
  simp only [Cq, AltItem4.stdCentre, hmq, texV1Even, texV2]; ext <;> simp; ring

set_option maxHeartbeats 400000 in
/-- **The mixed contact, `W₁` even**: on `(Q^+, P^{-,1} + W)` the defect is `K₀/4`. -/
theorem regionA_even {w : Word} (hw : ¬ IsBase w) (hph : phase w ≠ 1) (P Q o : PartialOdometer) (βP βQ k2 k4 : ℤ)
    (HP : ∀ z ∈ P.dom, Cp w - z ∈ P.dom ∧
      2 * (P.val (Cp w - z) - P.val z) = dotS (aP2 w) (Cp w) - 2 * dotS (aP2 w) z)
    (hdP : P.dom = (stateAt w).tOdd)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv2 : ∀ y ∈ shift (stateAt w).tOdd (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus),
      o.val y = P.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Minus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)) y + k2)
    (hv4 : ∀ y ∈ shift (stateAt w).tEven (AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus),
      o.val y = Q.val (y - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Plus) + dotS (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)) y + k4)
    (hk : k2 - k4 = -JointFamily.h0 (texV2 (parentsAt w).even) +
      ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) - βP + βQ)
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
  have hHT := (HP y (by rw [hdP]; exact hy1)).2
  rw [show Cp w - y = z + texV2 (parentsAt w).odd by rw [hydef]; abel, eP, hydef] at hHT
  have h0V := AltSixEven.h0_even (texV2 (parentsAt w).even) (by simp only [texV2]; omega)
  -- the defect
  unfold defect
  rw [hv2 _ hxW, hv4 _ hx, hzB, add_sub_cancel_right, eQ]
  simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cp, JointFamily.altE, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, W1Odd, ho, if_false, Bool.false_eq_true] at hHT hk h0V ⊢
  linarith [hHT, hk, h0V]

set_option maxHeartbeats 400000 in
/-- **The mixed contact, `W₁` odd**: on `(P^{+,2}, Q^- + W)` the defect is `K₀/4`. -/
theorem regionB_odd {w : Word} (hw : ¬ IsBase w) (hph : phase w = 1) (P Q o : PartialOdometer) (βP βQ k1 k5 : ℤ)
    (HQ : ∀ z ∈ Q.dom, Cq w - z ∈ Q.dom ∧
      2 * (Q.val (Cq w - z) - Q.val z) = dotS (aQ2 w) (Cq w) - 2 * dotS (aQ2 w) z)
    (hdQ : Q.dom = (stateAt w).tEven)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv1 : ∀ y ∈ shift (stateAt w).tOdd (AltRotStep.shP (phase w == 1) (parentsAt w).odd (parentsAt w).even + AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .dsP1Plus),
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
  have eP : P.val z = βP := botP z ((AltGlueOdd.mem_tOdd_iff hw z).2 hzp) ((AltGlueOdd.mem_tOdd_iff hw _).2 cf.1)
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
  rw [hv5 _ hxW, hv1 _ hx, hzV, add_sub_cancel_right, eP]
  simp only [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cq, JointFamily.altE, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, W1Odd, ho, if_true, if_false,
    Bool.false_eq_true] at hHT hk h0B ⊢
  linarith [hHT, hk, h0B]

set_option maxHeartbeats 400000 in
/-- **The contact with the parent piece**: on `(H, Q^- + W)` the defect is `K₀/4`. -/
theorem regionC {u : Word} {xd : Digit} (hx : xd ≠ Digit.two) (hw : ¬ IsBase (u ++ [xd])) (Q Qh o : PartialOdometer)
    (βQ βH k5 k6 : ℤ)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven →
      Q.val y = βQ)
    (botH : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven →
      Qh.val y = βH)
    (hv5 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus),
      o.val y = Q.val (y - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) +
        dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) y + k5)
    (hv6 : ∀ y ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even),
      o.val y = Qh.val (y - hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) +
        dotS (altAff (u ++ [xd]) (AltGlueOdd.cH (u ++ [xd]))) y + k6)
    (hk : k5 - k6 = JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).odd) +
      (if phase (u ++ [xd]) = 1 then
        (parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num -
          (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den +
          (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.num ^ 2 -
          (parentsAt (u ++ [xd])).odd.num
      else
        (parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num +
          2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den -
          2 * (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.num ^ 2 -
          (parentsAt (u ++ [xd])).odd.num) - βQ + βH)
    (y : Site) (hy : y ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even))
    (hyW : y + latV (u ++ [xd]) false 0 1 ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus)) :
    4 * defect o (latV (u ++ [xd]) false 0 1)
        (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true) y =
      -dotS (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (latV (u ++ [xd]) false 0 1) -
        2 * dotS (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true)
          (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1) := by
  set w := u ++ [xd] with hwdef
  obtain ⟨-, ⟨k2', k3⟩, -, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, hqe, hdet⟩ := parents_facts hw
  have hin := AltItem4.contact_mem u xd hx hw (y + latV w false 0 1) hyW (by rw [add_sub_cancel_right]; exact hy)
  rw [add_sub_cancel_right] at hin
  set hh := hOdd (phase w == 1) (parentsAt w).odd (parentsAt w).even with hhdef
  obtain ⟨z, rfl⟩ : ∃ z, y = z + hh := ⟨y - hh, by abel⟩
  have hz1 : InH (parentsAt w).even z := by
    rw [mem_shift, add_sub_cancel_right] at hin; exact (AltGlueOdd.mem_tEven_iff hw z).1 hin
  obtain ⟨z2, hz2def⟩ : ∃ z2, z2 = z + hh + latV w false 0 1 - AltRotStep.offP0 (phase w == 1) (parentsAt w).odd (parentsAt w).even .q1Minus := ⟨_, rfl⟩
  have hz2 : InH (parentsAt w).even z2 := by
    rw [mem_shift, ← hz2def] at hyW; exact (AltGlueOdd.mem_tEven_iff hw _).1 hyW
  have hdiff : z2 - z = texV2 (parentsAt w).even + (if phase w = 1 then texV1Odd (parentsAt w).odd else -texV1Odd (parentsAt w).odd) := by
    rw [hz2def, hhdef]
    rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> rw [ho] <;> simp only [hph] <;>
      ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, hOdd] <;> ring
  have ht : SiteInduction.tCo (parentsAt w).even z2 = SiteInduction.tCo (parentsAt w).even z - SiteInduction.tOf (parentsAt w).even - 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> rw [hph] at hdet <;> simp only [hph] at hdet ⊢ <;>
      norm_num at hdet ⊢ <;>
      simp only [SiteInduction.tCo, SiteInduction.tOf, texV1Odd, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
        Prod.snd_neg] <;> linarith
  have hpar : (z2.1 + z2.2) % 2 = (z.1 + z.2) % 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> simp only [hph] <;> norm_num <;>
      simp only [texV1Odd, texV2] <;> omega
  have cc := AltLatticeOddW.contact_c_facts (parentsAt w).even.num (parentsAt w).even.den ⟨k2', k3⟩ hqe hmq z z2 hz1 hz2 ht hpar
  -- `Qh` on the bottom walk of `T(q₁)` at `z`
  have eH : Qh.val z = βH := botH z ((AltGlueOdd.mem_tEven_iff hw z).2 hz1) ((AltGlueOdd.mem_tEven_iff hw _).2 cc.1)
  -- `Q` on its top walk at `z2`, by the half-turn
  obtain ⟨yq, hyq⟩ : ∃ yq, yq = Cq w - z2 := ⟨_, rfl⟩
  have hy1 : yq ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hyq, Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hz2
  have hy2 : yq + texV2 (parentsAt w).even ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hyq, Cq_eq hw]; exact cc.2
  have eQ := botQ yq hy1 hy2
  have hHT := (HQ yq (by rw [hdQ]; exact hy1)).2
  rw [show Cq w - yq = z2 by rw [hyq]; abel, eQ, hyq] at hHT
  have h0B := AltSixEven.h0_even (texV2 (parentsAt w).odd) (by simp only [texV2]; omega)
  -- the defect
  unfold defect
  rw [hv5 _ hyW, hv6 _ hy, add_sub_cancel_right, eH, ← hz2def]
  subst hz2def
  rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> simp only [hph, if_true] at hk <;>
    norm_num at hk <;>
    simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, latV, AltItem4.latV1, AltItem4.fracOf, SiteInduction.curO, Parents.current, Parents.combine, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cq, JointFamily.altE, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hOdd, AltGlueOdd.cH, W1Odd, ho, hhdef, if_true, if_false, Bool.false_eq_true] at hHT hk h0B ⊢ <;>
    linarith [hHT, hk, h0B]

theorem cert_q_zero {w : Word} (hw : ¬ IsBase w) : ((0 : ℤ), (0 : ℤ)) ∈ (stateAt w).tEven := by
  rw [AltGlueOdd.mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  clear hdet
  apply AltGlueOdd.inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, if_true, if_false, Bool.false_eq_true, hmq] at hpar ⊢ <;>
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

/-- The constants of a glue: one per piece. -/
theorem respects_kappa (o : PartialOdometer) (ps : List Piece) (hR : RespectsPieces o ps)
    (hexc : ∀ pc ∈ ps, pc.exc = ∅) :
    ∃ κ : ℕ → ℤ, ∀ (i : ℕ) (pc : Piece), ps[i]? = some pc → ∀ y ∈ pc.placed, o.val y = pieceVal pc y + κ i := by
  have h : ∀ i : ℕ, ∃ b : ℤ, ∀ pc : Piece, ps[i]? = some pc → ∀ y ∈ pc.placed, o.val y = pieceVal pc y + b := by
    intro i
    rcases hi : ps[i]? with _ | pc
    · exact ⟨0, fun pc h => by simp at h⟩
    · obtain ⟨b, hb⟩ := hR.2 pc (List.mem_of_getElem? hi)
      refine ⟨b, fun pc' h' y hy => ?_⟩
      cases h'
      rw [hb y hy (by rw [hexc _ (List.mem_of_getElem? hi)]; exact Set.notMem_empty y)]
      rfl
  choose κ hκ using h
  exact ⟨κ, hκ⟩

set_option maxHeartbeats 400000 in
/-- The first difference of `KDiffs` (`W₁` even): `Q^+` and `P^{-,1}` meet at `P^{-,1}`'s point `1`, on the bottom walk of `P`
and the top walk of `Q`. -/
theorem kd_a {u : Word} {xd : Digit} (hw : ¬ IsBase (u ++ [xd])) (hph : phase (u ++ [xd]) ≠ 1)
    (P Q : PartialOdometer) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (βP βQ : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ) (o : PartialOdometer) (κ : ℕ → ℤ)
    (hv2 : ∀ y ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus), o.val y = P.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Minus)) y + κ 2)
    (hv4 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus), o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Plus)) y + κ 4) :
    κ 2 - κ 4 = -JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).even) +
      ((parentsAt (u ++ [xd])).even.den ^ 2 + 2 * (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).even.num ^ 2) - βP + βQ := by
  have ho : (phase (u ++ [xd]) == 1) = false := by simpa using hph
  have m1 := AltGlueOdd.cert_p_one hw
  have mB1 := AltGlueOdd.cert_p_B1 hw
  have mq1 := AltGlueOdd.cert_q_one hw
  have mV1 := AltGlueOdd.cert_q_V1 hw
  have m2 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) := by
    rw [mem_shift, add_sub_cancel_left]; exact m1
  have e4 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ)) - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus = texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)) := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
  have m4 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) := by rw [mem_shift, e4]; exact mV1
  have v2 := hv2 _ m2
  have v4 := hv4 _ m4
  rw [add_sub_cancel_left] at v2
  rw [e4] at v4
  have eP : P.val ((1 : ℤ), (0 : ℤ)) = βP := botP _ m1 (by rw [add_comm]; exact mB1)
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
/-- The second difference of `KDiffs` (`W₁` odd): `P^{+,2}` and `Q^-` meet at `Q^-`'s point `1`. -/
theorem kd_b {u : Word} {xd : Digit} (hw : ¬ IsBase (u ++ [xd])) (hph : phase (u ++ [xd]) = 1)
    (P Q : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (βP βQ : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ) (o : PartialOdometer) (κ : ℕ → ℤ)
    (hv1 : ∀ y ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus), o.val y = P.val (y - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus) + aP2 (u ++ [xd])) y + κ 1)
    (hv5 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus), o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) y + κ 5) :
    κ 5 - κ 1 = JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).odd) +
      ((parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den + (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num -
        (parentsAt (u ++ [xd])).odd.num ^ 2 - (parentsAt (u ++ [xd])).odd.num) - βQ + βP := by
  have ho : (phase (u ++ [xd]) == 1) = true := by simpa using hph
  have m1 := AltGlueOdd.cert_p_one hw
  have mB1 := AltGlueOdd.cert_p_B1 hw
  have mq1 := AltGlueOdd.cert_q_one hw
  have mV1 := AltGlueOdd.cert_q_V1 hw
  have m5 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) := by
    rw [mem_shift, add_sub_cancel_left]; exact mq1
  have e1 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ)) - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) = texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ)) := by
    rw [ho]; ext <;> simp [AltRotStep.offP0, AltRotStep.shP, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, texV1Odd, texV1Even, texV2] <;> ring
  have m1' : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by rw [mem_shift, e1]; exact mB1
  have v5 := hv5 _ m5
  have v1 := hv1 _ m1'
  rw [add_sub_cancel_left] at v5
  rw [e1] at v1
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
/-- The third difference of `KDiffs`: `κ₅ - κ₄` from the half-turn of the glue at the origin of `Q^+`, `κ₄ - κ₀` at a corner
contact of `Q^+` and `P^{+,1}`, and `κ₀ - κ₆` at a point of `P^{+,1}` on the top walk of `P` whose point in the parent piece is
on the bottom walk of `T(q₁)`. -/
theorem kd_c {u : Word} {xd : Digit} (hw : ¬ IsBase (u ++ [xd]))
    (P Q Qh : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (βP βQ βH : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botH : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → y ∈ Qh.dom ∧ Qh.val y = βH)
    (hP0 : P.val 0 = βP) (hPA : P.val (texV1Odd (parentsAt (u ++ [xd])).odd) = βP) (hQ0 : Q.val 0 = βQ) (hQU : Q.val (texV1Even (parentsAt (u ++ [xd])).even) = βQ) (o : PartialOdometer)
    (HT : HalfTurnId o (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (dotS (JointFamily.altE (u ++ [xd])) (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even))) (κ : ℕ → ℤ)
    (hv0 : ∀ y ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus), o.val y = P.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus)) y + κ 0)
    (hv4 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus), y ∈ o.dom ∧
      o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Plus)) y + κ 4)
    (hv5 : ∀ y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus), o.val y = Q.val (y - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus)) + dotS (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) y + κ 5)
    (hv6 : ∀ y ∈ shift Qh.dom (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even), o.val y = Qh.val (y - (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even)) + dotS (altAff (u ++ [xd]) (AltGlueOdd.cH (u ++ [xd]))) y + κ 6) :
    κ 5 - κ 6 = JointFamily.h0 (texV2 (parentsAt (u ++ [xd])).odd) +
      (if phase (u ++ [xd]) = 1 then
        (parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den + (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num -
          (parentsAt (u ++ [xd])).odd.num ^ 2 - (parentsAt (u ++ [xd])).odd.num
      else
        (parentsAt (u ++ [xd])).odd.den ^ 2 + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).odd.num + 2 * (parentsAt (u ++ [xd])).odd.den * (parentsAt (u ++ [xd])).even.num - (parentsAt (u ++ [xd])).odd.den -
          2 * (parentsAt (u ++ [xd])).even.den * (parentsAt (u ++ [xd])).odd.num - (parentsAt (u ++ [xd])).odd.num ^ 2 - (parentsAt (u ++ [xd])).odd.num) - βQ + βH := by
  have m0p := AltGlueOdd.cert_p_zero hw
  have m1 := AltGlueOdd.cert_p_one hw
  have mB1 := AltGlueOdd.cert_p_B1 hw
  have mA := AltGlueOdd.cert_p_A hw
  have mq0 := cert_q_zero hw
  have mq1 := AltGlueOdd.cert_q_one hw
  have mV1 := AltGlueOdd.cert_q_V1 hw
  have mU := AltGlueOdd.cert_q_U hw
  have h0B := AltSixEven.h0_even (texV2 (parentsAt (u ++ [xd])).odd) (by simp only [texV2]; omega)
  -- (1) the half-turn of the glue at the origin of `Q^+`
  have m4 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) := by rw [mem_shift, sub_self]; exact mq0
  have eD : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus = Cq (u ++ [xd]) := by
    have e := AltItem4.refl_Qp hw
    rw [← Cq_eq hw] at e
    rw [← e]; abel
  have mC : Cq (u ++ [xd]) ∈ (stateAt (u ++ [xd])).tEven := by
    have h := (HQ _ (by rw [hdQ]; exact mq0)).1
    rw [hdQ] at h; exact (sub_zero (Cq (u ++ [xd]))) ▸ h
  have m5 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) := by rw [mem_shift, eD]; exact mC
  have hT := (HT _ (hv4 _ m4).1).2
  have v4 := (hv4 _ m4).2
  have v5 := hv5 _ m5
  rw [sub_self, hQ0] at v4
  rw [eD] at v5
  have hQC := (HQ _ (by rw [hdQ]; exact mq0)).2
  have z0 : ((0 : ℤ), (0 : ℤ)) = (0 : Site) := rfl
  rw [z0, sub_zero, hQ0] at hQC
  rw [v4, v5] at hT
  -- the `Q`-value on the bottom walk of `T(q₁)` at `U - i` and the top-walk value of `P` at `B + 1`
  have hy1 : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) ∈ (stateAt (u ++ [xd])).tOdd := by
    rw [← hdP]; exact (HP _ (by rw [hdP]; exact mB1)).1
  have hy2 : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd := by
    have e : Cp (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).odd = Cp (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) := by abel
    rw [e, ← hdP]; exact (HP _ (by rw [hdP]; exact m1)).1
  have hP1 : P.val ((1 : ℤ), (0 : ℤ)) = βP := botP _ m1 (by rw [add_comm]; exact mB1)
  rcases AltBounds.phase_cases (u ++ [xd]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
  · -- `W₁` odd
    -- (2) `Q^+` and `P^{+,1}` at `A`
    have e40 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus = texV1Odd (parentsAt (u ++ [xd])).odd := by rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2]
    have m0 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by rw [mem_shift, e40]; exact mA
    have v0 := hv0 _ m0
    rw [e40, hPA] at v0
    -- (3) `P^{+,1}` and `H` at `h + U - i`
    have me : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) ∈ (stateAt (u ++ [xd])).tEven := by
      rw [← hdQ]; exact (HQ _ (by rw [hdQ]; exact mV1)).1
    have meV : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven := by
      have e : Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ))) + texV2 (parentsAt (u ++ [xd])).even = Cq (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) := by abel
      rw [e, ← hdQ]; exact (HQ _ (by rw [hdQ]; exact mq1)).1
    obtain ⟨mH, eH⟩ := botH _ me meV
    have m6 : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + (Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)))) ∈ shift Qh.dom (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) := by
      rw [mem_shift, add_sub_cancel_left]; exact mH
    have e60 : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + (Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)))) - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus = Cp (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) := by
      rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Cp, Cq, hOdd]; ring
    have mC1 : Cp (u ++ [xd]) - ((1 : ℤ), (0 : ℤ)) ∈ (stateAt (u ++ [xd])).tOdd := by rw [← hdP]; exact (HP _ (by rw [hdP]; exact m1)).1
    have m0' : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + (Cq (u ++ [xd]) - (texV2 (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)))) ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by
      rw [mem_shift, e60]; exact mC1
    have v6 := hv6 _ m6
    have v0' := hv0 _ m0'
    rw [add_sub_cancel_left, eH] at v6
    rw [e60] at v0'
    have hPC := (HP _ (by rw [hdP]; exact m1)).2
    rw [hP1] at hPC
    simp only [hph, if_true]
    simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cp, Cq, JointFamily.altE, dotS, hOdd, AltGlueOdd.cH, W1Odd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, if_true, ho] at hT hQC v0 v4 v0' v6 hPC h0B ⊢
    linarith [hT, hQC, v0, v4, v0', v6, hPC, h0B]
  · -- `W₁` even
    -- (2) `P^{+,1}` and `Q^+` at `U`
    have m0 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by rw [mem_shift, sub_self]; exact m0p
    have e04 : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus = texV1Even (parentsAt (u ++ [xd])).even := by rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
    have m4' : AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) := by rw [mem_shift, e04]; exact mU
    have v0 := hv0 _ m0
    have v4' := (hv4 _ m4').2
    rw [sub_self, hP0] at v0
    rw [e04, hQU] at v4'
    -- (3) `P^{+,1}` and `H` at `h + 1`
    obtain ⟨mH, eH⟩ := botH _ mq1 (by rw [add_comm]; exact mV1)
    have m6 : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)) ∈ shift Qh.dom (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) := by rw [mem_shift, add_sub_cancel_left]; exact mH
    have e60 : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)) - AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus = texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ)) := by
      rw [ho]; ext <;> simp [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, hOdd, Bool.false_eq_true]; ring
    have m0' : hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + ((1 : ℤ), (0 : ℤ)) ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by rw [mem_shift, e60]; exact mB1
    have v6 := hv6 _ m6
    have v0' := hv0 _ m0'
    rw [add_sub_cancel_left, eH] at v6
    rw [e60] at v0'
    have eP := botP _ hy1 hy2
    have hPC := (HP _ (by rw [hdP]; exact hy1)).2
    rw [sub_sub_cancel, eP] at hPC
    have hph' : phase (u ++ [xd]) ≠ 1 := by omega
    simp only [hph', if_false]
    simp only [AltRotStep.offP0, SurgicalAlt.coeffOff, SurgicalAlt.altP0Coeff, texV1Odd, texV1Even, texV2, altAff, SurgicalAlt.coeffAffine, aP2, aQ2, offsetA, centreOdd, Cp, Cq, JointFamily.altE, dotS, hOdd, AltGlueOdd.cH, W1Odd, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, if_false, Bool.false_eq_true, ho] at hT hQC v0 v4' v0' v6 hPC h0B ⊢
    linarith [hT, hQC, v0, v4', v0', v6, hPC, h0B]

/-- The half-turn partner: `4 g = K₀` at `D - v - x` gives it at `x`. -/
theorem four_partner (o : PartialOdometer) (D L v a : Site) (M : ℤ) (h : HalfTurnId o D L M) (x : Site)
    (hx : x ∈ o.dom) (hxv : x + v ∈ o.dom) (h4 : 4 * defect o v a (D - v - x) = -dotS L v - 2 * dotS a (D - v)) :
    4 * defect o v a x = -dotS L v - 2 * dotS a (D - v) := by
  have e := (AltLatticeCore.defect_halfTurn o D L v a M h x hx hxv).2.2
  linarith

/-- The constant differences used on the four contact regions. -/
def KDiffs (w : Word) (βP βQ βH : ℤ) (κ : ℕ → ℤ) : Prop :=
  (phase w ≠ 1 → κ 2 - κ 4 = -JointFamily.h0 (texV2 (parentsAt w).even) +
      ((parentsAt w).even.den ^ 2 + 2 * (parentsAt w).even.den * (parentsAt w).even.num - (parentsAt w).even.num ^ 2) -
      βP + βQ) ∧
    (phase w = 1 → κ 5 - κ 1 = JointFamily.h0 (texV2 (parentsAt w).odd) +
      ((parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num -
        (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).odd.den +
        (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2 - (parentsAt w).odd.num) - βQ + βP) ∧
    κ 5 - κ 6 = JointFamily.h0 (texV2 (parentsAt w).odd) +
      (if phase w = 1 then
        (parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num -
          (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).odd.den +
          (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2 - (parentsAt w).odd.num
      else
        (parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num +
          2 * (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).odd.den -
          2 * (parentsAt w).even.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2 - (parentsAt w).odd.num) - βQ + βH

/-- The explicit constants of the decomposition (`AltSixOdd.kOddEF`, `kOddOF` on the six standard copies, `K₁ - β_H` on the
parent piece) have the differences `KDiffs`. -/
def kappaOdd (w : Word) (βP βQ βH : ℤ) (i : ℕ) : ℤ :=
  if i = 6 then
    -JointFamily.h0 (texV2 (parentsAt w).odd) +
      (if phase w = 1 then (parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num - (parentsAt w).odd.num ^ 2
       else (parentsAt w).odd.den ^ 2 + 2 * (parentsAt w).odd.den * (parentsAt w).odd.num +
         (parentsAt w).odd.den * (parentsAt w).even.num - (parentsAt w).even.den * (parentsAt w).odd.num -
         (parentsAt w).odd.num ^ 2) - βH
  else
    (if phase w = 1 then AltSixOdd.kOddOF else AltSixOdd.kOddEF) (parentsAt w).odd.num (parentsAt w).odd.den
      (parentsAt w).even.num (parentsAt w).even.den (JointFamily.h0 (texV2 (parentsAt w).odd))
      (JointFamily.h0 (texV2 (parentsAt w).even)) βP βQ i

theorem kappaOdd_diffs (w : Word) (βP βQ βH : ℤ) : KDiffs w βP βQ βH (kappaOdd w βP βQ βH) := by
  refine ⟨fun hph => ?_, fun hph => ?_, ?_⟩
  · simp only [kappaOdd, hph, if_false, AltSixOdd.kOddEF]; norm_num
  · simp only [kappaOdd, hph, if_true, AltSixOdd.kOddOF]; norm_num; ring
  · by_cases hph : phase w = 1 <;> simp only [kappaOdd, hph, if_true, if_false, AltSixOdd.kOddEF, AltSixOdd.kOddOF] <;>
      norm_num <;> ring

set_option maxHeartbeats 400000 in
/-- **Item (b), the odd alternate child along its second period** (types one and three): a glue `o` of the seven pieces
with constants `κ` having the differences `KDiffs`, over normalised parents (the half-turns `HP`, `HQ`, `HH` and the values
`β` on the bottom walks, in overlap form), is lattice self-compatible along `W = v_{p₀,2}` with the factor `a_{p₀,2}`. -/
theorem odd_W (u : Word) (xd : Digit) (hx : xd ≠ Digit.two) (hw : ¬ IsBase (u ++ [xd]))
    (P Q Qh : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (hdH : Qh.dom = altEvenTile AltRotStep.B u) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ Qh.dom)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (HH : ∀ z ∈ Qh.dom, JointFamily.altD u false - z ∈ Qh.dom ∧
      2 * (Qh.val (JointFamily.altD u false - z) - Qh.val z) =
        dotS (JointFamily.altE u) (JointFamily.altD u false) - 2 * dotS (JointFamily.altE u) z)
    (βP βQ βH : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ)
    (botH : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Qh.val y = βH)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces7 (u ++ [xd]) P Q Qh)) (hdom : o.dom = altOddTile AltRotStep.B (u ++ [xd]))
    (κ : ℕ → ℤ) (hval : ∀ (i : ℕ) (pc : Piece), (pieces7 (u ++ [xd]) P Q Qh)[i]? = some pc → ∀ y ∈ pc.placed,
      o.val y = pieceVal pc y + κ i)
    (hK : KDiffs (u ++ [xd]) βP βQ βH κ) :
    JointFamily.LatticeSelfCompatible o (latV (u ++ [xd]) false 0 1) (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true) := by
  have HT := AltGlueOdd.glue_halfTurn_odd u xd hx hw P Q Qh hdP hdQ h0 HP HQ HH o hR
  have HT' : HalfTurnId o (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (dotS (JointFamily.altE (u ++ [xd])) (AltGlueOdd.Dw (u ++ [xd]))) := HT
  -- the values on the seven pieces
  have pv : ∀ (i : ℕ) (T : PartialOdometer) (of af : Site), (pieces7 (u ++ [xd]) P Q Qh)[i]? = some (stdPiece T of af) →
      ∀ y ∈ shift T.dom of, y ∈ o.dom ∧ o.val y = T.val (y - of) + dotS af y + κ i := by
    intro i T of af hi y hy
    have hy' : y ∈ (stdPiece T of af).placed := (placed_std T of af y).2 hy
    refine ⟨?_, by rw [hval i _ hi y hy']; rfl⟩
    rw [hR.1, JointGlue.mem_pieceUnion]
    exact ⟨_, List.mem_of_getElem? hi, hy'⟩
  have hv0 := pv 0 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus)) rfl
  have hv1 := pv 1 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus + AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus) + aP2 (u ++ [xd])) rfl
  have hv2 := pv 2 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Minus)) rfl
  have hv3 := pv 3 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus + AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Minus) + aP2 (u ++ [xd])) rfl
  have hv4 := pv 4 Q (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Plus)) rfl
  have hv5 := pv 5 Q (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) rfl
  have hv6 := pv 6 Qh (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (altAff (u ++ [xd]) (AltGlueOdd.cH (u ++ [xd]))) rfl
  rw [hdP] at hv0 hv1 hv2 hv3
  rw [hdQ] at hv4 hv5
  rw [hdH] at hv6
  rw [add_comm] at hv1 hv3
  obtain ⟨hKa, hKb, hKc⟩ := hK
  refine AltLatticeCore.latticeSelfCompatible_of_four o _ _
    (-dotS (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (latV (u ++ [xd]) false 0 1) - 2 * dotS (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true) (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1)) (fun y hy hyW => ?_)
  have hy' := hy
  have hyW' := hyW
  rw [hdom] at hy' hyW'
  -- the half-turn images of the pieces
  have rP : ∀ a z, z ∈ shift (stateAt (u ++ [xd])).tOdd a → centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - z ∈ shift (stateAt (u ++ [xd])).tOdd (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - a) :=
    fun a z hz => AltItem4.pcopy_refl hw _ a z hz
  have rQ : ∀ b z, z ∈ shift (stateAt (u ++ [xd])).tEven b → centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - z ∈ shift (stateAt (u ++ [xd])).tEven (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - b) :=
    fun b z hz => AltItem4.qcopy_refl hw _ b z hz
  have e45 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) = AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus := AltItem4.refl_Qp hw
  have e54 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) = AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus := by rw [← AltItem4.refl_Qp hw]; abel
  have e12 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) = AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus := AltItem4.refl_P2 hw
  have e21 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) = AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus := AltItem4.refl_M1 hw
  have es : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y + latV (u ++ [xd]) false 0 1 = centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - y := by abel
  have es' : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - (y + latV (u ++ [xd]) false 0 1) = centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y := by abel
  rcases AltLatticeOddW.classify_W u xd hx hw y hy' hyW' with hr | ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩ | ⟨hc1, hc2⟩ | ⟨hd1, hd2⟩
  · -- the complete overlap
    exact R_case hw P o _ _ HT' (κ 0) (κ 3) hv0 (fun z hz => by
      obtain ⟨h1, h2⟩ := hv3 z hz; exact ⟨h1, by rw [h2]⟩) y hr
  · -- `(Q^+, P^{-,1} + W)`
    rcases AltBounds.phase_cases (u ++ [xd]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
    · refine four_partner o _ _ _ _ _ HT' y hy hyW ?_
      have m1 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even + AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) := by
        have := rP _ _ ha2; rw [e21, es'] at this; exact this
      have m2 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y + latV (u ++ [xd]) false 0 1 ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) := by
        have := rQ _ _ ha1; rw [e45, ← es] at this; exact this
      exact regionB_odd hw hph P Q o βP βQ (κ 1) (κ 5) HQ hdQ botP botQ (fun z hz => (hv1 z hz).2)
        (fun z hz => (hv5 z hz).2) (hKb hph) _ m1 m2
    · exact regionA_even hw (by omega) P Q o βP βQ (κ 2) (κ 4) HP hdP botP botQ (fun z hz => (hv2 z hz).2)
        (fun z hz => (hv4 z hz).2) (hKa (by omega)) y ha1 ha2
  · -- `(P^{+,2}, Q^- + W)`
    rcases AltBounds.phase_cases (u ++ [xd]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
    · exact regionB_odd hw hph P Q o βP βQ (κ 1) (κ 5) HQ hdQ botP botQ (fun z hz => (hv1 z hz).2)
        (fun z hz => (hv5 z hz).2) (hKb hph) y hb1 hb2
    · refine four_partner o _ _ _ _ _ HT' y hy hyW ?_
      have m1 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) := by
        have := rQ _ _ hb2; rw [e54, es'] at this; exact this
      have m2 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y + latV (u ++ [xd]) false 0 1 ∈ shift (stateAt (u ++ [xd])).tOdd (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) := by
        have := rP _ _ hb1; rw [e12, ← es] at this; exact this
      exact regionA_even hw (by omega) P Q o βP βQ (κ 2) (κ 4) HP hdP botP botQ (fun z hz => (hv2 z hz).2)
        (fun z hz => (hv4 z hz).2) (hKa (by omega)) _ m1 m2
  · -- `(H, Q^- + W)`
    exact regionC hx hw Q Qh o βQ βH (κ 5) (κ 6) HQ hdQ botQ botH (fun z hz => (hv5 z hz).2)
      (fun z hz => (hv6 z hz).2) hKc y hc1 hc2
  · -- `(Q^+, H + W)`
    refine four_partner o _ _ _ _ _ HT' y hy hyW ?_
    have m1 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y ∈ shift (altEvenTile AltRotStep.B u) (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) := by
      have := AltItem4.parent_odd_sym u xd hx _ hd2; rw [es'] at this; exact this
    have m2 : centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even - latV (u ++ [xd]) false 0 1 - y + latV (u ++ [xd]) false 0 1 ∈ shift (stateAt (u ++ [xd])).tEven (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) := by
      have := rQ _ _ hd1; rw [e45, ← es] at this; exact this
    exact regionC hx hw Q Qh o βQ βH (κ 5) (κ 6) HQ hdQ botQ botH (fun z hz => (hv5 z hz).2)
      (fun z hz => (hv6 z hz).2) hKc _ m1 m2

set_option maxHeartbeats 400000 in
/-- **Item (b), the odd alternate child along its second period, from the parents** (types one and three): an odometer `o`
respecting the seven pieces on `T̂(p₀)`, over normalised parents (the half-turns `HP`, `HQ`, `HH`; the values `β` on the bottom
walks, in overlap form; `P(0) = P(v_{p₁,1}) = β_P` and `Q(0) = Q(v_{q₁,1}) = β_Q`), is lattice self-compatible along
`W = v_{p₀,2}` with the factor `a_{p₀,2}`. The constants of the pieces have the differences `KDiffs` (`kd_a`, `kd_b`, `kd_c`). -/
theorem odd_W_parents (u : Word) (xd : Digit) (hx : xd ≠ Digit.two) (hw : ¬ IsBase (u ++ [xd]))
    (P Q Qh : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (hdH : Qh.dom = altEvenTile AltRotStep.B u) (h0 : ((0 : ℤ), (0 : ℤ)) ∈ Qh.dom)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (HH : ∀ z ∈ Qh.dom, JointFamily.altD u false - z ∈ Qh.dom ∧
      2 * (Qh.val (JointFamily.altD u false - z) - Qh.val z) =
        dotS (JointFamily.altE u) (JointFamily.altD u false) - 2 * dotS (JointFamily.altE u) z)
    (βP βQ βH : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ)
    (botH : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → y ∈ Qh.dom ∧ Qh.val y = βH)
    (hP0 : P.val 0 = βP) (hPA : P.val (texV1Odd (parentsAt (u ++ [xd])).odd) = βP) (hQ0 : Q.val 0 = βQ) (hQU : Q.val (texV1Even (parentsAt (u ++ [xd])).even) = βQ)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces7 (u ++ [xd]) P Q Qh)) (hdom : o.dom = altOddTile AltRotStep.B (u ++ [xd])) :
    JointFamily.LatticeSelfCompatible o (latV (u ++ [xd]) false 0 1) (offsetA ((parentsAt (u ++ [xd])).current .odd).num ((parentsAt (u ++ [xd])).current .odd).den true) := by
  obtain ⟨κ, hval⟩ := respects_kappa o _ hR (fun pc hpc => by
    simp only [pieces7, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have HT := AltGlueOdd.glue_halfTurn_odd u xd hx hw P Q Qh hdP hdQ h0 HP HQ HH o hR
  have HT' : HalfTurnId o (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (dotS (JointFamily.altE (u ++ [xd])) (centreOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even)) := HT
  have pv : ∀ (i : ℕ) (T : PartialOdometer) (of af : Site), (pieces7 (u ++ [xd]) P Q Qh)[i]? = some (stdPiece T of af) →
      ∀ y ∈ shift T.dom of, y ∈ o.dom ∧ o.val y = T.val (y - of) + dotS af y + κ i := by
    intro i T of af hi y hy
    have hy' : y ∈ (stdPiece T of af).placed := (placed_std T of af y).2 hy
    refine ⟨?_, by rw [hval i _ hi y hy']; rfl⟩
    rw [hR.1, JointGlue.mem_pieceUnion]
    exact ⟨_, List.mem_of_getElem? hi, hy'⟩
  have hv0 := pv 0 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus)) rfl
  have hv1 := pv 1 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Plus + AltRotStep.shP (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Plus) + aP2 (u ++ [xd])) rfl
  have hv2 := pv 2 P (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .dsP1Minus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .dsP1Minus)) rfl
  have hv4 := pv 4 Q (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Plus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Plus)) rfl
  have hv5 := pv 5 Q (AltRotStep.offP0 (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even .q1Minus) (altAff (u ++ [xd]) (SurgicalAlt.altP0Coeff (W1Odd (u ++ [xd])) .q1Minus)) rfl
  have hv6 := pv 6 Qh (hOdd (phase (u ++ [xd]) == 1) (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even) (altAff (u ++ [xd]) (AltGlueOdd.cH (u ++ [xd]))) rfl
  rw [hdP] at hv0 hv1 hv2
  rw [hdQ] at hv4 hv5
  rw [add_comm] at hv1
  have hK : KDiffs (u ++ [xd]) βP βQ βH κ :=
    ⟨fun hph => kd_a hw hph P Q hdQ HQ βP βQ botP botQ o κ (fun y hy => (hv2 y hy).2)
        (fun y hy => (hv4 y hy).2),
      fun hph => kd_b hw hph P Q hdP HP βP βQ botP botQ o κ (fun y hy => (hv1 y hy).2)
        (fun y hy => (hv5 y hy).2),
      kd_c hw P Q Qh hdP hdQ HP HQ βP βQ βH botP botH hP0 hPA hQ0 hQU o HT' κ
        (fun y hy => (hv0 y hy).2) hv4 (fun y hy => (hv5 y hy).2) (fun y hy => (hv6 y hy).2)⟩
  exact odd_W u xd hx hw P Q Qh hdP hdQ hdH h0 HP HQ HH βP βQ βH botP botQ (fun y h1 h2 => (botH y h1 h2).2) o hR hdom
    κ hval hK

end FLatticePaper.Tiles.AltLatticeOddWMain
