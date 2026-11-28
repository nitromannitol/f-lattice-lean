import FLatticePaper.Tiles.AltLatticeEvenV

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the even alternate child along its second period, values

The defect `g(x) = o(x + v) - o(x) - aᵀx` of an odometer respecting the seven pieces of `T̂(q₀)`, `v = v_{q₀,2}`, `a = a_{q₀,2}`:
on the regions `(T(q₁)^{+,1}, T(q₁)^{-,2})` and `(T(p₁)^+, T(p₁)^-)`, both mapped to themselves by `x ↦ D̂ - v - x`, `2g` is
constant (the point of `x` on the bottom walk of its parent, the point of `x + v` on the top walk), so `4g = K₀`. -/

namespace FLatticePaper.Tiles.AltLatticeEvenVMain

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1)
open FLatticePaper.Tiles.AltGlueEven (De cHe pieces7e)
open FLatticePaper.Tiles.AltLatticeCore (defect HalfTurnId)
open FLatticePaper.Tiles.SiteInduction (InH curE)

/-- On a region mapped to itself by `x ↦ D - v - x` on which `2g` is a constant, `4g = K₀`. -/
theorem four_of_two (o : PartialOdometer) (D L v a : Site) (M : ℤ) (h : HalfTurnId o D L M) (R : Set Site)
    (hR : ∀ x ∈ R, x ∈ o.dom ∧ x + v ∈ o.dom) (hinv : ∀ x ∈ R, D - v - x ∈ R) (F : ℤ)
    (hF : ∀ x ∈ R, 2 * defect o v a x = F) (x : Site) (hx : x ∈ R) :
    4 * defect o v a x = -dotS L v - 2 * dotS a (D - v) := by
  obtain ⟨hx1, hx2⟩ := hR x hx
  have e := (AltLatticeCore.defect_halfTurn o D L v a M h x hx1 hx2).2.2
  have e1 := hF _ (hinv x hx)
  have e2 := hF x hx
  linarith

set_option maxHeartbeats 400000 in
/-- **The region `(T(q₁)^{+,1}, T(q₁)^{-,2})`**: `2g` is constant. -/
theorem regionQQ {w : Word} (hw : ¬ IsBase w) (Q o : PartialOdometer) (βQ k0 k3 : ℤ)
    (HQ : ∀ z ∈ Q.dom, AltGlueOdd.Cq w - z ∈ Q.dom ∧
      2 * (Q.val (AltGlueOdd.Cq w - z) - Q.val z) = dotS (aQ2 w) (AltGlueOdd.Cq w) - 2 * dotS (aQ2 w) z)
    (hdQ : Q.dom = (stateAt w).tEven)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv0 : ∀ y ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)), o.val y = Q.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) y + k0)
    (hv3 : ∀ y ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2), o.val y = Q.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) y + k3)
    (x : Site) (hx : x ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) (hxv : x + texV2 (curE w) ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) :
    2 * defect o (texV2 (curE w)) (offsetA (curE w).num (curE w).den true) x =
      -dotS (aQ2 w) (AltGlueOdd.Cq w) + 2 * dotS (aQ2 w) (texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) + 2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) (texV2 (curE w)) + 2 * (k3 - k0) := by
  obtain ⟨-, ⟨k2', k3'⟩, -, hmq⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨z, rfl⟩ : ∃ z, x = z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) := ⟨x - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)), by abel⟩
  have hz1 : InH (parentsAt w).even z := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tEven_iff hw z).1 hx
  obtain ⟨z2, hz2d⟩ : ∃ z2, z2 = z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) + texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) := ⟨_, rfl⟩
  have hz2 : InH (parentsAt w).even z2 := by
    rw [mem_shift, ← hz2d] at hxv; exact (AltGlueOdd.mem_tEven_iff hw _).1 hxv
  have hdiff : z2 - z = texV2 (parentsAt w).even + (if phase w = 1 then texV1Odd (parentsAt w).odd - texV1Even (parentsAt w).even
      else texV1Even (parentsAt w).even - texV1Odd (parentsAt w).odd) := by
    rw [hz2d]
    rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> simp only [hph] <;> norm_num <;>
      ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true, W1Odd, ho] <;> ring
  have ht : SiteInduction.tCo (parentsAt w).even z2 = SiteInduction.tCo (parentsAt w).even z -
      SiteInduction.tOf (parentsAt w).even - 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> rw [hph] at hdet <;> simp only [hph] at hdet ⊢ <;>
      norm_num at hdet ⊢ <;>
      simp only [SiteInduction.tCo, SiteInduction.tOf, texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
        Prod.fst_sub, Prod.snd_sub] <;> linarith
  have hpar : (z2.1 + z2.2) % 2 = (z.1 + z.2) % 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> simp only [hph] <;> norm_num <;>
      simp only [texV1Odd, texV1Even, texV2] <;> omega
  have cc := AltLatticeOddW.contact_c_facts (parentsAt w).even.num (parentsAt w).even.den ⟨k2', k3'⟩ hqe hmq z z2 hz1 hz2 ht hpar
  have eQ1 : Q.val z = βQ := botQ z ((AltGlueOdd.mem_tEven_iff hw z).2 hz1) ((AltGlueOdd.mem_tEven_iff hw _).2 cc.1)
  obtain ⟨yq, hyq⟩ : ∃ yq, yq = AltGlueOdd.Cq w - z2 := ⟨_, rfl⟩
  have hy1 : yq ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hyq, AltLatticeOddWMain.Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hz2
  have hy2 : yq + texV2 (parentsAt w).even ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hyq, AltLatticeOddWMain.Cq_eq hw]; exact cc.2
  have eQ2 := botQ yq hy1 hy2
  have hHT := (HQ yq (by rw [hdQ]; exact hy1)).2
  rw [show AltGlueOdd.Cq w - yq = z2 by rw [hyq]; abel, eQ2, hyq] at hHT
  unfold defect
  rw [hv3 _ hxv, hv0 _ hx, add_sub_cancel_right, eQ1, ← hz2d]
  subst hz2d
  rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;>
    simp only [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, aP2, aQ2, offsetA, curE, Parents.current, Parents.combine, AltGlueOdd.Cq, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true, W1Odd, ho] at hHT ⊢ <;> linarith [hHT]

set_option maxHeartbeats 400000 in
/-- **The region `(T(p₁)^+, T(p₁)^-)`**: `2g` is constant. -/
theorem regionPP {w : Word} (hw : ¬ IsBase w) (P o : PartialOdometer) (βP k4 k5 : ℤ)
    (HP : ∀ z ∈ P.dom, AltGlueOdd.Cp w - z ∈ P.dom ∧
      2 * (P.val (AltGlueOdd.Cp w - z) - P.val z) = dotS (aP2 w) (AltGlueOdd.Cp w) - 2 * dotS (aP2 w) z)
    (hdP : P.dom = (stateAt w).tOdd)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (hv4 : ∀ y ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)), o.val y = P.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) y + k4)
    (hv5 : ∀ y ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)), o.val y = P.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) y + k5)
    (x : Site) (hx : x ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) (hxv : x + texV2 (curE w) ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) :
    2 * defect o (texV2 (curE w)) (offsetA (curE w).num (curE w).den true) x =
      -dotS (aP2 w) (AltGlueOdd.Cp w) + 2 * dotS (aP2 w) (texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) + 2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) (texV2 (curE w)) + 2 * (k5 - k4) := by
  obtain ⟨⟨k1', k1''⟩, -, hmp, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, -, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨z, rfl⟩ : ∃ z, x = z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) := ⟨x - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)), by abel⟩
  have hz1 : InH (parentsAt w).odd z := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tOdd_iff hw z).1 hx
  obtain ⟨z2, hz2d⟩ : ∃ z2, z2 = z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) + texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) := ⟨_, rfl⟩
  have hz2 : InH (parentsAt w).odd z2 := by
    rw [mem_shift, ← hz2d] at hxv; exact (AltGlueOdd.mem_tOdd_iff hw _).1 hxv
  have hdiff : z2 - z = texV2 (parentsAt w).odd + (if phase w = 1 then -(texV1Even (parentsAt w).even + texV1Even (parentsAt w).even)
      else texV1Even (parentsAt w).even + texV1Even (parentsAt w).even) := by
    rw [hz2d]
    rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;> simp only [hph] <;> norm_num <;>
      ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true, W1Odd, ho] <;> ring
  have ht : SiteInduction.tCo (parentsAt w).odd z2 = SiteInduction.tCo (parentsAt w).odd z -
      SiteInduction.tOf (parentsAt w).odd - 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> rw [hph] at hdet <;> simp only [hph] at hdet ⊢ <;>
      norm_num at hdet ⊢ <;>
      simp only [SiteInduction.tCo, SiteInduction.tOf, texV1Even, texV2, Prod.fst_add, Prod.snd_add,
        Prod.fst_neg, Prod.snd_neg] <;> linarith
  have hpar : (z2.1 + z2.2) % 2 = (z.1 + z.2) % 2 := by
    have e : z2 = z + (z2 - z) := by abel
    rw [e, hdiff]
    rcases AltBounds.phase_cases w with ⟨-, hph⟩ | ⟨-, hph⟩ <;> simp only [hph] <;> norm_num <;>
      simp only [texV1Even, texV2,
        ] <;> omega
  have cc := AltLatticeEvenV.contact_c_facts_p (parentsAt w).odd.num (parentsAt w).odd.den ⟨k1', k1''⟩ hmp z z2 hz1 hz2 ht hpar
  have eP1 : P.val z = βP := botP z ((AltGlueOdd.mem_tOdd_iff hw z).2 hz1) ((AltGlueOdd.mem_tOdd_iff hw _).2 cc.1)
  obtain ⟨yp, hyp⟩ : ∃ yp, yp = AltGlueOdd.Cp w - z2 := ⟨_, rfl⟩
  have hy1 : yp ∈ (stateAt w).tOdd := by
    rw [AltGlueOdd.mem_tOdd_iff hw, hyp, AltLatticeOddWMain.Cp_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hz2
  have hy2 : yp + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := by
    rw [AltGlueOdd.mem_tOdd_iff hw, hyp, AltLatticeOddWMain.Cp_eq hw]; exact cc.2
  have eP2 := botP yp hy1 hy2
  have hHT := (HP yp (by rw [hdP]; exact hy1)).2
  rw [show AltGlueOdd.Cp w - yp = z2 by rw [hyp]; abel, eP2, hyp] at hHT
  unfold defect
  rw [hv5 _ hxv, hv4 _ hx, add_sub_cancel_right, eP1, ← hz2d]
  subst hz2d
  rcases AltBounds.phase_cases w with ⟨ho, hph⟩ | ⟨ho, hph⟩ <;>
    simp only [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, aP2, offsetA, curE, Parents.current, Parents.combine, AltGlueOdd.Cp, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, if_false, Bool.false_eq_true, W1Odd, ho] at hHT ⊢ <;> linarith [hHT]

set_option maxHeartbeats 400000 in
/-- **The mixed region `(T(q₁)^{+,1}, T(p₁)^-)`, `W₁` even**: `4g = K₀`, given the constant relations of the glue. -/
theorem regionM_even {w : Word} (hw : ¬ IsBase w) (hph : phase w ≠ 1) (P Q o : PartialOdometer) (βP βQ k0 k4 k5 : ℤ)
    (HP : ∀ z ∈ P.dom, AltGlueOdd.Cp w - z ∈ P.dom ∧
      2 * (P.val (AltGlueOdd.Cp w - z) - P.val z) = dotS (aP2 w) (AltGlueOdd.Cp w) - 2 * dotS (aP2 w) z)
    (hdP : P.dom = (stateAt w).tOdd)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv0 : ∀ y ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)), o.val y = Q.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) y + k0)
    (hv5 : ∀ y ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)), o.val y = P.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) y + k5)
    (hk54 : 2 * (k5 - k4) = -2 * dotS (JointFamily.altE w) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) + dotS (JointFamily.altE w) (De w) - dotS (aP2 w) (AltGlueOdd.Cp w) -
      2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) (De w - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) + 2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)))
    (hk40 : k4 - k0 = βQ - βP + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) - (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) (texV1Even (parentsAt w).even))
    (x : Site) (hx : x ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) (hxv : x + texV2 (curE w) ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) :
    4 * defect o (texV2 (curE w)) (offsetA (curE w).num (curE w).den true) x = -dotS (-(2 : ℤ) • JointFamily.altE w) (texV2 (curE w)) - 2 * dotS (offsetA (curE w).num (curE w).den true) (De w - texV2 (curE w)) := by
  obtain ⟨⟨k1, k1'⟩, ⟨k2', k3⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, hqe, hdet⟩ := AltPieces.parents_facts hw
  rw [if_neg hph] at hdet
  have ho : W1Odd w = false := by simpa [W1Odd] using hph
  have ho' : (phase w == 1) = false := by simpa using hph
  obtain ⟨z, rfl⟩ : ∃ z, x = z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) := ⟨x - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)), by abel⟩
  have hzq : InH (parentsAt w).even z := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tEven_iff hw z).1 hx
  have hz2 : z + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) + texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) = z + texV1Even (parentsAt w).even + texV2 (parentsAt w).odd := by
    rw [ho]; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Bool.false_eq_true] <;> ring
  have hzp : InH (parentsAt w).odd (z + texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) := by
    rw [mem_shift, hz2] at hxv; exact (AltGlueOdd.mem_tOdd_iff hw _).1 hxv
  have cf := AltLatticeEvenV.contact_U_even (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den ⟨k1, k1'⟩ ⟨k2', k3⟩ hqe hdet z.1 z.2 hzq hzp
  have eQ : Q.val z = βQ := botQ z ((AltGlueOdd.mem_tEven_iff hw z).2 hzq) ((AltGlueOdd.mem_tEven_iff hw _).2 cf.1)
  obtain ⟨y, hyd⟩ : ∃ y, y = AltGlueOdd.Cp w - (z + texV1Even (parentsAt w).even + texV2 (parentsAt w).odd) := ⟨_, rfl⟩
  have hy1 : y ∈ (stateAt w).tOdd := by
    rw [AltGlueOdd.mem_tOdd_iff hw, hyd, AltLatticeOddWMain.Cp_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hzp
  have hy2 : y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd := by
    have e : y + texV2 (parentsAt w).odd = AltGlueOdd.Cp w - (z + texV1Even (parentsAt w).even) := by rw [hyd]; abel
    rw [e, AltGlueOdd.mem_tOdd_iff hw, AltLatticeOddWMain.Cp_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ cf.2
  have eP := botP y hy1 hy2
  have hHT := (HP y (by rw [hdP]; exact hy1)).2
  rw [show AltGlueOdd.Cp w - y = z + texV1Even (parentsAt w).even + texV2 (parentsAt w).odd by rw [hyd]; abel, eP, hyd] at hHT
  unfold defect
  rw [hv5 _ hxv, hv0 _ hx, hz2, add_sub_cancel_right, eQ]
  simp only [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, aP2, aQ2, offsetA, curE, Parents.current, Parents.combine, AltGlueOdd.Cp, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_false, Bool.false_eq_true, W1Odd, De, AltPieces.centreEven, JointFamily.altE, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ho'] at hHT hk54 hk40 ⊢
  linarith [hHT, hk54, hk40]

set_option maxHeartbeats 400000 in
/-- **The mixed region `(T(p₁)^+, T(q₁)^{-,2})`, `W₁` odd**: `4g = K₀`, given the constant relations of the glue. -/
theorem regionM_odd {w : Word} (hw : ¬ IsBase w) (hph : phase w = 1) (P Q o : PartialOdometer) (βP βQ k0 k3 k4 : ℤ)
    (HQ : ∀ z ∈ Q.dom, AltGlueOdd.Cq w - z ∈ Q.dom ∧
      2 * (Q.val (AltGlueOdd.Cq w - z) - Q.val z) = dotS (aQ2 w) (AltGlueOdd.Cq w) - 2 * dotS (aQ2 w) z)
    (hdQ : Q.dom = (stateAt w).tEven)
    (botP : ∀ y, y ∈ (stateAt w).tOdd → y + texV2 (parentsAt w).odd ∈ (stateAt w).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt w).tEven → y + texV2 (parentsAt w).even ∈ (stateAt w).tEven → Q.val y = βQ)
    (hv4 : ∀ y ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)), o.val y = P.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) y + k4)
    (hv3 : ∀ y ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2), o.val y = Q.val (y - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) y + k3)
    (hk30 : 2 * (k3 - k0) = -2 * dotS (JointFamily.altE w) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) + dotS (JointFamily.altE w) (De w) - dotS (aQ2 w) (AltGlueOdd.Cq w) -
      2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) (De w - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) + 2 * dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)))
    (hk40 : k4 - k0 = βQ - βP + dotS (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) - (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) (texV1Odd (parentsAt w).odd))
    (x : Site) (hx : x ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) (hxv : x + texV2 (curE w) ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) :
    4 * defect o (texV2 (curE w)) (offsetA (curE w).num (curE w).den true) x = -dotS (-(2 : ℤ) • JointFamily.altE w) (texV2 (curE w)) - 2 * dotS (offsetA (curE w).num (curE w).den true) (De w - texV2 (curE w)) := by
  obtain ⟨⟨k1, k1'⟩, ⟨k2', k3'⟩, -, -⟩ := AltItem5.parent_hyps hw
  obtain ⟨-, -, -, -, -, hqe, hdet⟩ := AltPieces.parents_facts hw
  rw [if_pos hph] at hdet
  have ho : W1Odd w = true := by simpa [W1Odd] using hph
  have ho' : (phase w == 1) = true := by simpa using hph
  obtain ⟨y, rfl⟩ : ∃ y, x = y + texV1Even (parentsAt w).even + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) := ⟨x - texV1Even (parentsAt w).even - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)), by abel⟩
  have hzp : InH (parentsAt w).odd (y + texV1Even (parentsAt w).even) := by
    rw [mem_shift, add_sub_cancel_right] at hx; exact (AltGlueOdd.mem_tOdd_iff hw _).1 hx
  have hz2 : y + texV1Even (parentsAt w).even + (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) + texV2 (curE w) - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) = y + texV2 (parentsAt w).even := by
    rw [ho]; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, curE, Parents.current, Parents.combine, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  have hzq : InH (parentsAt w).even (y + texV2 (parentsAt w).even) := by
    rw [mem_shift, hz2] at hxv; exact (AltGlueOdd.mem_tEven_iff hw _).1 hxv
  have cf := AltLatticeEvenV.contact_U_odd (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den ⟨k1, k1'⟩ ⟨k2', k3'⟩ hqe hdet y.1 y.2 hzp hzq
  have eP : P.val (y + texV1Even (parentsAt w).even) = βP :=
    botP _ ((AltGlueOdd.mem_tOdd_iff hw _).2 hzp) ((AltGlueOdd.mem_tOdd_iff hw _).2 cf.1)
  obtain ⟨yq, hyq⟩ : ∃ yq, yq = AltGlueOdd.Cq w - (y + texV2 (parentsAt w).even) := ⟨_, rfl⟩
  have hy1 : yq ∈ (stateAt w).tEven := by
    rw [AltGlueOdd.mem_tEven_iff hw, hyq, AltLatticeOddWMain.Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ hzq
  have hy2 : yq + texV2 (parentsAt w).even ∈ (stateAt w).tEven := by
    have e : yq + texV2 (parentsAt w).even = AltGlueOdd.Cq w - y := by rw [hyq]; abel
    rw [e, AltGlueOdd.mem_tEven_iff hw, AltLatticeOddWMain.Cq_eq hw, ← AltItem4.refl_eq]; exact EncUpper.inH_refl _ _ cf.2
  have eQ := botQ yq hy1 hy2
  have hHT := (HQ yq (by rw [hdQ]; exact hy1)).2
  rw [show AltGlueOdd.Cq w - yq = y + texV2 (parentsAt w).even by rw [hyq]; abel, eQ, hyq] at hHT
  unfold defect
  rw [hv3 _ hxv, hv4 _ hx, hz2, add_sub_cancel_right, eP]
  simp only [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, aP2, aQ2, offsetA, curE, Parents.current, Parents.combine, AltGlueOdd.Cq, dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, W1Odd, De, AltPieces.centreEven, JointFamily.altE, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ho'] at hHT hk30 hk40 ⊢
  linarith [hHT, hk30, hk40]

set_option maxHeartbeats 400000 in
/-- **Item (b), the even alternate child along its second period, from the parents** (types one and two): an odometer `o`
respecting the seven pieces on `T̂(q₀)`, over normalised parents (the half-turns `HP`, `HQ`, `HH`; the values `β` on the bottom
walks of the standard parents, in overlap form; `P(0) = P(v_{p₁,1}) = β_P`, `Q(0) = Q(v_{q₁,1}) = β_Q`; the first tile of the
alternate parent in its domain), is lattice self-compatible along `v_{q₀,2}` with the factor `a_{q₀,2}`. -/
theorem even_V_parents (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd]))
    (P Q Ph : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ Ph.dom) (h1 : ((1 : ℤ), (0 : ℤ)) ∈ Ph.dom)
    (HP : ∀ z ∈ P.dom, AltGlueOdd.Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (AltGlueOdd.Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (AltGlueOdd.Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (HQ : ∀ z ∈ Q.dom, AltGlueOdd.Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (AltGlueOdd.Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (AltGlueOdd.Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (HH : ∀ z ∈ Ph.dom, JointFamily.altD u true - z ∈ Ph.dom ∧
      2 * (Ph.val (JointFamily.altD u true - z) - Ph.val z) =
        dotS (JointFamily.altE u) (JointFamily.altD u true) - 2 * dotS (JointFamily.altE u) z)
    (βP βQ : ℤ)
    (botP : ∀ y, y ∈ (stateAt (u ++ [xd])).tOdd → y + texV2 (parentsAt (u ++ [xd])).odd ∈ (stateAt (u ++ [xd])).tOdd → P.val y = βP)
    (botQ : ∀ y, y ∈ (stateAt (u ++ [xd])).tEven → y + texV2 (parentsAt (u ++ [xd])).even ∈ (stateAt (u ++ [xd])).tEven → Q.val y = βQ)
    (hP0 : P.val 0 = βP) (hPA : P.val (texV1Odd (parentsAt (u ++ [xd])).odd) = βP) (hQ0 : Q.val 0 = βQ)
    (hQU : Q.val (texV1Even (parentsAt (u ++ [xd])).even) = βQ)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces7e (u ++ [xd]) xd P Q Ph))
    (hdom : o.dom = altEvenTile AltRotStep.B (u ++ [xd])) :
    JointFamily.LatticeSelfCompatible o (texV2 (curE (u ++ [xd]))) (offsetA (curE (u ++ [xd])).num (curE (u ++ [xd])).den true) := by
  obtain ⟨κ, hval⟩ := AltLatticeOddWMain.respects_kappa o _ hR (fun pc hpc => by
    simp only [pieces7e, List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have HT := AltGlueEven.glue_halfTurn_even u xd hx hw P Q Ph hdP hdQ h0 h1 HP HQ HH o hR
  have pv : ∀ (i : ℕ) (T : PartialOdometer) (of af : Site), (pieces7e (u ++ [xd]) xd P Q Ph)[i]? = some (stdPiece T of af) →
      ∀ y ∈ shift T.dom of, y ∈ o.dom ∧ o.val y = T.val (y - of) + dotS af y + κ i := by
    intro i T of af hi y hy
    have hy' : y ∈ (stdPiece T of af).placed := (AltLatticeOddWMain.placed_std T of af y).2 hy
    refine ⟨?_, by rw [hval i _ hi y hy']; rfl⟩
    rw [hR.1, JointGlue.mem_pieceUnion]
    exact ⟨_, List.mem_of_getElem? hi, hy'⟩
  have hv0 := pv 0 Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) rfl
  have hv3 := pv 3 Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd])) rfl
  have hv4 := pv 4 P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) rfl
  have hv5 := pv 5 P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) rfl
  rw [hdQ] at hv0 hv3
  rw [hdP] at hv4 hv5
  have mp0 := AltGlueOdd.cert_p_zero hw
  have mq0 := AltGlueEven.cert_q_zero hw
  have mA := AltGlueOdd.cert_p_A hw
  have mU := AltGlueOdd.cert_q_U hw
  -- the constant relations of the glue
  have k54 : 2 * (κ 5 - κ 4) = -2 * dotS (JointFamily.altE (u ++ [xd])) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) + dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) - dotS (aP2 (u ++ [xd])) (AltGlueOdd.Cp (u ++ [xd])) -
      2 * dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) + 2 * dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by
    have y4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by rw [mem_shift, sub_self]; exact mp0
    have eD : De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) = AltGlueOdd.Cp (u ++ [xd]) := by rw [AltGlueEven.off_45e]; abel
    have y5 : De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) := by
      rw [mem_shift, eD, ← hdP, ← sub_zero (AltGlueOdd.Cp (u ++ [xd]))]; exact (HP _ (by rw [hdP]; exact mp0)).1
    have t := (HT _ (hv4 _ y4).1).2
    rw [(hv4 _ y4).2, (hv5 _ y5).2, sub_self, eD, hP0] at t
    have e := (HP _ (by rw [hdP]; exact mp0)).2
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : Site) from rfl, sub_zero, hP0] at e
    simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at t e ⊢
    linarith
  have k30 : 2 * (κ 3 - κ 0) = -2 * dotS (JointFamily.altE (u ++ [xd])) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) + dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) - dotS (aQ2 (u ++ [xd])) (AltGlueOdd.Cq (u ++ [xd])) -
      2 * dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd])) (De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))) + 2 * dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by
    have y0 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by rw [mem_shift, sub_self]; exact mq0
    have eD : De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) = AltGlueOdd.Cq (u ++ [xd]) := by rw [AltGlueEven.off_03e]; abel
    have y3 : De (u ++ [xd]) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) := by
      rw [mem_shift, eD, ← hdQ, ← sub_zero (AltGlueOdd.Cq (u ++ [xd]))]; exact (HQ _ (by rw [hdQ]; exact mq0)).1
    have t := (HT _ (hv0 _ y0).1).2
    rw [(hv0 _ y0).2, (hv3 _ y3).2, sub_self, eD, hQ0] at t
    have e := (HQ _ (by rw [hdQ]; exact mq0)).2
    rw [show ((0 : ℤ), (0 : ℤ)) = (0 : Site) from rfl, sub_zero, hQ0] at e
    simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero] at t e ⊢
    linarith
  -- the half-turn images of the pieces
  have rP : ∀ a z, z ∈ shift (stateAt (u ++ [xd])).tOdd a → De (u ++ [xd]) - z ∈ shift (stateAt (u ++ [xd])).tOdd (De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - a) :=
    fun a z hz => AltItem4.pcopy_refl hw _ a z hz
  have rQ : ∀ b z, z ∈ shift (stateAt (u ++ [xd])).tEven b → De (u ++ [xd]) - z ∈ shift (stateAt (u ++ [xd])).tEven (De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - b) :=
    fun b z hz => AltItem4.qcopy_refl hw _ b z hz
  have e03 : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2 := by
    rw [AltGlueEven.off_03e, AltLatticeOddWMain.Cq_eq hw]
  have e30 : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) := by
    rw [AltGlueEven.off_03e, AltLatticeOddWMain.Cq_eq hw]; abel
  have e45 : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus) := by
    rw [AltGlueEven.off_45e, AltLatticeOddWMain.Cp_eq hw]
  have e54 : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) := by
    rw [AltGlueEven.off_45e, AltLatticeOddWMain.Cp_eq hw]; abel
  refine AltLatticeCore.latticeSelfCompatible_of_four o _ _ (-dotS (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (texV2 (curE (u ++ [xd]))) - 2 * dotS (offsetA (curE (u ++ [xd])).num (curE (u ++ [xd])).den true) (De (u ++ [xd]) - texV2 (curE (u ++ [xd])))) (fun y hy hyv => ?_)
  have hy' := hy
  have hyv' := hyv
  rw [hdom] at hy' hyv'
  have es : De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y := by abel
  have es' : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) = De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y := by abel
  obtain ⟨hK, hJ⟩ := AltLatticeEvenV.classify_V u xd hx hw y hy' hyv'
  rcases AltBounds.phase_cases (u ++ [xd]) with ⟨ho, hph⟩ | ⟨ho, hph⟩
  · -- `W₁` odd
    have k40 : κ 4 - κ 0 = βQ - βP + dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (texV1Odd (parentsAt (u ++ [xd])).odd) := by
      have eA : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) = texV1Odd (parentsAt (u ++ [xd])).odd := by
        rw [show W1Odd (u ++ [xd]) = true from ho]; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2]
      have z4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by rw [mem_shift, eA]; exact mA
      have z0 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by rw [mem_shift, sub_self]; exact mq0
      have a1 := (hv4 _ z4).2
      have a2 := (hv0 _ z0).2
      rw [eA, hPA] at a1
      rw [sub_self, hQ0] at a2
      have e3 : dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (texV1Odd (parentsAt (u ++ [xd])).odd) = dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by
        rw [show W1Odd (u ++ [xd]) = true from ho]; simp [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, dotS, Prod.fst_zero, Prod.snd_zero]
      rw [e3]; simp only [dotS, Prod.fst_sub, Prod.snd_sub] at a1 a2 ⊢; linarith
    rcases hK with hK | hK <;> rcases hJ with hJ | hJ
    · -- `(P⁺, P⁻)`
      refine four_of_two o _ _ _ _ _ HT {x | x ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) ∧ x + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))}
        (fun x hx => ⟨(hv4 x hx.1).1, (hv5 _ hx.2).1⟩) (fun x hx => ⟨?_, ?_⟩) _
        (fun x hx => regionPP hw P o βP (κ 4) (κ 5) HP hdP botP (fun z hz => (hv4 z hz).2) (fun z hz => (hv5 z hz).2) x hx.1 hx.2)
        y ⟨hK, hJ⟩
      · have := rP _ _ hx.2; rw [e54] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x = De (u ++ [xd]) - (x + texV2 (curE (u ++ [xd]))) by abel]; exact this
      · have := rP _ _ hx.1; rw [e45] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - x by abel]; exact this
    · -- `(P⁺, Q⁻²)`
      exact regionM_odd hw hph P Q o βP βQ (κ 0) (κ 3) (κ 4) HQ hdQ botP botQ (fun z hz => (hv4 z hz).2)
        (fun z hz => (hv3 z hz).2) k30 k40 y hK hJ
    · -- `(Q⁺¹, P⁻)`, the half-turn image of `(P⁺, Q⁻²)`
      refine AltLatticeOddWMain.four_partner o _ _ _ _ _ HT y hy hyv ?_
      have m1' : De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by have := rP _ _ hJ; rw [e54, es'] at this; exact this
      have m2' : De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) := by have := rQ _ _ hK; rw [e03, ← es] at this; exact this
      exact regionM_odd hw hph P Q o βP βQ (κ 0) (κ 3) (κ 4) HQ hdQ botP botQ (fun z hz => (hv4 z hz).2)
        (fun z hz => (hv3 z hz).2) k30 k40 _ m1' m2'
    · -- `(Q⁺¹, Q⁻²)`
      refine four_of_two o _ _ _ _ _ HT {x | x ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) ∧ x + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2)}
        (fun x hx => ⟨(hv0 x hx.1).1, (hv3 _ hx.2).1⟩) (fun x hx => ⟨?_, ?_⟩) _
        (fun x hx => regionQQ hw Q o βQ (κ 0) (κ 3) HQ hdQ botQ (fun z hz => (hv0 z hz).2) (fun z hz => (hv3 z hz).2) x hx.1 hx.2)
        y ⟨hK, hJ⟩
      · have := rQ _ _ hx.2; rw [e30] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x = De (u ++ [xd]) - (x + texV2 (curE (u ++ [xd]))) by abel]; exact this
      · have := rQ _ _ hx.1; rw [e03] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - x by abel]; exact this
  · -- `W₁` even
    have hph' : phase (u ++ [xd]) ≠ 1 := by omega
    have k40 : κ 4 - κ 0 = βQ - βP + dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (texV1Even (parentsAt (u ++ [xd])).even) := by
      have eU : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) = texV1Even (parentsAt (u ++ [xd])).even := by
        rw [show W1Odd (u ++ [xd]) = false from ho]; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, Bool.false_eq_true]
      have z4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by rw [mem_shift, sub_self]; exact mp0
      have z0 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by rw [mem_shift, eU]; exact mU
      have a1 := (hv4 _ z4).2
      have a2 := (hv0 _ z0).2
      rw [sub_self, hP0] at a1
      rw [eU, hQU] at a2
      have e3 : dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (texV1Even (parentsAt (u ++ [xd])).even) = dotS (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) - (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) := by
        rw [show W1Odd (u ++ [xd]) = false from ho]; simp [altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, dotS, Prod.fst_zero, Prod.snd_zero, Bool.false_eq_true]
      rw [e3]; simp only [dotS, Prod.fst_sub, Prod.snd_sub] at a1 a2 ⊢; linarith
    rcases hK with hK | hK <;> rcases hJ with hJ | hJ
    · -- `(P⁺, P⁻)`
      refine four_of_two o _ _ _ _ _ HT {x | x ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) ∧ x + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))}
        (fun x hx => ⟨(hv4 x hx.1).1, (hv5 _ hx.2).1⟩) (fun x hx => ⟨?_, ?_⟩) _
        (fun x hx => regionPP hw P o βP (κ 4) (κ 5) HP hdP botP (fun z hz => (hv4 z hz).2) (fun z hz => (hv5 z hz).2) x hx.1 hx.2)
        y ⟨hK, hJ⟩
      · have := rP _ _ hx.2; rw [e54] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x = De (u ++ [xd]) - (x + texV2 (curE (u ++ [xd]))) by abel]; exact this
      · have := rP _ _ hx.1; rw [e45] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - x by abel]; exact this
    · -- `(P⁺, Q⁻²)`, the half-turn image of `(Q⁺¹, P⁻)`
      refine AltLatticeOddWMain.four_partner o _ _ _ _ _ HT y hy hyv ?_
      have m1' : De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) := by have := rQ _ _ hJ; rw [e30, es'] at this; exact this
      have m2' : De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) := by have := rP _ _ hK; rw [e45, ← es] at this; exact this
      exact regionM_even hw hph' P Q o βP βQ (κ 0) (κ 4) (κ 5) HP hdP botP botQ (fun z hz => (hv0 z hz).2)
        (fun z hz => (hv5 z hz).2) k54 k40 _ m1' m2'
    · -- `(Q⁺¹, P⁻)`
      exact regionM_even hw hph' P Q o βP βQ (κ 0) (κ 4) (κ 5) HP hdP botP botQ (fun z hz => (hv0 z hz).2)
        (fun z hz => (hv5 z hz).2) k54 k40 y hK hJ
    · -- `(Q⁺¹, Q⁻²)`
      refine four_of_two o _ _ _ _ _ HT {x | x ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) ∧ x + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2)}
        (fun x hx => ⟨(hv0 x hx.1).1, (hv3 _ hx.2).1⟩) (fun x hx => ⟨?_, ?_⟩) _
        (fun x hx => regionQQ hw Q o βQ (κ 0) (κ 3) HQ hdQ botQ (fun z hz => (hv0 z hz).2) (fun z hz => (hv3 z hz).2) x hx.1 hx.2)
        y ⟨hK, hJ⟩
      · have := rQ _ _ hx.2; rw [e30] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x = De (u ++ [xd]) - (x + texV2 (curE (u ++ [xd]))) by abel]; exact this
      · have := rQ _ _ hx.1; rw [e03] at this; rw [show De (u ++ [xd]) - texV2 (curE (u ++ [xd])) - x + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - x by abel]; exact this

end FLatticePaper.Tiles.AltLatticeEvenVMain
