import FLatticePaper.Tiles.AltGlueEven
import FLatticePaper.Tiles.AltLatticeOddWMain
import FLatticePaper.Tiles.AltLatticeEvenVArith

/-! # Item (b) of `lemma:weak_alternate_odometer_properties`: the even alternate child along its second period

Geometry of the self-overlap of `T̂(q₀)` along `v = v_{q₀,2}` at a word `u x` of type one or two. A point `x` of `T̂(q₀)` with
`x + v ∈ T̂(q₀)` lies in `T(p₁)^+` or `T(q₁)^{+,1}`, and `x + v` in `T(p₁)^-` or `T(q₁)^{-,2}`: on the other five pieces
`t_{q₀}(x) - T(q₀)` is below `t_{q₀}(D̂) - 2 d_{q₀}`, the lower bound of `t_{q₀}` on `T̂(q₀)` (the claim of the text
`AltBounds.claim_all` and the half-turn), and the other side follows by the half-turn. -/

namespace FLatticePaper.Tiles.AltLatticeEvenV

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1)
open FLatticePaper.Tiles.AltGlueEven (De cHe pieces7e)
open FLatticePaper.Tiles.SiteInduction (InH curE)

/-- **The exclusion by `t_{q₀}`**: a point whose `t_{q₀}` is at most `M`, with `M - T(q₀)` below the lower bound
`t_{q₀}(D̂) - 2 d_{q₀}` of `t_{q₀}` on `T̂(q₀)`, has its translate by `v_{q₀,2}` outside `T̂(q₀)`. -/
theorem excl_core (w : Word) (x : Site) (M : ℤ) (hx : (curE w).num * x.1 - (curE w).den * x.2 ≤ M)
    (hM : M - SiteInduction.tOf (curE w) < (curE w).num * (De w).1 - (curE w).den * (De w).2 - 2 * (curE w).den) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w := by
  intro h
  have hD := (AltPieces.altEven_halfTurn w _).1 h
  have c := ((AltBounds.claim_all w).2 _ hD).1
  have e : De w = AltPieces.centreEven (phase w == 1) (parentsAt w).odd (parentsAt w).even := rfl
  rw [e] at hM
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, texV2] at c
  simp only [SiteInduction.tOf] at hM
  nlinarith

/-- On a copy of `T(p₁)` at `a`, `t_{q₀} ≤ t_{q₀}(a) + 2 d_{q₀}`. -/
theorem excl_P {w : Word} (hw : ¬ IsBase w) (a x : Site) (hx : x ∈ shift (stateAt w).tOdd a)
    (hM : (curE w).num * a.1 - (curE w).den * a.2 + 2 * (curE w).den - SiteInduction.tOf (curE w) <
      (curE w).num * (De w).1 - (curE w).den * (De w).2 - 2 * (curE w).den) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w :=
  excl_core w x _ (by have := AltItem4.Ls_pcopy hw a x hx; linarith) hM

/-- On a copy of `T(q₁)` at `a`, `t_{q₀} ≤ t_{q₀}(a) + 2 d_{q₀}`. -/
theorem excl_Q {w : Word} (hw : ¬ IsBase w) (a x : Site) (hx : x ∈ shift (stateAt w).tEven a)
    (hM : (curE w).num * a.1 - (curE w).den * a.2 + 2 * (curE w).den - SiteInduction.tOf (curE w) <
      (curE w).num * (De w).1 - (curE w).den * (De w).2 - 2 * (curE w).den) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w :=
  excl_core w x _ (by have := AltItem4.Ls_qcopy hw a x hx; linarith) hM

/-- On the parent piece `T̂(p₁) + h'`, `t_{q₀} ≤ t_{q₀}(h') + 2 d_{q₀} + 3` (the claim on `T̂(p₁)` and `|det| = 1`). -/
theorem excl_H {u : Word} {xd : Digit} (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (a x : Site)
    (hxa : x ∈ shift (altOddTile AltRotStep.B u) a)
    (hM : (curE (u ++ [xd])).num * a.1 - (curE (u ++ [xd])).den * a.2 + 2 * (curE (u ++ [xd])).den + 3 -
        SiteInduction.tOf (curE (u ++ [xd])) <
      (curE (u ++ [xd])).num * (De (u ++ [xd])).1 - (curE (u ++ [xd])).den * (De (u ++ [xd])).2 - 2 * (curE (u ++ [xd])).den) :
    x + texV2 (curE (u ++ [xd])) ∉ altEvenTile AltRotStep.B (u ++ [xd]) := by
  refine excl_core _ x _ ?_ hM
  rw [mem_shift] at hxa
  obtain ⟨c1, c2⟩ := (AltBounds.claim_all u).1 _ hxa
  have hp : SiteInduction.curO u = (parentsAt (u ++ [xd])).odd := by
    cases xd with
    | one => exact (HorizontalStep.par_one u).1.symm
    | two => exact (HorizontalStep.par_two u).1.symm
    | three => exact absurd rfl hx
  rw [hp] at c1 c2
  obtain ⟨h1, h2, h3, h4, -, -, hdet⟩ := AltPieces.parents_facts hw
  have hd : (parentsAt (u ++ [xd])).odd.num * (parentsAt (u ++ [xd])).even.den -
      (parentsAt (u ++ [xd])).even.num * (parentsAt (u ++ [xd])).odd.den = 1 ∨
      (parentsAt (u ++ [xd])).odd.num * (parentsAt (u ++ [xd])).even.den -
      (parentsAt (u ++ [xd])).even.num * (parentsAt (u ++ [xd])).odd.den = -1 := by
    split_ifs at hdet <;> simp [hdet]
  rw [abs_le] at c2
  simp only [curE, Parents.current, Parents.combine, Prod.fst_sub, Prod.snd_sub] at c1 c2 ⊢
  generalize (parentsAt (u ++ [xd])).odd.num = n1 at *
  generalize (parentsAt (u ++ [xd])).odd.den = d1 at *
  generalize (parentsAt (u ++ [xd])).even.num = n2 at *
  generalize (parentsAt (u ++ [xd])).even.den = d2 at *
  have iden : d1 * ((1 * n1 + 1 * n2 + n1) * x.1 - (1 * d1 + 1 * d2 + d1) * x.2 -
      ((1 * n1 + 1 * n2 + n1) * a.1 - (1 * d1 + 1 * d2 + d1) * a.2 + 2 * (1 * d1 + 1 * d2 + d1) + 3)) =
      (d1 * n2 - d2 * n1) * (x.1 - a.1) - (2 * d1 + d2) * (d1 * (x.2 - a.2) - n1 * (x.1 - a.1) + 2 * d1) - 3 * d1 := by
    ring
  have hz : (d1 * n2 - d2 * n1) * (x.1 - a.1) ≤ 3 * d1 := by
    rcases hd with hd | hd
    · rw [show d1 * n2 - d2 * n1 = -1 by linarith]; linarith
    · rw [show d1 * n2 - d2 * n1 = 1 by linarith]; linarith
  have hpos : 0 ≤ (2 * d1 + d2) * (d1 * (x.2 - a.2) - n1 * (x.1 - a.1) + 2 * d1) :=
    mul_nonneg (by linarith) (by linarith)
  by_contra hc
  push Not at hc
  have := mul_pos (by linarith : (0 : ℤ) < d1) (sub_pos.2 hc)
  nlinarith [iden, hz, hpos, this]

/-! ### The five pieces that cannot carry a point whose translate is in `T̂(q₀)` -/

theorem sep_P5 {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : x ∈ shift (stateAt w).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w := by
  refine excl_P hw _ x hx ?_
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := AltPieces.parents_facts hw
  rcases Bool.eq_false_or_eq_true (W1Odd w) with ho | ho <;> simp only [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, if_true, if_false, Bool.false_eq_true, ho] <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at *
  · nlinarith [AltLatticeEvenVArith.m_o_Pm n1 d1 n2 d2 h1 h2 h3 h4]
  · nlinarith [AltLatticeEvenVArith.m_e_Pm n1 d1 n2 d2 h1 h2 h3 h4]

theorem sep_Q1 {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : x ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w := by
  refine excl_Q hw _ x hx ?_
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := AltPieces.parents_facts hw
  rcases Bool.eq_false_or_eq_true (W1Odd w) with ho | ho <;> simp only [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true, ho] <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at *
  · nlinarith [AltLatticeEvenVArith.m_o_Qp2 n1 d1 n2 d2 h1 h2 h3 h4]
  · nlinarith [AltLatticeEvenVArith.m_e_Qp2 n1 d1 n2 d2 h1 h2 h3 h4]

theorem sep_Q2 {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : x ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus))) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w := by
  refine excl_Q hw _ x hx ?_
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := AltPieces.parents_facts hw
  rcases Bool.eq_false_or_eq_true (W1Odd w) with ho | ho <;> simp only [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, if_true, if_false, Bool.false_eq_true, ho] <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at *
  · nlinarith [AltLatticeEvenVArith.m_o_Qm1 n1 d1 n2 d2 h1 h2 h3 h4]
  · nlinarith [AltLatticeEvenVArith.m_e_Qm1 n1 d1 n2 d2 h1 h2 h3 h4]

theorem sep_Q3 {w : Word} (hw : ¬ IsBase w) (x : Site) (hx : x ∈ shift (stateAt w).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)) :
    x + texV2 (curE w) ∉ altEvenTile AltRotStep.B w := by
  refine excl_Q hw _ x hx ?_
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := AltPieces.parents_facts hw
  rcases Bool.eq_false_or_eq_true (W1Odd w) with ho | ho <;> simp only [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, if_true, if_false, Bool.false_eq_true, ho] <;>
    generalize (parentsAt w).odd.num = n1 at * <;> generalize (parentsAt w).odd.den = d1 at * <;>
    generalize (parentsAt w).even.num = n2 at * <;> generalize (parentsAt w).even.den = d2 at *
  · nlinarith [AltLatticeEvenVArith.m_o_Qm2 n1 d1 n2 d2 h1 h2 h3 h4]
  · nlinarith [AltLatticeEvenVArith.m_e_Qm2 n1 d1 n2 d2 h1 h2 h3 h4]

theorem sep_H {u : Word} {xd : Digit} (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (x : Site)
    (hxa : x ∈ shift (altOddTile AltRotStep.B u) (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd))) :
    x + texV2 (curE (u ++ [xd])) ∉ altEvenTile AltRotStep.B (u ++ [xd]) := by
  refine excl_H hx hw _ x hxa ?_
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := AltPieces.parents_facts hw
  rcases (show xd = Digit.one ∨ xd = Digit.two by cases xd <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hx)
    with rfl | rfl
  · obtain ⟨-, t2, -, t4⟩ := AltGlueEven.type_one_rel u
    rcases Bool.eq_false_or_eq_true (W1Odd (u ++ [Digit.one])) with ho | ho <;>
      simp only [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, if_true, if_false, Bool.false_eq_true, cHe, ho, if_true] <;>
      generalize (parentsAt (u ++ [Digit.one])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [Digit.one])).odd.den = d1 at * <;>
      generalize (parentsAt (u ++ [Digit.one])).even.num = n2 at * <;> generalize (parentsAt (u ++ [Digit.one])).even.den = d2 at *
    · nlinarith [AltLatticeEvenVArith.m_o_H1 n1 d1 n2 d2 h1 h2 h3 h4 t2 t4]
    · nlinarith [AltLatticeEvenVArith.m_e_H1 n1 d1 n2 d2 h1 h2 h3 h4 t2 t4]
  · have t1 := AltGlueEven.type_two_rel u
    rcases Bool.eq_false_or_eq_true (W1Odd (u ++ [Digit.two])) with ho | ho <;>
      simp only [altOff, SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, De, AltPieces.centreEven, curE, Parents.current, Parents.combine, SiteInduction.tOf, if_true, if_false, Bool.false_eq_true, cHe, ho, if_true, show (Digit.two = Digit.one) = False from by simp] <;>
      generalize (parentsAt (u ++ [Digit.two])).odd.num = n1 at * <;> generalize (parentsAt (u ++ [Digit.two])).odd.den = d1 at * <;>
      generalize (parentsAt (u ++ [Digit.two])).even.num = n2 at * <;> generalize (parentsAt (u ++ [Digit.two])).even.den = d2 at *
    · nlinarith [AltLatticeEvenVArith.m_o_H2 n1 d1 n2 d2 h1 h2 h3 h4 t1]
    · nlinarith [AltLatticeEvenVArith.m_e_H2 n1 d1 n2 d2 h1 h2 h3 h4 t1]

/-! ### The translate side, by the half-turn -/

theorem altD_true (u : Word) :
    JointFamily.altD u true = AltPieces.centreOdd (phase u == 1) (parentsAt u).odd (parentsAt u).even := by
  rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;>
    simp only [JointFamily.altD, W1Odd, h] <;> ext <;>
    simp [JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2,
      AltPieces.centreOdd] <;> ring

/-- The parent piece of the even child is symmetric about `D̂`. -/
theorem parent_even_sym (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (z : Site)
    (hz : z ∈ shift (altOddTile AltRotStep.B u) (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd))) : De (u ++ [xd]) - z ∈ shift (altOddTile AltRotStep.B u) (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) := by
  rw [mem_shift] at hz ⊢
  have e := AltGlueEven.off_66e u xd hx
  have h := (AltPieces.altOdd_halfTurn u _).1 hz
  rw [← altD_true] at h
  convert h using 1
  rw [← sub_eq_zero]
  have e2 : De (u ++ [xd]) - z - altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) - (JointFamily.altD u true - (z - altOff (u ++ [xd]) (cHe (u ++ [xd]) xd))) =
      De (u ++ [xd]) - JointFamily.altD u true - altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) - altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) := by abel
  rw [e2, ← e, sub_self]

theorem sepJ_0 (u : Word) (xd : Digit) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hJ : y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))) : False := by
  have h' := AltItem4.qcopy_refl hw (De (u ++ [xd])) _ _ hJ
  have hm : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) := by
    have e : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2 := by
      rw [AltGlueEven.off_03e (u ++ [xd]), AltLatticeOddWMain.Cq_eq hw]
    rw [e] at h'; exact h'
  have hD : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd]) := by
    rw [show De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y by abel]
    exact (AltPieces.altEven_halfTurn _ y).1 hy
  exact sep_Q3 hw _ hm hD

theorem sepJ_1 (u : Word) (xd : Digit) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hJ : y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2)) : False := by
  have h' := AltItem4.qcopy_refl hw (De (u ++ [xd])) _ _ hJ
  have hm : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) := by
    have e : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) := by
      rw [AltGlueEven.off_12e (u ++ [xd]), AltLatticeOddWMain.Cq_eq hw]
    rw [e] at h'; exact h'
  have hD : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd]) := by
    rw [show De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y by abel]
    exact (AltPieces.altEven_halfTurn _ y).1 hy
  exact sep_Q2 hw _ hm hD

theorem sepJ_2 (u : Word) (xd : Digit) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hJ : y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))) : False := by
  have h' := AltItem4.qcopy_refl hw (De (u ++ [xd])) _ _ hJ
  have hm : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) := by
    have e : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).even - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2 := by
      rw [AltGlueEven.off_12e (u ++ [xd]), AltLatticeOddWMain.Cq_eq hw]; abel
    rw [e] at h'; exact h'
  have hD : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd]) := by
    rw [show De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y by abel]
    exact (AltPieces.altEven_halfTurn _ y).1 hy
  exact sep_Q1 hw _ hm hD

theorem sepJ_4 (u : Word) (xd : Digit) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hJ : y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))) : False := by
  have h' := AltItem4.pcopy_refl hw (De (u ++ [xd])) _ _ hJ
  have hm : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) := by
    have e : De (u ++ [xd]) - AltItem4.stdCentre (parentsAt (u ++ [xd])).odd - (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) = altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus) := by
      rw [AltGlueEven.off_45e (u ++ [xd]), AltLatticeOddWMain.Cp_eq hw]
    rw [e] at h'; exact h'
  have hD : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd]) := by
    rw [show De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y by abel]
    exact (AltPieces.altEven_halfTurn _ y).1 hy
  exact sep_P5 hw _ hm hD

theorem sepJ_6 (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hJ : y + texV2 (curE (u ++ [xd])) ∈ shift (altOddTile AltRotStep.B u) (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd))) : False := by
  have hm := parent_even_sym u xd hx _ hJ
  have hD : De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd]) := by
    rw [show De (u ++ [xd]) - (y + texV2 (curE (u ++ [xd]))) + texV2 (curE (u ++ [xd])) = De (u ++ [xd]) - y by abel]
    exact (AltPieces.altEven_halfTurn _ y).1 hy
  exact sep_H hx hw _ hm hD

/-! ### The classification -/

theorem altP1Part_eq (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (aO : Tile) :
    AltRotStep.altP1Part (phase (u ++ [xd]) == 1) xd aO (parentsAt (u ++ [xd])).odd (parentsAt (u ++ [xd])).even = shift aO (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) := by
  cases xd with
  | three => exact absurd rfl hx
  | one => rcases Bool.eq_false_or_eq_true (phase (u ++ [Digit.one]) == 1) with h | h <;> simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, cHe, W1Odd, h, altOff, JointFamily.vP1, JointFamily.vP2,
      JointFamily.vQ1, JointFamily.vQ2]
  | two => rcases Bool.eq_false_or_eq_true (phase (u ++ [Digit.two]) == 1) with h | h <;> simp [AltRotStep.altP1Part, SurgicalAlt.altP1Coeff, cHe, W1Odd, h, altOff, JointFamily.vP1, JointFamily.vP2,
      JointFamily.vQ1, JointFamily.vQ2]

/-- Every point of `T̂(q₀)` lies in one of the seven pieces. -/
theorem mem_pieces (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd])) :
    y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) ∨ y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) ∨ y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) ∨ y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) ∨ y ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) ∨ y ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) ∨
      y ∈ shift (altOddTile AltRotStep.B u) (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) := by
  obtain ⟨y', hy', he⟩ := AltPieces.altEvenTile_eq AltRotStep.B hw
  rw [AltRotStep.altTypeOf_snoc] at hy'
  obtain rfl := Option.some.inj hy'
  have hreg : (SurgicalAltTiles.altRegs AltRotStep.B (u ++ [xd])).1 = altOddTile AltRotStep.B u := by
    cases xd with
    | one => exact (AltBounds.altRegs_one u).1
    | two => exact AltBounds.altRegs_two u
    | three => exact absurd rfl hx
  rw [he, hreg, altP1Part_eq u _ hx, Finset.mem_union, AltPieces.mem_evenStd_iff] at hy
  rcases hy with (⟨a, ha, hK⟩ | ⟨b, hb, hK⟩) | hH
  · simp only [AltPieces.evenPOffs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK)))))
  · simp only [AltPieces.evenQOffs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl hK
    · exact Or.inr (Or.inl (by rw [add_comm]; exact hK))
    · exact Or.inr (Or.inr (Or.inl hK))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [add_comm]; exact hK))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hH)))))

/-- **The classification of the self-overlap of `T̂(q₀)` along `v_{q₀,2}`** (types one and two): `x` lies in
`T(p₁)^+` or `T(q₁)^{+,1}`, and `x + v` in `T(p₁)^-` or `T(q₁)^{-,2}`. -/
theorem classify_V (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd])) (y : Site) (hy : y ∈ altEvenTile AltRotStep.B (u ++ [xd]))
    (hyv : y + texV2 (curE (u ++ [xd])) ∈ altEvenTile AltRotStep.B (u ++ [xd])) :
    (y ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) ∨ y ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))) ∧ (y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tOdd (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) ∨ y + texV2 (curE (u ++ [xd])) ∈ shift (stateAt (u ++ [xd])).tEven (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2)) := by
  refine ⟨?_, ?_⟩
  · rcases mem_pieces u xd hx hw y hy with h | h | h | h | h | h | h
    · exact Or.inr h
    · exact (sep_Q1 hw y h hyv).elim
    · exact (sep_Q2 hw y h hyv).elim
    · exact (sep_Q3 hw y h hyv).elim
    · exact Or.inl h
    · exact (sep_P5 hw y h hyv).elim
    · exact (sep_H hx hw y h hyv).elim
  · rcases mem_pieces u xd hx hw _ hyv with h | h | h | h | h | h | h
    · exact (sepJ_0 u xd hw y hy h).elim
    · exact (sepJ_1 u xd hw y hy h).elim
    · exact (sepJ_2 u xd hw y hy h).elim
    · exact Or.inr h
    · exact (sepJ_4 u xd hw y hy h).elim
    · exact Or.inl h
    · exact (sepJ_6 u xd hx hw y hy h).elim

/-! ### The closed-form facts of the mixed contacts -/

set_option maxHeartbeats 400000 in
/-- **The mixed contact, determinant `-1`**: for `y` in `H_q` with `y + v_{q,1} + v_{p,2}` in `H_p`, also `y + v_{q,2}` is in
`H_q` and `y + v_{q,1}` in `H_p` (the transfer of `AltLatticeOddWArith` at `z = y + v_{q,1}`, where `t_q` is unchanged and
`σ_q` grows by `T_q`). -/
theorem contact_U_even (n1 d1 n2 d2 : ℤ) (hf : 0 < n1 ∧ n1 < d1) (hg : 0 < n2 ∧ n2 < d2) (hqe : (n2 + d2) % 2 = 0)
    (he : n1 * d2 - n2 * d1 = -1) (y1 y2 : ℤ) (hy : InH ⟨n2, d2⟩ (y1, y2))
    (hw : InH ⟨n1, d1⟩ ((y1, y2) + texV1Even ⟨n2, d2⟩ + texV2 ⟨n1, d1⟩)) :
    InH ⟨n2, d2⟩ ((y1, y2) + texV2 ⟨n2, d2⟩) ∧ InH ⟨n1, d1⟩ ((y1, y2) + texV1Even ⟨n2, d2⟩) := by
  have pB : ((texV2 (⟨n1, d1⟩ : Fraction)).1 + (texV2 (⟨n1, d1⟩ : Fraction)).2) % 2 = 0 := by simp only [texV2]; omega
  have pV : ((texV2 (⟨n2, d2⟩ : Fraction)).1 + (texV2 (⟨n2, d2⟩ : Fraction)).2) % 2 = 0 := by simp only [texV2]; omega
  have pU : ((texV1Even (⟨n2, d2⟩ : Fraction)).1 + (texV1Even (⟨n2, d2⟩ : Fraction)).2) % 2 = 0 := by
    simp only [texV1Even]; omega
  have hbox := (AltPieces.inH_box ⟨n2, d2⟩ hg.1 hg.2 (y1, y2) hy).2.2.1
  unfold InH at hy hw ⊢
  rw [AltLatticeOddW.decide_par_add _ _ pB, AltLatticeOddW.decide_par_add _ _ pU] at hw
  rw [AltLatticeOddW.decide_par_add _ _ pV, AltLatticeOddW.decide_par_add _ _ pU]
  obtain ⟨q1, q2, q3, q4⟩ := hy
  obtain ⟨p1, p2, p3, p4⟩ := hw
  simp only [SiteInduction.tCo, SiteInduction.sCo, SiteInduction.tOf, texV2, texV1Even, Prod.fst_add, Prod.snd_add] at q1 q2 q3 q4 p1 p2 p3 p4 hbox ⊢
  rcases Bool.eq_false_or_eq_true (decide ((y1 + y2) % 2 = 0)) with hb | hb <;> rw [hb] at q1 q2 q3 q4 p1 p2 p3 p4 ⊢ <;>
    simp only [SiteInduction.aOf, SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at q1 q2 q3 q4 p1 p2 p3 p4 ⊢
  · -- even parity
    have G1 := AltLatticeOddWArith.gq_even n1 d1 n2 d2 (y1 + d2) (y2 + n2) hf.1 hf.2 hg.1 hg.2 he (by linarith) (by linarith)
    have G2 := AltLatticeOddWArith.gp_even n1 d1 n2 d2 (y1 + d2) (y2 + n2) hf.1 hf.2 hg.1 hg.2 he (by linarith) (by linarith)
      (by linarith)
    exact ⟨⟨by linarith, by nlinarith, by linarith, by linarith⟩, ⟨by nlinarith, G2, by linarith, by linarith⟩⟩
  · -- odd parity
    have G1 := AltLatticeOddWArith.gq_odd n1 d1 n2 d2 (y1 + d2) (y2 + n2) hf.1 hf.2 hg.1 hg.2 he (by linarith) (by linarith)
    have G2 := AltLatticeOddWArith.gp_odd n1 d1 n2 d2 (y1 + d2) (y2 + n2) hf.1 hf.2 hg.1 hg.2 he G1 (by linarith)
      (by nlinarith [min_le_left (d2 - n2) (3 * n2 - d2)]) (by linarith)
    exact ⟨⟨by linarith, by nlinarith, by linarith, by linarith⟩, ⟨by nlinarith, by linarith, by linarith, by linarith⟩⟩

set_option maxHeartbeats 400000 in
/-- **The mixed contact, determinant `+1`**: for `y` with `y + v_{q,1}` in `H_p` and `y + v_{q,2}` in `H_q`, also
`y + v_{q,1} + v_{p,2}` is in `H_p` and `y` in `H_q`. -/
theorem contact_U_odd (n1 d1 n2 d2 : ℤ) (hf : 0 < n1 ∧ n1 < d1) (hg : 0 < n2 ∧ n2 < d2) (hqe : (n2 + d2) % 2 = 0)
    (he : n1 * d2 - n2 * d1 = 1) (y1 y2 : ℤ) (hz : InH ⟨n1, d1⟩ ((y1, y2) + texV1Even ⟨n2, d2⟩))
    (hv : InH ⟨n2, d2⟩ ((y1, y2) + texV2 ⟨n2, d2⟩)) :
    InH ⟨n1, d1⟩ ((y1, y2) + texV1Even ⟨n2, d2⟩ + texV2 ⟨n1, d1⟩) ∧ InH ⟨n2, d2⟩ (y1, y2) := by
  have he' : n2 * d1 - n1 * d2 = -1 := by linarith
  have hTp : 0 < d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2 := by nlinarith [hf.1, hf.2]
  have hTq : 0 < d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2 := by nlinarith [hg.1, hg.2]
  have pB : ((texV2 (⟨n1, d1⟩ : Fraction)).1 + (texV2 (⟨n1, d1⟩ : Fraction)).2) % 2 = 0 := by simp only [texV2]; omega
  have pV : ((texV2 (⟨n2, d2⟩ : Fraction)).1 + (texV2 (⟨n2, d2⟩ : Fraction)).2) % 2 = 0 := by simp only [texV2]; omega
  have pU : ((texV1Even (⟨n2, d2⟩ : Fraction)).1 + (texV1Even (⟨n2, d2⟩ : Fraction)).2) % 2 = 0 := by
    simp only [texV1Even]; omega
  have hbox := (AltPieces.inH_box ⟨n1, d1⟩ hf.1 hf.2 _ hz).2.2.1
  unfold InH at hz hv ⊢
  rw [AltLatticeOddW.decide_par_add _ _ pU] at hz
  rw [AltLatticeOddW.decide_par_add _ _ pV] at hv
  rw [AltLatticeOddW.decide_par_add _ _ pB, AltLatticeOddW.decide_par_add _ _ pU]
  obtain ⟨p1, p2, p3, p4⟩ := hz
  obtain ⟨q1, q2, q3, q4⟩ := hv
  simp only [SiteInduction.tCo, SiteInduction.sCo, SiteInduction.tOf, texV2, texV1Even, Prod.fst_add, Prod.snd_add] at q1 q2 q3 q4 p1 p2 p3 p4 hbox ⊢
  rcases Bool.eq_false_or_eq_true (decide ((y1 + y2) % 2 = 0)) with hb | hb <;> rw [hb] at q1 q2 q3 q4 p1 p2 p3 p4 ⊢ <;>
    simp only [SiteInduction.aOf, SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at q1 q2 q3 q4 p1 p2 p3 p4 ⊢
  · -- even parity
    have G1 := AltLatticeOddWArith.gq_even n2 d2 n1 d1 (y1 + d2) (y2 + n2) hg.1 hg.2 hf.1 hf.2 he' (by linarith)
      (by nlinarith)
    have G2 := AltLatticeOddWArith.gp_even n2 d2 n1 d1 (y1 + d2) (y2 + n2) hg.1 hg.2 hf.1 hf.2 he' (by linarith)
      (by nlinarith) (by linarith)
    exact ⟨⟨by nlinarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  · -- odd parity
    have G1 := AltLatticeOddWArith.gq_odd n2 d2 n1 d1 (y1 + d2) (y2 + n2) hg.1 hg.2 hf.1 hf.2 he' (by linarith)
      (by nlinarith [min_le_left (d2 - n2) (3 * n2 - d2)])
    have G2 := AltLatticeOddWArith.gp_odd n2 d2 n1 d1 (y1 + d2) (y2 + n2) hg.1 hg.2 hf.1 hf.2 he' G1 hbox (by linarith)
      (by linarith)
    exact ⟨⟨by nlinarith, by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

set_option maxHeartbeats 400000 in
/-- **The closed-form facts of a contact of two copies of `T(p₁)`**: two points `y`, `z` of `H_p` with `t(z) = t(y) - T - 2`
and the same parity: `y + v_{p,2}` and `C_p - z + v_{p,2}` are in `H_p`. -/
theorem contact_c_facts_p (n2 d2 : ℤ) (hg : 0 < n2 ∧ n2 < d2)
    (hmg : SiteInduction.muOf ⟨n2, d2⟩ = 2) (y z : Site)
    (hy : InH ⟨n2, d2⟩ y) (hz : InH ⟨n2, d2⟩ z)
    (ht : SiteInduction.tCo ⟨n2, d2⟩ z = SiteInduction.tCo ⟨n2, d2⟩ y - SiteInduction.tOf ⟨n2, d2⟩ - 2)
    (hpar : (z.1 + z.2) % 2 = (y.1 + y.2) % 2) :
    InH ⟨n2, d2⟩ (y + texV2 ⟨n2, d2⟩) ∧
      InH ⟨n2, d2⟩ (AltItem4.stdCentre ⟨n2, d2⟩ - z + texV2 ⟨n2, d2⟩) := by
  have pV : ((texV2 (⟨n2, d2⟩ : Fraction)).1 + (texV2 (⟨n2, d2⟩ : Fraction)).2) % 2 = 0 := by simp only [texV2]; omega
  have hz' := EncUpper.inH_refl _ _ hz
  rw [AltItem4.refl_eq] at hz'
  have pC : ((AltItem4.stdCentre ⟨n2, d2⟩ - z).1 + (AltItem4.stdCentre ⟨n2, d2⟩ - z).2) % 2 = (y.1 + y.2) % 2 := by
    simp only [AltItem4.stdCentre, hmg, Prod.fst_sub, Prod.snd_sub]; omega
  unfold InH at hy hz hz' ⊢
  rw [AltLatticeOddW.decide_par_add _ _ pV, AltLatticeOddW.decide_par_add _ _ pV]
  have e1 : decide ((z.1 + z.2) % 2 = 0) = decide ((y.1 + y.2) % 2 = 0) := by simp only [decide_eq_decide]; omega
  have e2 : decide (((AltItem4.stdCentre ⟨n2, d2⟩ - z).1 + (AltItem4.stdCentre ⟨n2, d2⟩ - z).2) % 2 = 0) =
      decide ((y.1 + y.2) % 2 = 0) := by simp only [decide_eq_decide]; omega
  rw [e1] at hz
  rw [e2] at hz' ⊢
  obtain ⟨y1, y2, y3, y4⟩ := hy
  obtain ⟨z1, z2, z3, z4⟩ := hz
  obtain ⟨c1, c2, c3, c4⟩ := hz'
  have hct : SiteInduction.tCo ⟨n2, d2⟩ (AltItem4.stdCentre ⟨n2, d2⟩ - z) =
      d2 + n2 - SiteInduction.tOf ⟨n2, d2⟩ - SiteInduction.tCo ⟨n2, d2⟩ z := by
    simp only [SiteInduction.tCo, SiteInduction.tOf, AltItem4.stdCentre, hmg, Prod.fst_sub, Prod.snd_sub]; ring
  have htV : ∀ x : Site, SiteInduction.tCo ⟨n2, d2⟩ (x + texV2 ⟨n2, d2⟩) = SiteInduction.tCo ⟨n2, d2⟩ x - SiteInduction.tOf ⟨n2, d2⟩ := by
    intro x; simp only [SiteInduction.tCo, SiteInduction.tOf, texV2, Prod.fst_add, Prod.snd_add]; ring
  have hsV : ∀ x : Site, SiteInduction.sCo ⟨n2, d2⟩ (x + texV2 ⟨n2, d2⟩) = SiteInduction.sCo ⟨n2, d2⟩ x := by
    intro x; simp only [SiteInduction.sCo, texV2, Prod.fst_add, Prod.snd_add]; ring
  rw [htV, htV, hsV, hsV]
  have hT : 0 < SiteInduction.tOf ⟨n2, d2⟩ := by simp only [SiteInduction.tOf]; nlinarith [hg.1, hg.2]
  exact ⟨⟨by linarith, by linarith, y3, y4⟩, ⟨by linarith, by linarith, c3, c4⟩⟩

end FLatticePaper.Tiles.AltLatticeEvenV
