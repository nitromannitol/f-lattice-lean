import FLatticePaper.Tiles.AltGlueOdd

/-! # The half-turn of the glued weak alternate odometer of the even child (uncorrected words)

At a non-base word `w = u x` with `x ≠ 3`, the decomposition of the even alternate child has seven pieces: four copies of
`T(q₁)` (two for each shifted doubling, shift `S_q`), two of `T(p₁)`, and the alternate parent `T̂(p₁)` of `u` at the
coefficient vector of the type (`pieces7e`, the entries of `tileAltEvenPieces` without L-corrections). The half-turn about
the centre `D̂` of `T̂(q₀)` exchanges `T(q₁)^{+,1} ↔ T(q₁)^{-,2}`, `T(q₁)^{+,2} ↔ T(q₁)^{-,1}`, `T(p₁)^+ ↔ T(p₁)^-` and maps the
parent piece to itself; as for the odd child (`AltGlueOdd`), an odometer respecting the pieces has the half-turn identity
`2(o(D̂ - y) - o(y)) = EᵀD̂ - 2Eᵀy` (`glue_halfTurn_even`). -/

namespace FLatticePaper.Tiles.AltGlueEven

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (Tile shift mem_shift stateAt IsBase oddTile evenTile)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)
open FLatticePaper.Tiles.JointFamily (Piece stdPiece RespectsPieces altOff altAff aP2 aQ2 W1Odd vP2 vQ1)
open FLatticePaper.Tiles.JointGlue (pieceVal)
open FLatticePaper.Tiles.AltLatticeCore (HalfTurnId)
open FLatticePaper.Tiles.SiteInduction (InH)
open FLatticePaper.Tiles.AltGlueOdd (phi phi_mirror phi_of_pieces respects_std Cp Cq mem_tOdd_iff mem_tEven_iff inH_of)

/-! ### Membership of the common points in the parent tiles -/

/-- The closed-form bounds of `A + B - U` in `T(q₁)` at a word of type one (`q₁ = p₁ + p_u`, `2p₁ - q₁ = q_u`). -/
theorem abu_arith (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2)
    (t1 : d1 < d2) (t2 : d2 < 2 * d1) (t3 : n1 ≤ n2)
    (e1 : -1 ≤ n1 * d2 - n2 * d1) (e2 : n1 * d2 - n2 * d1 ≤ 1) :
    min (2 * n2) (d2 - n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) ≤ n2 * (d1 + n1 - d2) - d2 * (3 * n1 + d1 - n2) ∧
      n2 * (d1 + n1 - d2) - d2 * (3 * n1 + d1 - n2) ≤ d2 + n2 - min (2 * n2) (d2 - n2) ∧
      0 ≤ (d2 + n2) * (d1 + n1 - d2) + (d2 - n2) * (3 * n1 + d1 - n2) ∧
      (d2 + n2) * (d1 + n1 - d2) + (d2 - n2) * (3 * n1 + d1 - n2) ≤ 1 * (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - 0 := by
  have m1 := min_le_right (2 * n2) (d2 - n2)
  have m2 := min_le_left (2 * n2) (d2 - n2)
  have p1 : 0 ≤ d1 * (d2 - d1 - 1) := mul_nonneg (by linarith) (by linarith)
  have p2 : 0 ≤ (d2 - d1) * (d2 - d1 - 1) := mul_nonneg (by linarith) (by linarith)
  have p3 : 0 ≤ (n2 - n1) * (2 * d1 - n1 - (n2 - n1)) := mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ (d2 - d1) * (n2 - n1) := mul_nonneg (by linarith) (by linarith)
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos h1 (sub_pos.2 h2)]
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos (sub_pos.2 t2) h3,
      mul_pos (sub_pos.2 h4) h1, mul_pos (sub_pos.2 h4) (sub_pos.2 h2), mul_pos (sub_pos.2 t2) (sub_pos.2 h4),
      mul_pos (sub_pos.2 t2) h1]
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos (sub_pos.2 t2) h3,
      mul_pos (sub_pos.2 h4) h1, mul_pos (sub_pos.2 h4) (sub_pos.2 h2), mul_pos (sub_pos.2 t2) (sub_pos.2 h4),
      mul_pos (sub_pos.2 t2) h1, mul_pos (sub_pos.2 t1) (sub_pos.2 h4)]

/-- The closed-form bounds of `2U + V` in `T(p₁)` when `d_{q₁} < d_{p₁}` (type two). -/
theorem uuv_arith (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (h3 : 0 < n2) (h4 : n2 < d2) (t1 : d2 < d1)
    (e1 : -1 ≤ n1 * d2 - n2 * d1) :
    min (2 * n1) (d1 - n1) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) ≤ n1 * (d2 + n2) - d1 * (3 * n2 + d2) ∧
      n1 * (d2 + n2) - d1 * (3 * n2 + d2) ≤ d1 + n1 - min (2 * n1) (d1 - n1) ∧
      0 ≤ (d1 + n1) * (d2 + n2) + (d1 - n1) * (3 * n2 + d2) ∧
      (d1 + n1) * (d2 + n2) + (d1 - n1) * (3 * n2 + d2) ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - 0 := by
  have m1 := min_le_right (2 * n1) (d1 - n1)
  have m2 := min_le_left (2 * n1) (d1 - n1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos (sub_pos.2 t1) h1,
      mul_pos (sub_pos.2 t1) (sub_pos.2 h4), mul_pos (sub_pos.2 t1) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) h1,
      mul_pos (sub_pos.2 h4) (sub_pos.2 h2), mul_pos (sub_pos.2 t1) (sub_pos.2 t1)]
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos h1 (sub_pos.2 h4)]
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h4)]
  · nlinarith [mul_pos h1 h3, mul_pos (sub_pos.2 h2) h3, mul_pos (sub_pos.2 t1) h3, mul_pos (sub_pos.2 t1) h1,
      mul_pos (sub_pos.2 t1) (sub_pos.2 h4), mul_pos (sub_pos.2 t1) (sub_pos.2 h2), mul_pos (sub_pos.2 h4) h1,
      mul_pos (sub_pos.2 h4) (sub_pos.2 h2), mul_pos (sub_pos.2 t1) (sub_pos.2 t1)]

theorem cert_q_ABU {w : Word} (hw : ¬ IsBase w) (t1 : (parentsAt w).odd.den < (parentsAt w).even.den) (t2 : (parentsAt w).even.den < 2 * (parentsAt w).odd.den)
    (t3 : (parentsAt w).odd.num ≤ (parentsAt w).even.num) :
    texV1Odd (parentsAt w).odd + texV2 (parentsAt w).odd - texV1Even (parentsAt w).even ∈ (stateAt w).tEven := by
  rw [mem_tEven_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, -, hmq⟩ := AltItem5.parent_hyps hw
  have e1 : -1 ≤ (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den := by split_ifs at hdet <;> omega
  have e2 : (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den ≤ 1 := by split_ifs at hdet <;> omega
  have A := abu_arith _ _ _ _ h1 h2 h3 h4 t1 t2 t3 e1 e2
  apply inH_of
  · intro _
    simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Odd,
      texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, if_true, hmq]
    obtain ⟨a1, a2, a3, a4⟩ := A
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro hpar
    simp only [texV1Odd, texV1Even, texV2, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hpar
    omega

theorem cert_p_2UV {w : Word} (hw : ¬ IsBase w) (t1 : (parentsAt w).even.den < (parentsAt w).odd.den) :
    texV1Even (parentsAt w).even + texV1Even (parentsAt w).even + texV2 (parentsAt w).even ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, -⟩ := AltItem5.parent_hyps hw
  have e1 : -1 ≤ (parentsAt w).odd.num * (parentsAt w).even.den - (parentsAt w).even.num * (parentsAt w).odd.den := by split_ifs at hdet <;> omega
  have A := uuv_arith _ _ _ _ h1 h2 h3 h4 t1 e1
  apply inH_of
  · intro _
    simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Even,
      texV2, Prod.fst_add, Prod.snd_add, if_true, hmp]
    obtain ⟨a1, a2, a3, a4⟩ := A
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro hpar
    simp only [texV1Even, texV2, Prod.fst_add, Prod.snd_add] at hpar
    omega

set_option maxHeartbeats 400000 in
theorem cert_p_BU1 {w : Word} (hw : ¬ IsBase w) (ho : phase w = 1) (t2 : (parentsAt w).even.den < 2 * (parentsAt w).odd.den) (t4 : (parentsAt w).even.num ≤ 2 * (parentsAt w).odd.num) :
    texV2 (parentsAt w).odd + texV1Even (parentsAt w).even + ((1 : ℤ), (0 : ℤ)) ∈ (stateAt w).tOdd := by
  rw [mem_tOdd_iff hw]
  obtain ⟨h1, h2, h3, h4, hpo, hqe, hdet⟩ := AltPieces.parents_facts hw
  obtain ⟨-, -, hmp, hmq⟩ := AltItem5.parent_hyps hw
  rw [if_pos ho] at hdet
  apply inH_of <;> intro hpar <;> simp only [SiteInduction.aOf, SiteInduction.lOf, SiteInduction.tOf, SiteInduction.tCo, SiteInduction.sCo, texV1Even, texV2, Prod.fst_add, Prod.snd_add, if_true, if_false, Bool.false_eq_true, hmp] at hpar ⊢ <;>
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
        mul_pos (sub_pos.2 h2) h3, mul_pos h1 (sub_pos.2 h4), mul_pos (sub_pos.2 h2) h1, mul_pos (sub_pos.2 h4) h3, mul_pos (sub_pos.2 t2) h1, mul_pos (sub_pos.2 t2) h3, mul_nonneg (sub_nonneg.2 t4) h1.le, mul_nonneg (sub_nonneg.2 t4) h3.le])

set_option maxHeartbeats 400000 in
theorem cert_q_zero {w : Word} (hw : ¬ IsBase w) :
    ((0 : ℤ), (0 : ℤ)) ∈ (stateAt w).tEven := by
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

/-! ### The seven pieces and their half-turn pairing -/

/-- The centre `D̂` of the half-turn of `T̂(q₀)` (item (1)). -/
def De (w : Word) : Site := AltPieces.centreEven (W1Odd w) (parentsAt w).odd (parentsAt w).even

/-- The coefficient vector of the alternate parent piece of the even child (types one and two). -/
def cHe (w : Word) (xd : Digit) : SurgicalAlt.AltCoeff :=
  if W1Odd w then (if xd = Digit.one then (0, 1, 1, 0) else (0, 0, 2, 1))
  else (if xd = Digit.one then (1, 1, -1, 0) else (0, 0, 0, 1))

/-- The seven pieces of the even alternate child of a word of type one or two (the entries of `tileAltEvenPieces`). -/
def pieces7e (w : Word) (xd : Digit) (P Q Ph : PartialOdometer) : List Piece :=
  let Sq := (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2
  let cP := SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus
  let cM := SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus
  let c1 := SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus
  let c2 := SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus
  [stdPiece Q (altOff w cP) (altAff w cP), stdPiece Q (altOff w cP + Sq) (altAff w cP + aP2 w),
    stdPiece Q (altOff w cM) (altAff w cM), stdPiece Q (altOff w cM + Sq) (altAff w cM + aP2 w),
    stdPiece P (altOff w c1) (altAff w c1), stdPiece P (altOff w c2) (altAff w c2),
    stdPiece Ph (altOff w (cHe w xd)) (altAff w (cHe w xd))]

theorem off_03e (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2 = De w - Cq w - altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [De, h] <;> ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreEven, Cq] <;> ring

theorem off_12e (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) = De w - Cq w - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [De, h] <;> ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreEven, Cq] <;> ring

theorem off_45e (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus) = De w - Cp w - altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [De, h] <;> ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, AltPieces.centreEven, Cp] <;> ring

theorem aff_03e (w : Word) :
    altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) = JointFamily.altE w - aQ2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;> simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, JointFamily.altE, offsetA] <;> ring

theorem aff_12e (w : Word) :
    (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w) + altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) = JointFamily.altE w - aQ2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;> simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, JointFamily.altE, offsetA] <;> ring

theorem aff_45e (w : Word) :
    altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus) + altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus) = JointFamily.altE w - aP2 w := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;> simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, JointFamily.altE, offsetA] <;> ring

theorem off_66e (u : Word) (x : Digit) (hx : x ≠ Digit.three) :
    altOff (u ++ [x]) (cHe (u ++ [x]) x) = De (u ++ [x]) - JointFamily.altD u true - altOff (u ++ [x]) (cHe (u ++ [x]) x) := by
  cases x with
  | three => exact absurd rfl hx
  | one =>
    simp only [De, cHe, W1Odd, AltItem4.phase_snoc_one, altOff, CeilWords.parentsAt_snoc_one, if_true]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.altD,
        texV1Odd, texV1Even, texV2, AltPieces.centreEven, W1Odd, Parents.current, Parents.combine, h,
        CeilWords.parentsAt_snoc_one] <;> ring
  | two =>
    simp only [De, cHe, W1Odd, AltItem4.phase_snoc_two, altOff, CeilWords.parentsAt_snoc_two]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.altD,
        texV1Odd, texV1Even, texV2, AltPieces.centreEven, W1Odd, Parents.current, Parents.combine, h,
        CeilWords.parentsAt_snoc_two] <;> ring

theorem aff_66e (u : Word) (x : Digit) (hx : x ≠ Digit.three) :
    altAff (u ++ [x]) (cHe (u ++ [x]) x) + altAff (u ++ [x]) (cHe (u ++ [x]) x) =
      JointFamily.altE (u ++ [x]) - JointFamily.altE u := by
  cases x with
  | three => exact absurd rfl hx
  | one =>
    simp only [cHe, W1Odd, AltItem4.phase_snoc_one, altAff, JointFamily.altE, aP2, aQ2, CeilWords.parentsAt_snoc_one, if_true]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring
  | two =>
    simp only [cHe, W1Odd, AltItem4.phase_snoc_two, altAff, JointFamily.altE, aP2, aQ2, CeilWords.parentsAt_snoc_two]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring

theorem pieces7e_mem (w : Word) (xd : Digit) (P Q Ph : PartialOdometer) :
    (stdPiece Q (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))) ∈ pieces7e w xd P Q Ph ∧ (stdPiece Q (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w)) ∈ pieces7e w xd P Q Ph ∧ (stdPiece Q (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus)) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus))) ∈ pieces7e w xd P Q Ph ∧ (stdPiece Q (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w)) ∈ pieces7e w xd P Q Ph ∧ (stdPiece P (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))) ∈ pieces7e w xd P Q Ph ∧ (stdPiece P (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus)) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))) ∈ pieces7e w xd P Q Ph ∧ (stdPiece Ph (altOff w (cHe w xd)) (altAff w (cHe w xd))) ∈ pieces7e w xd P Q Ph := by
  simp [pieces7e]

theorem type_one_rel (u : Word) :
    (parentsAt (u ++ [Digit.one])).odd.den < (parentsAt (u ++ [Digit.one])).even.den ∧
      (parentsAt (u ++ [Digit.one])).even.den < 2 * (parentsAt (u ++ [Digit.one])).odd.den ∧
      (parentsAt (u ++ [Digit.one])).odd.num ≤ (parentsAt (u ++ [Digit.one])).even.num ∧
      (parentsAt (u ++ [Digit.one])).even.num ≤ 2 * (parentsAt (u ++ [Digit.one])).odd.num := by
  have h1 := (parentsAt_valid u).odd_bounds
  have h2 := (parentsAt_valid u).even_bounds
  unfold Fraction.InUnitInterval at h1 h2
  rw [(HorizontalStep.par_one u).1, (HorizontalStep.par_one u).2]
  simp only [Parents.current, Parents.combine]; omega

theorem type_two_rel (u : Word) :
    (parentsAt (u ++ [Digit.two])).even.den < (parentsAt (u ++ [Digit.two])).odd.den := by
  have h1 := (parentsAt_valid u).odd_bounds
  have h2 := (parentsAt_valid u).even_bounds
  unfold Fraction.InUnitInterval at h1 h2
  rw [(HorizontalStep.par_two u).1, (HorizontalStep.par_two u).2]
  simp only [Parents.current, Parents.combine]; omega

set_option maxHeartbeats 400000 in
/-- **The half-turn of the glued even alternate odometer** at a word of type one or two: with the normalised half-turn
identities of the parents, an odometer respecting the seven pieces satisfies `2(o(D̂ - y) - o(y)) = EᵀD̂ - 2Eᵀy`. -/
theorem glue_halfTurn_even (u : Word) (xd : Digit) (hx : xd ≠ Digit.three) (hw : ¬ IsBase (u ++ [xd]))
    (P Q Ph : PartialOdometer) (hdP : P.dom = (stateAt (u ++ [xd])).tOdd) (hdQ : Q.dom = (stateAt (u ++ [xd])).tEven)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ Ph.dom) (h1 : ((1 : ℤ), (0 : ℤ)) ∈ Ph.dom)
    (HP : ∀ z ∈ P.dom, Cp (u ++ [xd]) - z ∈ P.dom ∧
      2 * (P.val (Cp (u ++ [xd]) - z) - P.val z) = dotS (aP2 (u ++ [xd])) (Cp (u ++ [xd])) - 2 * dotS (aP2 (u ++ [xd])) z)
    (HQ : ∀ z ∈ Q.dom, Cq (u ++ [xd]) - z ∈ Q.dom ∧
      2 * (Q.val (Cq (u ++ [xd]) - z) - Q.val z) = dotS (aQ2 (u ++ [xd])) (Cq (u ++ [xd])) - 2 * dotS (aQ2 (u ++ [xd])) z)
    (HH : ∀ z ∈ Ph.dom, JointFamily.altD u true - z ∈ Ph.dom ∧
      2 * (Ph.val (JointFamily.altD u true - z) - Ph.val z) =
        dotS (JointFamily.altE u) (JointFamily.altD u true) - 2 * dotS (JointFamily.altE u) z)
    (o : PartialOdometer) (hR : RespectsPieces o (pieces7e (u ++ [xd]) xd P Q Ph)) :
    HalfTurnId o (De (u ++ [xd])) (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) := by
  have hxd2 : xd = Digit.one ∨ xd = Digit.two := by
    cases xd <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl hx
  obtain ⟨b0, hb0⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).1
  obtain ⟨b1, hb1⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.1
  obtain ⟨b2, hb2⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.1
  obtain ⟨b3, hb3⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.1
  obtain ⟨b4, hb4⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.1
  obtain ⟨b5, hb5⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.2.1
  obtain ⟨b6, hb6⟩ := respects_std o _ hR _ _ _ (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.2.2
  have r0 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b0 b3 hb0 hb3 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (off_03e (u ++ [xd])) (aff_03e (u ++ [xd])))
  have r3 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b3 b0 hb3 hb0 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (by rw [off_03e (u ++ [xd])]; abel) (by rw [add_comm]; exact aff_03e (u ++ [xd])))
  have r1 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b1 b2 hb1 hb2 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (off_12e (u ++ [xd])) (aff_12e (u ++ [xd])))
  have r2 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b2 b1 hb2 hb1 (AltGlueHalfTurn.piece_halfTurn Q _ _ HQ (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (by rw [off_12e (u ++ [xd])]; abel) (by rw [add_comm]; exact aff_12e (u ++ [xd])))
  have r4 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b4 b5 hb4 hb5 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (off_45e (u ++ [xd])) (aff_45e (u ++ [xd])))
  have r5 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b5 b4 hb5 hb4 (AltGlueHalfTurn.piece_halfTurn P _ _ HP (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (by rw [off_45e (u ++ [xd])]; abel) (by rw [add_comm]; exact aff_45e (u ++ [xd])))
  have r6 := phi_of_pieces o _ _ (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) _ b6 b6 hb6 hb6 (AltGlueHalfTurn.piece_halfTurn Ph _ _ HH (De (u ++ [xd])) _ _ _ _ (JointFamily.altE (u ++ [xd]))
    (off_66e u xd hx) (by rw [aff_66e u xd hx]))
  have m6 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) ∈ (stdPiece Ph (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) (altAff (u ++ [xd]) (cHe (u ++ [xd]) xd))).placed := by
    rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, sub_self]; exact h0
  have N6 : ∀ y ∈ (stdPiece Ph (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) (altAff (u ++ [xd]) (cHe (u ++ [xd]) xd))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := by
    intro y hy
    obtain ⟨hy', e1⟩ := r6 y hy
    have e2 := (r6 _ hy').2
    rw [phi_mirror] at e2
    omega
  have final : (∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) → (∀ y ∈ (stdPiece Ph (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) (altAff (u ++ [xd]) (cHe (u ++ [xd]) xd))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) →
      HalfTurnId o (De (u ++ [xd])) (-(2 : ℤ) • JointFamily.altE (u ++ [xd])) (dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd]))) := by
    intro P0 P1 P2 P3 P4 P5 P6 y hy
    have hdom := hR.1
    rw [hdom, JointGlue.mem_pieceUnion] at hy
    obtain ⟨p, hp, hyp⟩ := hy
    have key : De (u ++ [xd]) - y ∈ JointFamily.pieceUnion (pieces7e (u ++ [xd]) xd P Q Ph) ∧ phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := by
      simp only [pieces7e, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.1, (r0 y hyp).1⟩, P0 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.1, (r1 y hyp).1⟩, P1 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.1, (r2 y hyp).1⟩, P2 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).1, (r3 y hyp).1⟩, P3 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.2.1, (r4 y hyp).1⟩, P4 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.1, (r5 y hyp).1⟩, P5 y hyp⟩
      · exact ⟨JointGlue.mem_pieceUnion.2 ⟨_, (pieces7e_mem (u ++ [xd]) xd P Q Ph).2.2.2.2.2.2, (r6 y hyp).1⟩, P6 y hyp⟩
    refine ⟨by rw [hdom]; exact key.1, ?_⟩
    have k2 := key.2
    unfold phi at k2
    simp only [dotS, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at k2 ⊢
    linarith
  have m61 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece Ph (altOff (u ++ [xd]) (cHe (u ++ [xd]) xd)) (altAff (u ++ [xd]) (cHe (u ++ [xd]) xd))).placed := by
    rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, add_sub_cancel_left]; exact h1
  rcases Bool.eq_false_or_eq_true (W1Odd (u ++ [xd])) with ho | ho
  · -- `W₁` odd
    have yc4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) + texV1Odd (parentsAt (u ++ [xd])).odd ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, add_sub_cancel_left]; rw [hdP]; exact AltGlueOdd.cert_p_A hw
    have yc0 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) + texV1Odd (parentsAt (u ++ [xd])).odd ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
      convert cert_q_zero hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho]
    rcases hxd2 with hxd | hxd
    · -- type one
      obtain ⟨t1, t2, t3, t4⟩ : _ := by subst hxd; exact type_one_rel u
      have ya4 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]
        convert cert_p_BU1 hw (by simpa [W1Odd] using ho) t2 t4 using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cHe, ho]
      have yb2 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
        convert AltGlueOdd.cert_q_U hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cHe, ho]
      have P4 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r4 y hy).2.trans ((r4 _ ya4).2.symm.trans (N6 _ m61))
      have P5 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r5 y hy).2.trans ((r5 _ (r4 _ ya4).1).2.symm.trans (by rw [phi_mirror, P4 _ ya4]; ring))
      have P2 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r2 y hy).2.trans ((r2 _ yb2).2.symm.trans (N6 _ m6))
      have P1 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r1 y hy).2.trans ((r1 _ (r2 _ yb2).1).2.symm.trans (by rw [phi_mirror, P2 _ yb2]; ring))
      have P0 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r0 y hy).2.trans ((r0 _ yc0).2.symm.trans (P4 _ yc4))
      have P3 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r3 y hy).2.trans ((r3 _ (r0 _ yc0).1).2.symm.trans (by rw [phi_mirror, P0 _ yc0]; ring))
      exact final P0 P1 P2 P3 P4 P5 N6

    · -- type two
      have t1 := by subst hxd; exact type_two_rel u
      have ya4 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]
        convert cert_p_2UV hw t1 using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cHe, ho] <;> ring
      have yd4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) + (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdP]
        convert AltGlueOdd.cert_p_B1 hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho]
      have yd2 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) + (texV2 (parentsAt (u ++ [xd])).odd + ((1 : ℤ), (0 : ℤ))) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
        convert AltGlueOdd.cert_q_one hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho]
      have P4 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r4 y hy).2.trans ((r4 _ ya4).2.symm.trans (N6 _ m6))
      have P5 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r5 y hy).2.trans ((r5 _ (r4 _ ya4).1).2.symm.trans (by rw [phi_mirror, P4 _ ya4]; ring))
      have P0 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r0 y hy).2.trans ((r0 _ yc0).2.symm.trans (P4 _ yc4))
      have P3 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r3 y hy).2.trans ((r3 _ (r0 _ yc0).1).2.symm.trans (by rw [phi_mirror, P0 _ yc0]; ring))
      have P2 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r2 y hy).2.trans ((r2 _ yd2).2.symm.trans (P4 _ yd4))
      have P1 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r1 y hy).2.trans ((r1 _ (r2 _ yd2).1).2.symm.trans (by rw [phi_mirror, P2 _ yd2]; ring))
      exact final P0 P1 P2 P3 P4 P5 N6

  · -- `W₁` even
    have yb4 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, sub_self]; rw [hdP]; exact AltGlueOdd.cert_p_zero hw
    have yb0 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
      convert AltGlueOdd.cert_q_U hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho]
    have yc5 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece, add_sub_cancel_left]; rw [hdP]; exact AltGlueOdd.cert_p_one hw
    have yc1 : altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed := by
      rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
      convert AltGlueOdd.cert_q_V1 hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, ho] <;> ring
    rcases hxd2 with hxd | hxd
    · -- type one
      obtain ⟨t1, t2, t3, t4⟩ : _ := by subst hxd; exact type_one_rel u
      have ya0 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
        convert cert_q_ABU hw t1 t2 t3 using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cHe, ho] <;> ring
      have P0 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r0 y hy).2.trans ((r0 _ ya0).2.symm.trans (N6 _ m6))

      have P3 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r3 y hy).2.trans ((r3 _ (r0 _ ya0).1).2.symm.trans (by rw [phi_mirror, P0 _ ya0]; ring))
      have P4 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r4 y hy).2.trans ((r4 _ yb4).2.symm.trans (P0 _ yb0))
      have P5 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r5 y hy).2.trans ((r5 _ (r4 _ yb4).1).2.symm.trans (by rw [phi_mirror, P4 _ yb4]; ring))
      have P1 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r1 y hy).2.trans ((r1 _ yc1).2.symm.trans (P5 _ yc5))
      have P2 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r2 y hy).2.trans ((r2 _ (r1 _ yc1).1).2.symm.trans (by rw [phi_mirror, P1 _ yc1]; ring))
      exact final P0 P1 P2 P3 P4 P5 N6

    · -- type two
      have ya0 : altOff (u ++ [xd]) (cHe (u ++ [xd]) xd) + ((1 : ℤ), (0 : ℤ)) ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed := by
        subst hxd; rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [hdQ]
        convert AltGlueOdd.cert_q_V1 hw using 1; ext <;> simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, texV1Odd, texV1Even, texV2, cHe, ho]
      have P0 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r0 y hy).2.trans ((r0 _ ya0).2.symm.trans (N6 _ m61))
      have P3 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r3 y hy).2.trans ((r3 _ (r0 _ ya0).1).2.symm.trans (by rw [phi_mirror, P0 _ ya0]; ring))
      have P4 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Plus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r4 y hy).2.trans ((r4 _ yb4).2.symm.trans (P0 _ yb0))
      have P5 : ∀ y ∈ (stdPiece P (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .p1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r5 y hy).2.trans ((r5 _ (r4 _ yb4).1).2.symm.trans (by rw [phi_mirror, P4 _ yb4]; ring))
      have P1 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + (SurgicalDict.altShifts (W1Odd (u ++ [xd])) (vP2 (u ++ [xd])) (vQ1 (u ++ [xd]))).2) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Plus) + aP2 (u ++ [xd]))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r1 y hy).2.trans ((r1 _ yc1).2.symm.trans (P5 _ yc5))
      have P2 : ∀ y ∈ (stdPiece Q (altOff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus)) (altAff (u ++ [xd]) (SurgicalAlt.altQ0Coeff (W1Odd (u ++ [xd])) .dsQ1Minus))).placed, phi o (De (u ++ [xd])) (JointFamily.altE (u ++ [xd])) y = dotS (JointFamily.altE (u ++ [xd])) (De (u ++ [xd])) := fun y hy =>
        (r2 y hy).2.trans ((r2 _ (r1 _ yc1).1).2.symm.trans (by rw [phi_mirror, P1 _ yc1]; ring))
      exact final P0 P1 P2 P3 P4 P5 N6

end FLatticePaper.Tiles.AltGlueEven
