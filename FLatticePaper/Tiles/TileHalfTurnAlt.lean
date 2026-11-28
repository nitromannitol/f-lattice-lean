import FLatticePaper.Tiles.TileHalfTurnStd
import FLatticePaper.Tiles.AltGlueOdd

/-! # (b) of `lemma:tile-odometer-existence` for the alternate children that are not corrected (Case 3)

The half-turn `y ↦ D̂ - y` about the centre `D̂` of the alternate tile sends the seven pieces of the alternate decomposition to
each other: the four copies of the doubled register `0 ↔ 3`, `1 ↔ 2`, the two copies of the other register `4 ↔ 5`, and the
alternate parent piece to itself (`2 t + D̂_{parent} = D̂`, `Ê_{parent} + 2 η = Ê`, as in `AltGlueOdd`). With the half-turn
identities of the parents, `TileHalfTurnGlue.glue_halfTurn_self` gives the identity of the child. The relations of the odd child
are those of `AltGlueOdd` (`off_03`, ..., `aff_66`); those of the even child are below. -/

namespace FLatticePaper.Tiles.TileHalfTurnAlt

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal goodPart)
open FLatticePaper.Tiles.TileStepAssembly (aOP aEP)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.TileHalfTurnStd (RawHT)

theorem flip_off {a b D C : Site} (h : a = D - C - b) : b = D - C - a := by rw [h]; abel

/-! ### The odd alternate child -/

theorem Dw_eq (w : Word) : AltGlueOdd.Dw w = altD w true := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    simp only [AltGlueOdd.Dw, altD, h, AltPieces.centreOdd, beq_self_eq_true, if_true, if_false, Bool.true_eq_false,
      Bool.false_eq_true, beq_iff_eq] <;> ext <;>
    simp [vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2] <;> ring

/-- The odd alternate decomposition of a word that does not end in `2`: the seven pieces of `AltGlueOdd`. -/
theorem aOP_full (D : JointData) (f : Word → JSlice) (u : Word) (x : Digit) (hx : x ≠ Digit.two) (u1 : Word)
    (hr1 : (regsAt (u ++ [x])).1 = some u1) (hl1 : u1.length < (u ++ [x]).length) :
    aOP D f (u ++ [x]) = AltGlueOdd.pieces7 (u ++ [x]) (f u1).tOdd (f u).tEven (f u).aEven := by
  have hr2 : (regsAt (u ++ [x])).2 = some u := ConnectedAltL.regs_pre_snd u x hx
  have hl : u.length < (u ++ [x]).length := by simp
  have e1 : below f (u ++ [x]) u1 = f u1 := JointRot.below_of_lt f _ u1 hl1
  have e2 : below f (u ++ [x]) u = f u := JointRot.below_of_lt f _ u hl
  have hq : (SurgicalAlt.altTypeOf (u ++ [x])).bind (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (u ++ [x])) ty) =
      some (AltGlueOdd.cH (u ++ [x])) := by
    have hl : SurgicalAlt.altTypeOf (u ++ [x]) = some x := by simp [SurgicalAlt.altTypeOf]
    rw [hl, Option.bind_some]
    unfold SurgicalAlt.altQ1Coeff AltGlueOdd.cH
    rw [if_neg hx]
    split_ifs <;> rfl
  have hc : decide ((u ++ [x]).getLast? = some Digit.two) = false := by simpa using hx
  simp only [aOP, tileAltOddPieces, hq, regOdo, hr1, hr2, e1, e2, AltGlueOdd.pieces7, hc, Bool.false_eq_true, if_false,
    List.cons_append, List.nil_append]

/-- **Case 3, odd alternate child**: the odd alternate tile odometer of a word that does not end in `2` has the half-turn
identity. -/
theorem halfTurn_altOdd (D : JointData) (f : Word → JSlice) (u : Word) (x : Digit) (hx : x ≠ Digit.two) (u1 : Word)
    (hr1 : (regsAt (u ++ [x])).1 = some u1) (hl1 : u1.length < (u ++ [x]).length) (o : PartialOdometer)
    (hR : RespectsPieces o (aOP D f (u ++ [x]))) (hconn : (overlapGraph (goodPart (aOP D f (u ++ [x])))).Connected)
    (hP : RawHT (f u1).tOdd (TileHalfTurnStd.cOdd (parentsAt (u ++ [x])).odd) (TileHalfTurnStd.aF (parentsAt (u ++ [x])).odd))
    (hQ : RawHT (f u).tEven (TileHalfTurnStd.cEven (parentsAt (u ++ [x])).even) (TileHalfTurnStd.aF (parentsAt (u ++ [x])).even))
    (hH : RawHT (f u).aEven (altD u false) (altE u)) {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (altD (u ++ [x]) true) (altE (u ++ [x])) := by
  have hL := aOP_full D f u x hx u1 hr1 hl1
  have hD := Dw_eq (u ++ [x])
  have o03 := AltGlueOdd.off_03 (u ++ [x])
  have o12 := AltGlueOdd.off_12 (u ++ [x])
  have o45 := AltGlueOdd.off_45 (u ++ [x])
  have o66 := AltGlueOdd.off_66 u x hx
  rw [hD] at o03 o12 o45 o66
  have a03 := AltGlueOdd.aff_03 (u ++ [x])
  have a12 := AltGlueOdd.aff_12 (u ++ [x])
  have a45 := AltGlueOdd.aff_45 (u ++ [x])
  have a66 := AltGlueOdd.aff_66 u x hx
  have cov : JointGlue.PiecesCovered (aOP D f (u ++ [x])) := by
    rw [hL]
    refine JointGlue.covered_of_no_exc _ (fun p hp => ?_)
    simp only [AltGlueOdd.pieces7, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine TileHalfTurnGlue.glue_halfTurn_self (aOP D f (u ++ [x])) o hR cov hconn
    (fun i => [3, 2, 1, 0, 5, 4, 6].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o03 a03⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o12 a12⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ (flip_off o12) ((add_comm _ _).trans a12)⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ (flip_off o03) ((add_comm _ _).trans a03)⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o45 a45⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ (flip_off o45) ((add_comm _ _).trans a45)⟩
  · simp only [AltGlueOdd.pieces7, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hH _ _ _ _ _ _ o66 a66⟩
  · simp [AltGlueOdd.pieces7] at hp

/-! ### The even alternate child -/

/-- The coefficient vector of the alternate parent piece of the even alternate child after a `1` or a `2`. -/
def cE (w : Word) (x : Digit) : SurgicalAlt.AltCoeff :=
  if W1Odd w then (if x = Digit.one then (0, 1, 1, 0) else (0, 0, 2, 1))
  else (if x = Digit.one then (1, 1, -1, 0) else (0, 0, 0, 1))

/-- The seven pieces of the even alternate child of a word ending in `1` or `2`. -/
def piecesE (w : Word) (x : Digit) (P Q Ph : PartialOdometer) : List Piece :=
  let Sq := (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2
  let cP := SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus
  let cM := SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus
  let c1 := SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus
  let c2 := SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus
  [stdPiece Q (altOff w cP) (altAff w cP), stdPiece Q (altOff w cP + Sq) (altAff w cP + aP2 w),
    stdPiece Q (altOff w cM) (altAff w cM), stdPiece Q (altOff w cM + Sq) (altAff w cM + aP2 w),
    stdPiece P (altOff w c1) (altAff w c1), stdPiece P (altOff w c2) (altAff w c2),
    stdPiece Ph (altOff w (cE w x)) (altAff w (cE w x))]

theorem aEP_full (D : JointData) (f : Word → JSlice) (u : Word) (x : Digit) (hx : x ≠ Digit.three) (u2 : Word)
    (hr2 : (regsAt (u ++ [x])).2 = some u2) (hl2 : u2.length < (u ++ [x]).length) :
    aEP D f (u ++ [x]) = piecesE (u ++ [x]) x (f u).tOdd (f u2).tEven (f u).aOdd := by
  have hr1 : (regsAt (u ++ [x])).1 = some u := ConnectedAltL.regs_pre_fst u x hx
  have hl : u.length < (u ++ [x]).length := by simp
  have e1 : below f (u ++ [x]) u = f u := JointRot.below_of_lt f _ u hl
  have e2 : below f (u ++ [x]) u2 = f u2 := JointRot.below_of_lt f _ u2 hl2
  have hq : (SurgicalAlt.altTypeOf (u ++ [x])).bind (fun ty => SurgicalAlt.altP1Coeff (W1Odd (u ++ [x])) ty) =
      some (cE (u ++ [x]) x) := by
    have hl : SurgicalAlt.altTypeOf (u ++ [x]) = some x := by simp [SurgicalAlt.altTypeOf]
    rw [hl, Option.bind_some]
    unfold SurgicalAlt.altP1Coeff cE
    cases x with
    | three => exact absurd rfl hx
    | one => split_ifs <;> simp_all
    | two => split_ifs <;> simp_all
  have hc : decide ((u ++ [x]).getLast? = some Digit.three) = false := by simpa using hx
  simp only [aEP, tileAltEvenPieces, hq, regOdo, hr1, hr2, e1, e2, piecesE, hc, Bool.false_eq_true, if_false,
    List.cons_append, List.nil_append]

theorem offE_03 (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2 =
      altD w false - TileHalfTurnStd.cEven (parentsAt w).even - altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [altD, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, vP1, vP2, vQ1, vQ2, texV1Odd,
      texV1Even, texV2, TileHalfTurnStd.cEven] <;> ring

theorem offE_12 (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) =
      altD w false - TileHalfTurnStd.cEven (parentsAt w).even - (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [altD, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, vP1, vP2, vQ1, vQ2, texV1Odd,
      texV1Even, texV2, TileHalfTurnStd.cEven] <;> ring

theorem offE_45 (w : Word) :
    altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus) =
      altD w false - TileHalfTurnStd.cOdd (parentsAt w).odd - altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus) := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [altD, h] <;> ext <;>
    simp [altOff, SurgicalAlt.coeffOff, SurgicalAlt.altQ0Coeff, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, TileHalfTurnStd.cOdd] <;>
    ring

theorem affE_03 (w : Word) :
    altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w) =
      altE w - TileHalfTurnStd.aF (parentsAt w).even := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, altE, offsetA, TileHalfTurnStd.aF] <;> ring

theorem affE_12 (w : Word) :
    (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w) + altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) =
      altE w - TileHalfTurnStd.aF (parentsAt w).even := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, altE, offsetA, TileHalfTurnStd.aF] <;> ring

theorem affE_45 (w : Word) :
    altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus) + altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus) =
      altE w - TileHalfTurnStd.aF (parentsAt w).odd := by
  rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;> simp only [h] <;> ext <;>
    simp [altAff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, aP2, aQ2, altE, offsetA, TileHalfTurnStd.aF] <;> ring

theorem offE_66 (u : Word) (x : Digit) (hx : x ≠ Digit.three) :
    altOff (u ++ [x]) (cE (u ++ [x]) x) = altD (u ++ [x]) false - altD u true - altOff (u ++ [x]) (cE (u ++ [x]) x) := by
  cases x with
  | three => exact absurd rfl hx
  | one =>
    simp only [cE, W1Odd, JointRot.phase_snoc_one, altOff, altD]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine, CeilWords.parentsAt_snoc_one] <;> ring
  | two =>
    simp only [cE, W1Odd, JointRot.phase_snoc_two, altOff, altD]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffOff, vP1, vP2, vQ1, vQ2, texV1Odd, texV1Even, texV2, Parents.current,
        Parents.combine, CeilWords.parentsAt_snoc_two] <;> ring

theorem affE_66 (u : Word) (x : Digit) (hx : x ≠ Digit.three) :
    altAff (u ++ [x]) (cE (u ++ [x]) x) + altAff (u ++ [x]) (cE (u ++ [x]) x) = altE (u ++ [x]) - altE u := by
  cases x with
  | three => exact absurd rfl hx
  | one =>
    simp only [cE, W1Odd, JointRot.phase_snoc_one, altAff, altE, aP2, aQ2, CeilWords.parentsAt_snoc_one]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring
  | two =>
    simp only [cE, W1Odd, JointRot.phase_snoc_two, altAff, altE, aP2, aQ2, CeilWords.parentsAt_snoc_two]
    rcases Bool.eq_false_or_eq_true (phase u == 1) with h | h <;> simp only [h] <;> ext <;>
      simp [SurgicalAlt.coeffAffine, offsetA, Parents.current, Parents.combine] <;> ring

/-- **Case 3, even alternate child**: the even alternate tile odometer of a word that does not end in `3` has the half-turn
identity. -/
theorem halfTurn_altEven (D : JointData) (f : Word → JSlice) (u : Word) (x : Digit) (hx : x ≠ Digit.three) (u2 : Word)
    (hr2 : (regsAt (u ++ [x])).2 = some u2) (hl2 : u2.length < (u ++ [x]).length) (o : PartialOdometer)
    (hR : RespectsPieces o (aEP D f (u ++ [x]))) (hconn : (overlapGraph (goodPart (aEP D f (u ++ [x])))).Connected)
    (hP : RawHT (f u).tOdd (TileHalfTurnStd.cOdd (parentsAt (u ++ [x])).odd) (TileHalfTurnStd.aF (parentsAt (u ++ [x])).odd))
    (hQ : RawHT (f u2).tEven (TileHalfTurnStd.cEven (parentsAt (u ++ [x])).even) (TileHalfTurnStd.aF (parentsAt (u ++ [x])).even))
    (hH : RawHT (f u).aOdd (altD u true) (altE u)) {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (altD (u ++ [x]) false) (altE (u ++ [x])) := by
  have hL := aEP_full D f u x hx u2 hr2 hl2
  have o03 := offE_03 (u ++ [x])
  have o12 := offE_12 (u ++ [x])
  have o45 := offE_45 (u ++ [x])
  have o66 := offE_66 u x hx
  have a03 := affE_03 (u ++ [x])
  have a12 := affE_12 (u ++ [x])
  have a45 := affE_45 (u ++ [x])
  have a66 := affE_66 u x hx
  have cov : JointGlue.PiecesCovered (aEP D f (u ++ [x])) := by
    rw [hL]
    refine JointGlue.covered_of_no_exc _ (fun p hp => ?_)
    simp only [piecesE, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine TileHalfTurnGlue.glue_halfTurn_self (aEP D f (u ++ [x])) o hR cov hconn
    (fun i => [3, 2, 1, 0, 5, 4, 6].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · simp only [piecesE, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o03 a03⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o12 a12⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ (flip_off o12) ((add_comm _ _).trans a12)⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ (flip_off o03) ((add_comm _ _).trans a03)⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o45 a45⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ (flip_off o45) ((add_comm _ _).trans a45)⟩
  · simp only [piecesE, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hH _ _ _ _ _ _ o66 a66⟩
  · simp [piecesE] at hp

end FLatticePaper.Tiles.TileHalfTurnAlt
