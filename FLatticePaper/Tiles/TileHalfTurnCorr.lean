import FLatticePaper.Tiles.TileHalfTurnL

/-! # (b) of `lemma:tile-odometer-existence` at the corrected children (Cases 2 and 4)

At a corrected child the two outer copies of the corrected register are the L-corrections `o^{L,±}`; the half-turn about the
centre of the child pairs them (as it pairs the copies they replace), and the half-turn of the L-corrected odometers about the
centre of the register (`TileHalfTurnL`, in the form `CrossHT`) gives the relation of the pair (`cross_pair`). The other copies
are paired as in Cases 1 and 3. -/

namespace FLatticePaper.Tiles.TileHalfTurnCorr

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal goodPart)
open FLatticePaper.Tiles.TileStepAssembly (tOP tEP aOP aEP)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.TileHalfTurnStd (RawHT)

/-- The half-turn about `C` with slope `a` from `T` to `T'`, up to a constant. -/
def CrossHT (T T' : PartialOdometer) (C a : Site) : Prop :=
  ∃ K : ℤ, ∀ z ∈ T.dom, C - z ∈ T'.dom ∧ 2 * (T'.val (C - z) - T.val z) = dotS (-(2 : ℤ) • a) z + K

/-- The half-turn relation of two placed odometers related by `CrossHT`, in the form of `TileHalfTurnGlue.glue_halfTurn`. -/
theorem cross_pair (T T' : PartialOdometer) (C a : Site) (HT : CrossHT T T' C a) (D off off' aff aff' E : Site)
    (hoff : off' = D - C - off) (haff : aff + aff' = E - a) :
    ∃ M : ℤ, ∀ y ∈ (stdPiece T off aff).placed, y ∉ (stdPiece T off aff).exc →
      D - y ∈ (stdPiece T' off' aff').placed ∧ D - y ∉ (stdPiece T' off' aff').exc ∧
      2 * (pieceVal (stdPiece T' off' aff') (D - y) - pieceVal (stdPiece T off aff) y) = dotS (-(2 : ℤ) • E) y + M := by
  obtain ⟨K, hK⟩ := HT
  refine ⟨K + 2 * dotS a off + 2 * dotS aff' D, fun y hy _ => ?_⟩
  rw [AltGlueHalfTurn.mem_placed_iff] at hy
  simp only [stdPiece] at hy
  obtain ⟨h1, h2⟩ := hK _ hy
  have e : D - y - off' = C - (y - off) := by rw [hoff]; abel
  refine ⟨?_, by simp [stdPiece], ?_⟩
  · rw [AltGlueHalfTurn.mem_placed_iff]; simp only [stdPiece]; rw [e]; exact h1
  · simp only [pieceVal, stdPiece]
    rw [e]
    have ha1 := congrArg Prod.fst haff
    have ha2 := congrArg Prod.snd haff
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at ha1 ha2
    simp only [dotS, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h2 ⊢
    linear_combination h2 - 2 * (y.1 * ha1 + y.2 * ha2)

theorem covered_std (ps : List Piece) (h : ∀ p ∈ ps, ∃ T off aff, p = stdPiece T off aff) : JointGlue.PiecesCovered ps :=
  JointGlue.covered_of_no_exc ps (fun p hp => by obtain ⟨T, off, aff, rfl⟩ := h p hp; rfl)

/-! ### Case 2, odd standard child after a `3` -/

theorem tOP_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) :
    (W1Odd w = true → tOP D f w = [stdPiece (f u1).tOdd (p0Off w .p1Plus) (p0Aff w .p1Plus),
      stdPiece (f u1).tOdd (p0Off w .p1Minus) (p0Aff w .p1Minus),
      stdPiece ((below f w w.dropLast).lEven true false) (p0Off w .q1DPlus) (p0Aff w .q1DPlus),
      stdPiece (f u2).tEven (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus),
      stdPiece (f u2).tEven (p0Off w .q1DMinus) (p0Aff w .q1DMinus),
      stdPiece ((below f w w.dropLast).lEven false false) (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus)]) ∧
    (W1Odd w = false → tOP D f w = [stdPiece (f u1).tOdd (p0Off w .p1Plus) (p0Aff w .p1Plus),
      stdPiece (f u1).tOdd (p0Off w .p1Minus) (p0Aff w .p1Minus),
      stdPiece (f u2).tEven (p0Off w .q1DPlus) (p0Aff w .q1DPlus),
      stdPiece ((below f w w.dropLast).lEven true false) (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus),
      stdPiece ((below f w w.dropLast).lEven false false) (p0Off w .q1DMinus) (p0Aff w .q1DMinus),
      stdPiece (f u2).tEven (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus)]) := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  exact ⟨fun ho => by simp [tOP, tileOddPieces, hr, regOdo, e1, e2, h3, ho],
    fun ho => by simp [tOP, tileOddPieces, hr, regOdo, e1, e2, h3, ho]⟩

/-- **Case 2, odd child**: the odd standard tile odometer after a `3` has the half-turn identity, given the half-turn of the even
L-corrected odometers of the even parent in both directions. -/
theorem halfTurn_oddStd_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) (o : PartialOdometer)
    (hR : RespectsPieces o (tOP D f w)) (hconn : (overlapGraph (goodPart (tOP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hpm : CrossHT ((below f w w.dropLast).lEven true false) ((below f w w.dropLast).lEven false false)
      (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hmp : CrossHT ((below f w w.dropLast).lEven false false) ((below f w w.dropLast).lEven true false)
      (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (TileHalfTurnStd.cOdd ((parentsAt w).current .odd)) (TileHalfTurnStd.aF ((parentsAt w).current .odd)) := by
  obtain ⟨o01, o10, o25, o34, o43, o52⟩ := TileHalfTurnStd.odd_offs w
  obtain ⟨aPP, aQQ⟩ := TileHalfTurnStd.odd_affs w
  have aPP' := (add_comm _ _).trans aPP
  have aQQ' := (add_comm _ _).trans aQQ
  refine TileHalfTurnGlue.glue_halfTurn_self (tOP D f w) o hR (JointGlue.tileOddPieces_covered _ _ _ _ _) hconn
    (fun i => [1, 0, 5, 4, 3, 2].getD i 0) _ _ ?_ hy0
  intro i p hp
  rcases Bool.eq_false_or_eq_true (W1Odd w) with hW | hW
  · rw [(tOP_corr D f w u1 u2 hr hl1 hl2 h3).1 hW] at hp ⊢
    rcases i with _ | _ | _ | _ | _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o01 aPP⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o10 aPP'⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, cross_pair _ _ _ _ hpm _ _ _ _ _ _ o25 aQQ⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o34 aQQ⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o43 aQQ'⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, cross_pair _ _ _ _ hmp _ _ _ _ _ _ o52 aQQ'⟩
    · simp at hp
  · rw [(tOP_corr D f w u1 u2 hr hl1 hl2 h3).2 hW] at hp ⊢
    rcases i with _ | _ | _ | _ | _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o01 aPP⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o10 aPP'⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o25 aQQ⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, cross_pair _ _ _ _ hpm _ _ _ _ _ _ o34 aQQ⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, cross_pair _ _ _ _ hmp _ _ _ _ _ _ o43 aQQ'⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
      exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o52 aQQ'⟩
    · simp at hp

/-! ### Case 2 rotated, even standard child after a `2` -/

theorem tEP_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? = some Digit.two) :
    tEP D f w = [stdPiece (f u1).tOdd (q0Off w .p1DPlus) (q0Aff w .p1DPlus),
      stdPiece ((below f w w.dropLast).lOdd false false) (q0Off w .p1DPlus + vP2 w) (q0Aff w .p1DPlus + aP2 w),
      stdPiece ((below f w w.dropLast).lOdd true false) (q0Off w .p1DMinus) (q0Aff w .p1DMinus),
      stdPiece (f u1).tOdd (q0Off w .p1DMinus + vP2 w) (q0Aff w .p1DMinus + aP2 w),
      stdPiece (f u2).tEven (q0Off w .q1Plus) (q0Aff w .q1Plus),
      stdPiece (f u2).tEven (q0Off w .q1Minus) (q0Aff w .q1Minus)] := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  simp [tEP, tileEvenPieces, hr, regOdo, e1, e2, h2]

/-- **Case 2 for the even child**: the even standard tile odometer after a `2` has the half-turn identity, given the half-turn
of the odd L-corrected odometers of the odd parent in both directions. -/
theorem halfTurn_evenStd_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? = some Digit.two) (o : PartialOdometer)
    (hR : RespectsPieces o (tEP D f w)) (hconn : (overlapGraph (goodPart (tEP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hpm : CrossHT ((below f w w.dropLast).lOdd true false) ((below f w w.dropLast).lOdd false false)
      (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hmp : CrossHT ((below f w w.dropLast).lOdd false false) ((below f w w.dropLast).lOdd true false)
      (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (TileHalfTurnStd.cEven ((parentsAt w).current .even)) (TileHalfTurnStd.aF ((parentsAt w).current .even)) := by
  have hL := tEP_corr D f w u1 u2 hr hl1 hl2 h2
  obtain ⟨o03, o12, o21, o30, o45, o54⟩ := TileHalfTurnStd.even_offs w
  obtain ⟨a03, a12, a45⟩ := TileHalfTurnStd.even_affs w
  refine TileHalfTurnGlue.glue_halfTurn_self (tEP D f w) o hR (JointGlue.tileEvenPieces_covered _ _ _ _ _) hconn
    (fun i => [3, 2, 1, 0, 5, 4].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o03 a03⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hmp _ _ _ _ _ _ o12 a12⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hpm _ _ _ _ _ _ o21 ((add_comm _ _).trans a12)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o30 ((add_comm _ _).trans a03)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o45 a45⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o54 ((add_comm _ _).trans a45)⟩
  · simp at hp

/-! ### Case 4, even alternate child after a `3` -/

theorem aEP_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) :
    aEP D f w = [stdPiece ((below f w w.dropLast).lEven true true) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus))
        (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus)),
      stdPiece (f u2).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w),
      stdPiece (f u2).tEven (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus))
        (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus)),
      stdPiece ((below f w w.dropLast).lEven false true) (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).2) (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w),
      stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus))
        (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Plus)),
      stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))
        (altAff w (SurgicalAlt.altQ0Coeff (W1Odd w) .p1Minus))] := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  simp [aEP, tileAltEvenPieces, hr, regOdo, e1, e2, h3, SurgicalAlt.altTypeOf, SurgicalAlt.altP1Coeff]

/-- **Case 4, even alternate child**: the even alternate tile odometer after a `3` has the half-turn identity, given the
half-turn of the elongated even L-corrected odometers of the even parent in both directions. -/
theorem halfTurn_altEven_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? = some Digit.three) (o : PartialOdometer)
    (hR : RespectsPieces o (aEP D f w)) (hconn : (overlapGraph (goodPart (aEP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hpm : CrossHT ((below f w w.dropLast).lEven true true) ((below f w w.dropLast).lEven false true)
      (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hmp : CrossHT ((below f w w.dropLast).lEven false true) ((below f w w.dropLast).lEven true true)
      (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (altD w false) (altE w) := by
  have hL := aEP_corr D f w u1 u2 hr hl1 hl2 h3
  have o03 := TileHalfTurnAlt.offE_03 w
  have o12 := TileHalfTurnAlt.offE_12 w
  have o45 := TileHalfTurnAlt.offE_45 w
  have a03 := TileHalfTurnAlt.affE_03 w
  have a12 := TileHalfTurnAlt.affE_12 w
  have a45 := TileHalfTurnAlt.affE_45 w
  have cov : JointGlue.PiecesCovered (aEP D f w) := by
    rw [hL]
    refine JointGlue.covered_of_no_exc _ (fun p hp => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine TileHalfTurnGlue.glue_halfTurn_self (aEP D f w) o hR cov hconn (fun i => [3, 2, 1, 0, 5, 4].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hpm _ _ _ _ _ _ o03 a03⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o12 a12⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o12)
      ((add_comm _ _).trans a12)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hmp _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o03) ((add_comm _ _).trans a03)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o45 a45⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o45)
      ((add_comm _ _).trans a45)⟩
  · simp at hp

/-! ### Case 4 rotated, odd alternate child after a `2` -/

theorem aOP_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? = some Digit.two) :
    aOP D f w = [stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus))
        (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus)),
      stdPiece ((below f w w.dropLast).lOdd false true) (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w),
      stdPiece ((below f w w.dropLast).lOdd true true) (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus))
        (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus)),
      stdPiece (f u1).tOdd (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) +
        (SurgicalDict.altShifts (W1Odd w) (vP2 w) (vQ1 w)).1) (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w),
      stdPiece (f u2).tEven (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus))
        (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Plus)),
      stdPiece (f u2).tEven (altOff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))
        (altAff w (SurgicalAlt.altP0Coeff (W1Odd w) .q1Minus))] := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  simp [aOP, tileAltOddPieces, hr, regOdo, e1, e2, h2, SurgicalAlt.altTypeOf, SurgicalAlt.altQ1Coeff]

/-- **Case 4 for the odd alternate child**: the odd alternate tile odometer after a `2` has the half-turn identity, given the
half-turn of the elongated odd L-corrected odometers of the odd parent in both directions. -/
theorem halfTurn_altOdd_corr (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? = some Digit.two) (o : PartialOdometer)
    (hR : RespectsPieces o (aOP D f w)) (hconn : (overlapGraph (goodPart (aOP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (TileHalfTurnStd.cEven (parentsAt w).even) (TileHalfTurnStd.aF (parentsAt w).even))
    (hpm : CrossHT ((below f w w.dropLast).lOdd true true) ((below f w w.dropLast).lOdd false true)
      (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    (hmp : CrossHT ((below f w w.dropLast).lOdd false true) ((below f w w.dropLast).lOdd true true)
      (TileHalfTurnStd.cOdd (parentsAt w).odd) (TileHalfTurnStd.aF (parentsAt w).odd))
    {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (altD w true) (altE w) := by
  have hL := aOP_corr D f w u1 u2 hr hl1 hl2 h2
  have hD := TileHalfTurnAlt.Dw_eq w
  have o03 := AltGlueOdd.off_03 w
  have o12 := AltGlueOdd.off_12 w
  have o45 := AltGlueOdd.off_45 w
  rw [hD] at o03 o12 o45
  have a03 := AltGlueOdd.aff_03 w
  have a12 := AltGlueOdd.aff_12 w
  have a45 := AltGlueOdd.aff_45 w
  have cov : JointGlue.PiecesCovered (aOP D f w) := by
    rw [hL]
    refine JointGlue.covered_of_no_exc _ (fun p hp => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  refine TileHalfTurnGlue.glue_halfTurn_self (aOP D f w) o hR cov hconn (fun i => [3, 2, 1, 0, 5, 4].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o03 a03⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hmp _ _ _ _ _ _ o12 a12⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, cross_pair _ _ _ _ hpm _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o12) ((add_comm _ _).trans a12)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o03)
      ((add_comm _ _).trans a03)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o45 a45⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ (TileHalfTurnAlt.flip_off o45)
      ((add_comm _ _).trans a45)⟩
  · simp at hp

end FLatticePaper.Tiles.TileHalfTurnCorr
