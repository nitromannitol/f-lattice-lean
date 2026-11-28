import FLatticePaper.Tiles.TileHalfTurnGlue
import FLatticePaper.Tiles.StdPairCompatPaper

/-! # (b) of `lemma:tile-odometer-existence` for the standard children that are not corrected (Case 1)

The half-turn `y ↦ D_{p₀} - y` about the centre of the odd standard tile sends the six copies of its decomposition to each other
(`0 ↔ 1`, `2 ↔ 5`, `3 ↔ 4`), with offsets `u + u' + D_r = D_{p₀}` and affine factors `η + η' = a_{p₀,2} - a_{r,2}`; for the even
standard tile the pairs are `0 ↔ 3`, `1 ↔ 2`, `4 ↔ 5`. With the half-turn identities of the parents (normalised with slope `0`),
`TileHalfTurnGlue.glue_halfTurn_self` gives the identity of the child.

`RawHT o C a` is the half-turn identity `2(o(C - z) - o(z)) = aᵀC - 2aᵀz` without normalisation; `raw_of_tileHalfTurn` and
`tileHalfTurn_of_raw` pass between it and `TileHalfTurn` for odometers normalised with slope `0`. -/

namespace FLatticePaper.Tiles.TileHalfTurnStd

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (pieceVal goodPart)
open FLatticePaper.Tiles.JointRot (SlopeZero)
open FLatticePaper.Tiles.TileStepAssembly (tOP tEP)
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt)
open FLatticePaper.Tiles.SurgicalDict (offsetP0 offsetQ0)

/-- The half-turn identity about `C` with slope `a`, without normalisation. -/
def RawHT (o : PartialOdometer) (C a : Site) : Prop :=
  ∀ z ∈ o.dom, C - z ∈ o.dom ∧ 2 * (o.val (C - z) - o.val z) = dotS a C - 2 * dotS a z

theorem normed_zero (o : PartialOdometer) (β : ℤ) (x : Site) : normed o 0 β x = o.val x - β := by
  simp [normed, dotS]

theorem raw_of_tileHalfTurn (o : PartialOdometer) (v1 v2 a2 : Site) (h : TileHalfTurn o v1 v2 a2) (hs : SlopeZero o) :
    RawHT o (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) a2 := by
  obtain ⟨α, β, hF, hH⟩ := h
  obtain ⟨β', hF'⟩ := hs
  obtain ⟨rfl, -⟩ := WeakStepAssembly.normal_unique o α 0 β β' hF hF'
  intro z hz
  obtain ⟨h1, h2⟩ := hH z hz
  rw [normed_zero, normed_zero] at h2
  exact ⟨h1, by linarith⟩

theorem tileHalfTurn_of_raw (o : PartialOdometer) (v1 v2 a2 : Site) (hs : SlopeZero o)
    (h : RawHT o (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) a2) : TileHalfTurn o v1 v2 a2 := by
  obtain ⟨β, hF⟩ := hs
  refine ⟨0, β, hF, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := h x hx
  rw [normed_zero, normed_zero]
  exact ⟨h1, by linarith⟩

theorem raw_of_altHalfTurn (o : PartialOdometer) (Dh E : Site) (h : AltHalfTurn o Dh E) (hs : SlopeZero o) :
    RawHT o Dh E := by
  obtain ⟨α, β, hF, hH⟩ := h
  obtain ⟨β', hF'⟩ := hs
  obtain ⟨rfl, -⟩ := WeakStepAssembly.normal_unique o α 0 β β' hF hF'
  intro z hz
  obtain ⟨h1, h2⟩ := hH z hz
  rw [normed_zero, normed_zero] at h2
  exact ⟨h1, by linarith⟩

theorem altHalfTurn_of_raw (o : PartialOdometer) (Dh E : Site) (hs : SlopeZero o) (h : RawHT o Dh E) :
    AltHalfTurn o Dh E := by
  obtain ⟨β, hF⟩ := hs
  refine ⟨0, β, hF, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := h x hx
  rw [normed_zero, normed_zero]
  exact ⟨h1, by linarith⟩

/-! ### The centres and slopes -/

/-- The centre of the odd standard tile of a fraction. -/
abbrev cOdd (f : Fraction) : Site := texV1Odd f + texV2 f + ((1 : ℤ), (-1 : ℤ))

/-- The centre of the even standard tile of a fraction. -/
abbrev cEven (f : Fraction) : Site := texV1Even f + texV2 f + ((1 : ℤ), (-1 : ℤ))

/-- The second affine factor `a_{f,2}`. -/
abbrev aF (f : Fraction) : Site := offsetA f.num f.den true

/-! ### The odd standard child that is not corrected -/

theorem tOP_full (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? ≠ some Digit.three) :
    tOP D f w = [stdPiece (f u1).tOdd (p0Off w .p1Plus) (p0Aff w .p1Plus),
      stdPiece (f u1).tOdd (p0Off w .p1Minus) (p0Aff w .p1Minus),
      stdPiece (f u2).tEven (p0Off w .q1DPlus) (p0Aff w .q1DPlus),
      stdPiece (f u2).tEven (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus),
      stdPiece (f u2).tEven (p0Off w .q1DMinus) (p0Aff w .q1DMinus),
      stdPiece (f u2).tEven (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus)] := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  simp [tOP, tileOddPieces, hr, regOdo, e1, e2, h3]

/-- The offsets of the odd standard decomposition under the half-turn. -/
theorem odd_offs (w : Word) :
    let D := cOdd ((parentsAt w).current .odd)
    let Cp := cOdd (parentsAt w).odd
    let Cq := cEven (parentsAt w).even
    p0Off w .p1Minus = D - Cp - p0Off w .p1Plus ∧ p0Off w .p1Plus = D - Cp - p0Off w .p1Minus ∧
      p0Off w .q1DMinus + vQ1 w = D - Cq - p0Off w .q1DPlus ∧ p0Off w .q1DMinus = D - Cq - (p0Off w .q1DPlus + vQ1 w) ∧
      p0Off w .q1DPlus + vQ1 w = D - Cq - p0Off w .q1DMinus ∧ p0Off w .q1DPlus = D - Cq - (p0Off w .q1DMinus + vQ1 w) := by
  intro D Cp Cq
  simp only [D, Cp, Cq, cOdd, cEven, p0Off, offsetP0, vP1, vP2, vQ1, vQ2, Parents.current, Parents.combine]
  cases W1Odd w <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp [texV1Odd, texV1Even, texV2] <;> ring

/-- The affine factors of the odd standard decomposition under the half-turn. -/
theorem odd_affs (w : Word) :
    let E := aF ((parentsAt w).current .odd)
    p0Aff w .p1Plus + p0Aff w .p1Minus = E - aF (parentsAt w).odd ∧
      p0Aff w .q1DPlus + p0Aff w .q1DMinus = E - aF (parentsAt w).even := by
  intro E
  simp only [E, aF, p0Aff, pairAffine, offsetA, Parents.current, Parents.combine]
  cases W1Odd w <;> simp only [if_true, if_false, Bool.false_eq_true] <;> refine ⟨?_, ?_⟩ <;> ext <;> simp

/-- **Case 1, odd child**: the odd standard tile odometer of a word that does not end in `3` has the half-turn identity. -/
theorem halfTurn_oddStd (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h3 : w.getLast? ≠ some Digit.three) (o : PartialOdometer)
    (hR : RespectsPieces o (tOP D f w)) (hconn : (overlapGraph (goodPart (tOP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (cOdd (parentsAt w).odd) (aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (cEven (parentsAt w).even) (aF (parentsAt w).even)) {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (cOdd ((parentsAt w).current .odd)) (aF ((parentsAt w).current .odd)) := by
  have hL := tOP_full D f w u1 u2 hr hl1 hl2 h3
  obtain ⟨o01, o10, o25, o34, o43, o52⟩ := odd_offs w
  obtain ⟨aPP, aQQ⟩ := odd_affs w
  have aPP' := (add_comm _ _).trans aPP
  have aQQ' := (add_comm _ _).trans aQQ
  refine TileHalfTurnGlue.glue_halfTurn_self (tOP D f w) o hR (JointGlue.tileOddPieces_covered _ _ _ _ _) hconn
    (fun i => [1, 0, 5, 4, 3, 2].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o01 aPP⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o10 aPP'⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o25 aQQ⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o34 aQQ⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o43 aQQ'⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o52 aQQ'⟩
  · simp at hp

/-! ### The even standard child that is not corrected -/

theorem tEP_full (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? ≠ some Digit.two) :
    tEP D f w = [stdPiece (f u1).tOdd (q0Off w .p1DPlus) (q0Aff w .p1DPlus),
      stdPiece (f u1).tOdd (q0Off w .p1DPlus + vP2 w) (q0Aff w .p1DPlus + aP2 w),
      stdPiece (f u1).tOdd (q0Off w .p1DMinus) (q0Aff w .p1DMinus),
      stdPiece (f u1).tOdd (q0Off w .p1DMinus + vP2 w) (q0Aff w .p1DMinus + aP2 w),
      stdPiece (f u2).tEven (q0Off w .q1Plus) (q0Aff w .q1Plus),
      stdPiece (f u2).tEven (q0Off w .q1Minus) (q0Aff w .q1Minus)] := by
  have e1 : below f w u1 = f u1 := JointRot.below_of_lt f w u1 hl1
  have e2 : below f w u2 = f u2 := JointRot.below_of_lt f w u2 hl2
  simp [tEP, tileEvenPieces, hr, regOdo, e1, e2, h2]

/-- The offsets of the even standard decomposition under the half-turn. -/
theorem even_offs (w : Word) :
    let D := cEven ((parentsAt w).current .even)
    let Cp := cOdd (parentsAt w).odd
    let Cq := cEven (parentsAt w).even
    q0Off w .p1DMinus + vP2 w = D - Cp - q0Off w .p1DPlus ∧ q0Off w .p1DMinus = D - Cp - (q0Off w .p1DPlus + vP2 w) ∧
      q0Off w .p1DPlus + vP2 w = D - Cp - q0Off w .p1DMinus ∧ q0Off w .p1DPlus = D - Cp - (q0Off w .p1DMinus + vP2 w) ∧
      q0Off w .q1Minus = D - Cq - q0Off w .q1Plus ∧ q0Off w .q1Plus = D - Cq - q0Off w .q1Minus := by
  intro D Cp Cq
  simp only [D, Cp, Cq, cOdd, cEven, q0Off, offsetQ0, vP1, vP2, vQ1, vQ2, Parents.current, Parents.combine]
  cases W1Odd w <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp [texV1Odd, texV1Even, texV2] <;> ring

/-- The affine factors of the even standard decomposition under the half-turn. -/
theorem even_affs (w : Word) :
    let E := aF ((parentsAt w).current .even)
    q0Aff w .p1DPlus + (q0Aff w .p1DMinus + aP2 w) = E - aF (parentsAt w).odd ∧
      (q0Aff w .p1DPlus + aP2 w) + q0Aff w .p1DMinus = E - aF (parentsAt w).odd ∧
      q0Aff w .q1Plus + q0Aff w .q1Minus = E - aF (parentsAt w).even := by
  intro E
  simp only [E, aF, q0Aff, aP2, pairAffine, offsetA, Parents.current, Parents.combine]
  cases W1Odd w <;> simp only [if_true, if_false, Bool.false_eq_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

/-- **Case 1, even child** (by the rotation in the text; here directly): the even standard tile odometer of a word that does not
end in `2` has the half-turn identity. -/
theorem halfTurn_evenStd (D : JointData) (f : Word → JSlice) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2))
    (hl1 : u1.length < w.length) (hl2 : u2.length < w.length) (h2 : w.getLast? ≠ some Digit.two) (o : PartialOdometer)
    (hR : RespectsPieces o (tEP D f w)) (hconn : (overlapGraph (goodPart (tEP D f w))).Connected)
    (hP : RawHT (f u1).tOdd (cOdd (parentsAt w).odd) (aF (parentsAt w).odd))
    (hQ : RawHT (f u2).tEven (cEven (parentsAt w).even) (aF (parentsAt w).even)) {y0 : Site} (hy0 : y0 ∈ o.dom) :
    RawHT o (cEven ((parentsAt w).current .even)) (aF ((parentsAt w).current .even)) := by
  have hL := tEP_full D f w u1 u2 hr hl1 hl2 h2
  obtain ⟨o03, o12, o21, o30, o45, o54⟩ := even_offs w
  obtain ⟨a03, a12, a45⟩ := even_affs w
  refine TileHalfTurnGlue.glue_halfTurn_self (tEP D f w) o hR (JointGlue.tileEvenPieces_covered _ _ _ _ _) hconn
    (fun i => [3, 2, 1, 0, 5, 4].getD i 0) _ _ ?_ hy0
  intro i p hp
  rw [hL] at hp ⊢
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o03 a03⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o12 a12⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o21 ((add_comm _ _).trans a12)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hP _ _ _ _ _ _ o30 ((add_comm _ _).trans a03)⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o45 a45⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
    exact ⟨_, rfl, TileHalfTurnGlue.std_pair _ _ _ hQ _ _ _ _ _ _ o54 ((add_comm _ _).trans a45)⟩
  · simp at hp

end FLatticePaper.Tiles.TileHalfTurnStd
