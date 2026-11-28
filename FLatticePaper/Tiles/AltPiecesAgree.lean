import Mathlib.Tactic.IntervalCases
import FLatticePaper.Tiles.AltSixEven
import FLatticePaper.Tiles.JointGlue

/-! # The seven pieces of an alternate decomposition agree

Case 3 of `lemma:tile-odometer-existence` assembled: the six standard copies of an alternate child agree with explicit constants
on the marks of the mixed pairs and on the overlaps of the doubled pairs (`AltSixEven.SixAgree`), and the parent piece agrees with
each copy on their whole overlap (`AltParentEF1` and the other parent modules). When two of the six copies overlap only as a
doubled pair or as a mixed pair inside the marks of both, the seven pieces agree on every overlap (`JointGlue.PiecesAgree`). -/

namespace FLatticePaper.Tiles.AltPiecesAgree

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.ChildGlue
open FLatticePaper.Tiles.AltSixEven
open FLatticePaper.Tiles.JointGlue (pieceVal PiecesAgree)

/-- The overlaps of two of the six copies: a doubled pair, or a mixed pair inside the marks of both. -/
def SixOverlaps (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop) : Prop :=
  ∀ i j, i < 6 → j < 6 → i < j → ∀ z, z ∈ pieceSet P Q T1 T2 i → z ∈ pieceSet P Q T1 T2 j →
    (pieceFlag P i = pieceFlag P j ∧ Dbl i j) ∨
      (pieceFlag P i ≠ pieceFlag P j ∧ z ∈ pieceSet P Q M1 M2 i ∧ z ∈ pieceSet P Q M1 M2 j)

/-- The constants of the seven pieces: `κ` on the six copies, `K6` on the parent piece. -/
def kappa7 (κ : ℕ → ℤ) (K6 : ℤ) (i : ℕ) : ℤ := if i = 6 then K6 else κ i

/-- **The seven pieces agree.** `ps` has the six copies (placed domains `pieceSet P Q T1 T2 i`, values `f0 i`) and the parent
piece as entry `6`; the copies agree with constants `κ` (`SixAgree`), the parent agrees with each copy with constant `K6`, and the
six copies overlap only as in `SixOverlaps`. -/
theorem sevenAgree_of (ps : List JointFamily.Piece) (P Q : List (ℤ × ℤ)) (T1 T2 M1 M2 : Set (ℤ × ℤ)) (Dbl : ℕ → ℕ → Prop)
    (f0 : ℕ → ℤ × ℤ → ℤ) (κ : ℕ → ℤ) (K6 : ℤ) (hlen : ps.length = 7) (hPQ : P.length + Q.length = 6)
    (hstd : ∀ i < 6, ∀ p, ps[i]? = some p → ∀ z, (z ∈ p.placed ↔ z ∈ pieceSet P Q T1 T2 i) ∧ pieceVal p z = f0 i z)
    (hsix : SixAgree P Q T1 T2 M1 M2 Dbl (fun i z => f0 i z + κ i))
    (hpar : ∀ p, ps[6]? = some p → ∀ j < 6, ∀ z ∈ p.placed, z ∈ pieceSet P Q T1 T2 j → pieceVal p z + K6 = f0 j z + κ j)
    (hov : SixOverlaps P Q T1 T2 M1 M2 Dbl) :
    PiecesAgree ps (kappa7 κ K6) := by
  have key : ∀ i j p q, i < j → ps[i]? = some p → ps[j]? = some q → ∀ x ∈ p.placed, x ∈ q.placed →
      pieceVal p x + kappa7 κ K6 i = pieceVal q x + kappa7 κ K6 j := by
    intro i j p q hij hp hq x hxp hxq
    have hj7 : j < 7 := hlen ▸ (List.getElem?_eq_some_iff.mp hq).1
    by_cases hj6 : j = 6
    · subst hj6
      have hi6 : i < 6 := hij
      have hi := hstd i hi6 p hp x
      have e := hpar q hq i hi6 x hxq (hi.1.mp hxp)
      simp only [kappa7, if_neg (Nat.ne_of_lt hi6)]
      rw [hi.2]
      exact e.symm
    · have hj6' : j < 6 := by omega
      have hi6 : i < 6 := by omega
      have hi := hstd i hi6 p hp x
      have hjj := hstd j hj6' q hq x
      simp only [kappa7, if_neg (Nat.ne_of_lt hi6), if_neg hj6]
      rw [hi.2, hjj.2]
      rcases hov i j hi6 hj6' hij x (hi.1.mp hxp) (hjj.1.mp hxq) with ⟨hf, hd⟩ | ⟨hf, hm1, hm2⟩
      · exact hsix.2 i j (by omega) (by omega) hij hf hd x (hi.1.mp hxp) (hjj.1.mp hxq)
      · exact hsix.1 i j (by omega) (by omega) hf x hm1 hm2
  intro i j p q hp hq x hxp hxq _ _
  rcases lt_trichotomy i j with h | h | h
  · exact key i j p q h hp hq x hxp hxq
  · subst h
    rw [hp] at hq
    cases hq
    rfl
  · exact (key j i q p h hq hp x hxq hxp).symm

/-! ### The entries of the alternate decompositions at an uncorrected child with a parent piece -/

open FLatticePaper.Farey
open FLatticePaper.Tiles.JointFamily (stdPiece tileAltEvenPieces tileAltOddPieces altOff altAff W1Odd)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.SurgicalAlt (altTypeOf altP1Coeff altQ1Coeff)
open FLatticePaper.Tiles.ClosedPathAlt
open FLatticePaper.Tiles.Standard (oddTile evenTile)
open FLatticePaper.Tiles.ClosedPathSum (dot2)

/-- The even alternate decomposition, entry by entry, in the offsets of `ClosedPathAlt`. -/
theorem aEven_list (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (c : SurgicalAlt.AltCoeff)
    (hr : regsAt w = (some u1, some u2)) (h3 : w.getLast? ≠ some Digit.three)
    (hc : (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some c) :
    tileAltEvenPieces S pOdd pEven aOdd aEven lEven w =
      [stdPiece (pEven u2) ((altEvenD w).getD 0 0) ((altEvenAff w).getD 0 0),
        stdPiece (pEven u2) ((altEvenD w).getD 1 0) ((altEvenAff w).getD 1 0),
        stdPiece (pEven u2) ((altEvenD w).getD 2 0) ((altEvenAff w).getD 2 0),
        stdPiece (pEven u2) ((altEvenD w).getD 3 0) ((altEvenAff w).getD 3 0),
        stdPiece (pOdd u1) ((altEvenR w).getD 0 0) ((altEvenAff w).getD 4 0),
        stdPiece (pOdd u1) ((altEvenR w).getD 1 0) ((altEvenAff w).getD 5 0),
        stdPiece (aOdd u1) (altOff w c) (altAff w c)] := by
  unfold tileAltEvenPieces
  simp only [hr, hc, h3, decide_false, Bool.false_eq_true, if_false, SurgicalWeak.regOdo]
  simp [altEvenD, altEvenR, altEvenAff, add_comm, W1Odd, altOff, altAff, JointFamily.vP1, JointFamily.vP2,
    JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

/-- The odd alternate decomposition, entry by entry, in the offsets of `ClosedPathAlt`. -/
theorem aOdd_list (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (c : SurgicalAlt.AltCoeff)
    (hr : regsAt w = (some u1, some u2)) (h2 : w.getLast? ≠ some Digit.two)
    (hc : (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some c) :
    tileAltOddPieces S pOdd pEven aOdd aEven lOdd w =
      [stdPiece (pOdd u1) ((altOddD w).getD 0 0) ((altOddAff w).getD 0 0),
        stdPiece (pOdd u1) ((altOddD w).getD 1 0) ((altOddAff w).getD 1 0),
        stdPiece (pOdd u1) ((altOddD w).getD 2 0) ((altOddAff w).getD 2 0),
        stdPiece (pOdd u1) ((altOddD w).getD 3 0) ((altOddAff w).getD 3 0),
        stdPiece (pEven u2) ((altOddR w).getD 0 0) ((altOddAff w).getD 4 0),
        stdPiece (pEven u2) ((altOddR w).getD 1 0) ((altOddAff w).getD 5 0),
        stdPiece (aEven u2) (altOff w c) (altAff w c)] := by
  unfold tileAltOddPieces
  simp only [hr, hc, h2, decide_false, Bool.false_eq_true, if_false, SurgicalWeak.regOdo]
  simp [altOddD, altOddR, altOddAff, add_comm, W1Odd, altOff, altAff, JointFamily.vP1, JointFamily.vP2,
    JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

theorem mem_placed_std (o : PartialOdometer) (off aff z : Site) :
    z ∈ (stdPiece o off aff).placed ↔ z - off ∈ o.dom := by
  simp only [JointFamily.Piece.placed, stdPiece, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨z - off, h, sub_add_cancel z off⟩

theorem mem_shiftS_iff (T : Set (ℤ × ℤ)) (v z : ℤ × ℤ) : z ∈ shiftS T v ↔ z - v ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨z - v, h, sub_add_cancel z v⟩

/-- The six copies of the even alternate decomposition are the placed copies of `ClosedPathAlt`. -/
theorem aEven_std (w u1 u2 : Word) (oP oQ H : PartialOdometer) (t η : Site)
    (hdP : oP.dom = oddTile u1) (hdQ : oQ.dom = evenTile u2) :
    ∀ i < 6, ∀ p, [stdPiece oQ ((altEvenD w).getD 0 0) ((altEvenAff w).getD 0 0),
        stdPiece oQ ((altEvenD w).getD 1 0) ((altEvenAff w).getD 1 0),
        stdPiece oQ ((altEvenD w).getD 2 0) ((altEvenAff w).getD 2 0),
        stdPiece oQ ((altEvenD w).getD 3 0) ((altEvenAff w).getD 3 0),
        stdPiece oP ((altEvenR w).getD 0 0) ((altEvenAff w).getD 4 0),
        stdPiece oP ((altEvenR w).getD 1 0) ((altEvenAff w).getD 5 0), stdPiece H t η][i]? = some p →
      ∀ z, (z ∈ p.placed ↔ z ∈ pieceSet (altEvenD w) (altEvenR w) (tEvenSet u2) (tOddSet u1) i) ∧
        pieceVal p z = placedAltEven w oP.val oQ.val 0 i z := by
  intro i hi p hp z
  have hl : (altEvenD w).length = 4 := by simp [altEvenD]
  interval_cases i <;> simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp <;> subst hp <;>
    refine ⟨?_, ?_⟩ <;>
    first
    | (rw [mem_placed_std]; simp [mem_shiftS_iff, pieceSet, hl, hdP, hdQ])
    | simp [pieceVal, placedAltEven, dot2, dotS, stdPiece]

/-- The six copies of the odd alternate decomposition are the placed copies of `ClosedPathAlt`. -/
theorem aOdd_std (w u1 u2 : Word) (oP oQ H : PartialOdometer) (t η : Site)
    (hdP : oP.dom = oddTile u1) (hdQ : oQ.dom = evenTile u2) :
    ∀ i < 6, ∀ p, [stdPiece oP ((altOddD w).getD 0 0) ((altOddAff w).getD 0 0),
        stdPiece oP ((altOddD w).getD 1 0) ((altOddAff w).getD 1 0),
        stdPiece oP ((altOddD w).getD 2 0) ((altOddAff w).getD 2 0),
        stdPiece oP ((altOddD w).getD 3 0) ((altOddAff w).getD 3 0),
        stdPiece oQ ((altOddR w).getD 0 0) ((altOddAff w).getD 4 0),
        stdPiece oQ ((altOddR w).getD 1 0) ((altOddAff w).getD 5 0), stdPiece H t η][i]? = some p →
      ∀ z, (z ∈ p.placed ↔ z ∈ pieceSet (altOddD w) (altOddR w) (tOddSet u1) (tEvenSet u2) i) ∧
        pieceVal p z = placedAltOdd w oP.val oQ.val 0 i z := by
  intro i hi p hp z
  have hl : (altOddD w).length = 4 := by simp [altOddD]
  interval_cases i <;> simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp <;> subst hp <;>
    refine ⟨?_, ?_⟩ <;>
    first
    | (rw [mem_placed_std]; simp [mem_shiftS_iff, pieceSet, hl, hdP, hdQ])
    | simp [pieceVal, placedAltOdd, dot2, dotS, stdPiece]

/-- **An odometer respecting a decomposition whose pieces agree with constants `κ`** equals each piece plus `κ` and one global
constant, when every piece meets a fixed piece `p0` outside the exceptional points (for the alternate decompositions, the parent
piece, which meets every copy at a corner contact). -/
theorem respects_explicit (o : PartialOdometer) (ps : List JointFamily.Piece) (κ : ℕ → ℤ) (hR : JointFamily.RespectsPieces o ps)
    (hag : PiecesAgree ps κ) (i0 : ℕ) (p0 : JointFamily.Piece) (hp0 : ps[i0]? = some p0)
    (hmeet : ∀ (i : ℕ) (p : JointFamily.Piece), ps[i]? = some p → ∃ x ∈ p.placed, x ∈ p0.placed ∧ x ∉ p.exc ∧ x ∉ p0.exc) :
    ∃ c : ℤ, ∀ (i : ℕ) (p : JointFamily.Piece), ps[i]? = some p → ∀ x ∈ p.placed, x ∉ p.exc →
      o.val x = pieceVal p x + κ i + c := by
  have hmem : ∀ (i : ℕ) (p : JointFamily.Piece), ps[i]? = some p → p ∈ ps := fun i p h => List.mem_of_getElem? h
  obtain ⟨b0, hb0⟩ := hR.2 p0 (hmem i0 p0 hp0)
  refine ⟨b0 - κ i0, fun i p hp x hx hxe => ?_⟩
  obtain ⟨b, hb⟩ := hR.2 p (hmem i p hp)
  obtain ⟨y, hy, hy0, hye, hy0e⟩ := hmeet i p hp
  have e1 := hb y hy hye
  have e2 := hb0 y hy0 hy0e
  have e3 := hag i i0 p p0 hp hp0 y hy hy0 hye hy0e
  have e4 := hb x hx hxe
  simp only [pieceVal] at e3 ⊢
  linarith

/-- The standard entries `0, 3, 4, 5` of the odd alternate decomposition, corrected or not. -/
theorem aOdd_mem (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2)) :
    stdPiece (pOdd u1) ((altOddD w).getD 0 0) ((altOddAff w).getD 0 0) ∈ tileAltOddPieces S pOdd pEven aOdd aEven lOdd w ∧
    stdPiece (pOdd u1) ((altOddD w).getD 3 0) ((altOddAff w).getD 3 0) ∈ tileAltOddPieces S pOdd pEven aOdd aEven lOdd w ∧
    stdPiece (pEven u2) ((altOddR w).getD 0 0) ((altOddAff w).getD 4 0) ∈ tileAltOddPieces S pOdd pEven aOdd aEven lOdd w ∧
    stdPiece (pEven u2) ((altOddR w).getD 1 0) ((altOddAff w).getD 5 0) ∈ tileAltOddPieces S pOdd pEven aOdd aEven lOdd w := by
  unfold tileAltOddPieces
  simp only [hr, SurgicalWeak.regOdo]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [altOddD, altOddR, altOddAff, add_comm, JointFamily.W1Odd, JointFamily.altOff,
    JointFamily.altAff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

/-- The standard entries `1, 2, 4, 5` of the even alternate decomposition, corrected or not. -/
theorem aEven_mem (S : SurgicalWeak.WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hr : regsAt w = (some u1, some u2)) :
    stdPiece (pEven u2) ((altEvenD w).getD 1 0) ((altEvenAff w).getD 1 0) ∈ tileAltEvenPieces S pOdd pEven aOdd aEven lEven w ∧
    stdPiece (pEven u2) ((altEvenD w).getD 2 0) ((altEvenAff w).getD 2 0) ∈ tileAltEvenPieces S pOdd pEven aOdd aEven lEven w ∧
    stdPiece (pOdd u1) ((altEvenR w).getD 0 0) ((altEvenAff w).getD 4 0) ∈ tileAltEvenPieces S pOdd pEven aOdd aEven lEven w ∧
    stdPiece (pOdd u1) ((altEvenR w).getD 1 0) ((altEvenAff w).getD 5 0) ∈ tileAltEvenPieces S pOdd pEven aOdd aEven lEven w := by
  unfold tileAltEvenPieces
  simp only [hr, SurgicalWeak.regOdo]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [altEvenD, altEvenR, altEvenAff, add_comm, JointFamily.W1Odd, JointFamily.altOff,
    JointFamily.altAff, JointFamily.vP1, JointFamily.vP2, JointFamily.vQ1, JointFamily.vQ2, JointFamily.aP2]

end FLatticePaper.Tiles.AltPiecesAgree
