import FLatticePaper.Tiles.TileHalfTurnL
import FLatticePaper.Tiles.ConnectedL

/-! # The triangle of an L-corrected decomposition is a translate of three pieces of the alternate decomposition of the prefix

For `w = pre 2^k` with `pre` not a base word, the last stem `S_k`, the bridge `B` and the first head `H_0` of `oddLPieces` at `w`
are the pieces `T(q₁)^∓`, `T(p₁)^{±,·}` and the alternate parent piece of `tileAltOddPieces` at `pre` (slots `5, 1, 6` for `-`,
`4, 2, 6` for `+`), placed at the offset translated by one vector `t` and with the affine factor increased by one vector `Δa`
(`odd_triangle`). The same holds for `evenLPieces` at `w = pre 3^k` and `tileAltEvenPieces` at `pre` (slots `5, 3, 6` and
`4, 0, 6`, `even_triangle`). In both cases the offsets are linear in the coefficient vectors at `pre`, and the coefficient of
the bridge (head) slot minus that of the stem slot is `K₂` (`K₂ + K₃ + K₄`). -/

namespace FLatticePaper.Tiles.LTriangle

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.SurgicalWeak (regOdo regsAt WeakData)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.ConnectedAltL (oStemPos oHeadPos eStemPos eHeadPos)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos oAffAt oStemC oBridgeC oHeadC eBridgePos eAffAt eStemC eBridgeC eHeadC)

/-- A piece moved by `t`, with its affine factor increased by `Δa`. -/
def mv (t da : Site) (q : Piece) : Piece := { q with off := q.off + t, aff := q.aff + da }

theorem strip_last (d : Digit) : ∀ (u : Word) (e : Digit), (stripTrailing d u).getLast? = some e → e ≠ d := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro e h; simp [stripTrailing, trailingCount] at h
  | append_singleton v x ih =>
    intro e h
    rw [JointRot.stripTrailing_snoc] at h
    split_ifs at h with hx
    · exact ih e h
    · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
      rw [← h]; exact hx

theorem not_all (pre : Word) (hpre : ¬ IsBase pre) (d : Digit) (hd : d = Digit.three ∨ d = Digit.two) :
    (!pre.isEmpty && pre.all (fun x => decide (x = d))) = false := by
  rcases hb : pre.all (fun x => decide (x = d)) with _ | _
  · simp
  · exfalso
    apply hpre
    have h : ∀ x ∈ pre, x = d := fun x hx => by simpa using List.all_eq_true.1 hb x hx
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem last_of_not_base (d : Digit) (w : Word) (hpre : ¬ IsBase (stripTrailing d w)) :
    ∃ s : Digit, s ≠ d ∧ (stripTrailing d w).getLast? = some s := by
  have hne : stripTrailing d w ≠ [] := fun h => hpre (Or.inl h)
  obtain ⟨s, hs⟩ : ∃ s, (stripTrailing d w).getLast? = some s := by
    rcases h : (stripTrailing d w).getLast? with _ | s
    · rw [List.getLast?_eq_none_iff] at h; exact absurd h hne
    · exact ⟨s, rfl⟩
  exact ⟨s, strip_last d w s hs, hs⟩

theorem range_map_get {α : Type*} (f : ℕ → α) (n i : ℕ) (h : i < n) : ((List.range n).map f)[i]? = some (f i) := by
  rw [List.getElem?_map, List.getElem?_range h]; rfl

set_option maxHeartbeats 400000 in
/-- **The triangle of the odd L-correction.** -/
theorem odd_triangle (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (w : Word) (plus elong : Bool) (hpre : ¬ IsBase (stripTrailing Digit.two w)) :
    ∃ t da : Site,
      (oddLPieces S pO pE aO aE w plus elong)[trailingCount Digit.two w]? =
          ((tileAltOddPieces S pO pE aO aE lO (stripTrailing Digit.two w))[if plus then 4 else 5]?).map (mv t da) ∧
        (oddLPieces S pO pE aO aE w plus elong)[trailingCount Digit.two w + 1]? =
          ((tileAltOddPieces S pO pE aO aE lO (stripTrailing Digit.two w))[if plus then 2 else 1]?).map (mv t da) ∧
        (oddLPieces S pO pE aO aE w plus elong)[trailingCount Digit.two w + 2]? =
          ((tileAltOddPieces S pO pE aO aE lO (stripTrailing Digit.two w))[6]?).map (mv t da) := by
  have hreg := not_all _ hpre Digit.three (Or.inl rfl)
  obtain ⟨s, hs2, hs⟩ := last_of_not_base Digit.two w hpre
  have hW : W1Odd w = W1Odd (stripTrailing Digit.two w) := (ConnectedL.W1Odd_strip_two w).symm
  have hc : decide ((stripTrailing Digit.two w).getLast? = some Digit.two) = false := by
    rw [hs]; simpa using hs2
  have hty : (SurgicalAlt.altTypeOf (stripTrailing Digit.two w)).bind
      (fun ty => SurgicalAlt.altQ1Coeff (W1Odd (stripTrailing Digit.two w)) ty) =
      some (if W1Odd (stripTrailing Digit.two w) then (1, 1, -1, 0) else (0, 1, 1, 0)) := by
    simp only [SurgicalAlt.altTypeOf, hs, Option.bind_some, SurgicalAlt.altQ1Coeff, if_neg hs2]
    split_ifs <;> rfl
  rw [TileHalfTurnL.oLP_eq S pO pE aO aE w plus elong hreg]
  have hl : ((List.range (trailingCount Digit.two w + 1)).map (fun j =>
      stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.two w)).2 false) (oStemPos w plus j)
        (oAffAt w plus (oStemC w plus j)))).length = trailingCount Digit.two w + 1 := by simp
  have hnh : 0 < 2 * (trailingCount Digit.two w + 1) - (if elong then 0 else 1) := by split_ifs <;> omega
  refine ⟨oStemPos w plus (trailingCount Digit.two w) -
      altOff (stripTrailing Digit.two w) (SurgicalAlt.altP0Coeff (W1Odd (stripTrailing Digit.two w)) (if plus then .q1Plus else .q1Minus)),
    oAffAt w plus (oStemC w plus (trailingCount Digit.two w)) -
      altAff (stripTrailing Digit.two w) (SurgicalAlt.altP0Coeff (W1Odd (stripTrailing Digit.two w)) (if plus then .q1Plus else .q1Minus)),
    ?_, ?_, ?_⟩
  · rw [TileHalfTurnL.get_left _ _ _ _ (by rw [hl]; omega), range_map_get _ _ _ (by omega)]
    simp only [tileAltOddPieces, hc, hty]
    cases plus <;> simp [mv, stdPiece]
  · rw [TileHalfTurnL.get_mid _ _ _ hl]
    simp only [tileAltOddPieces, hc, hty]
    cases plus <;> simp only [mv, stdPiece, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, List.cons_append, Option.some.injEq, Piece.mk.injEq, true_and, and_true] <;>
      refine ⟨?_, ?_⟩ <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.two w)) with h | h <;>
      simp only [oBridgePos, oStemPos, oAffAt, oStemC, oBridgeC, hW, h, oddKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
        SurgicalAlt.altP0Coeff, SurgicalDict.altShifts, aP2, offsetA, vP1, vP2, vQ1, vQ2, if_true, if_false, Bool.false_eq_true] <;>
      ext <;> simp <;> ring
  · rw [show trailingCount Digit.two w + 2 = trailingCount Digit.two w + 1 + 1 + 0 from rfl,
      TileHalfTurnL.get_right _ _ _ hl, range_map_get _ _ _ hnh]
    simp only [tileAltOddPieces, hc, hty]
    cases plus <;> simp only [mv, stdPiece, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, List.cons_append, List.nil_append, Option.some.injEq, Piece.mk.injEq,
      true_and, and_true] <;>
      refine ⟨?_, ?_⟩ <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.two w)) with h | h <;>
      simp only [oHeadPos, oStemPos, oAffAt, oStemC, oHeadC, hW, h, oddKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
        SurgicalAlt.altP0Coeff, vP1, vP2, vQ1, vQ2, if_true, if_false, Bool.false_eq_true] <;>
      ext <;> simp <;> ring

set_option maxHeartbeats 400000 in
/-- **The triangle of the even L-correction.** -/
theorem even_triangle (S : WeakData) (pO pE aO aE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (w : Word) (plus elong : Bool) (hpre : ¬ IsBase (stripTrailing Digit.three w)) :
    ∃ t da : Site,
      (evenLPieces S pO pE aO aE w plus elong)[trailingCount Digit.three w]? =
          ((tileAltEvenPieces S pO pE aO aE lE (stripTrailing Digit.three w))[if plus then 4 else 5]?).map (mv t da) ∧
        (evenLPieces S pO pE aO aE w plus elong)[trailingCount Digit.three w + 1]? =
          ((tileAltEvenPieces S pO pE aO aE lE (stripTrailing Digit.three w))[if plus then 0 else 3]?).map (mv t da) ∧
        (evenLPieces S pO pE aO aE w plus elong)[trailingCount Digit.three w + 2]? =
          ((tileAltEvenPieces S pO pE aO aE lE (stripTrailing Digit.three w))[6]?).map (mv t da) := by
  have hreg := not_all _ hpre Digit.two (Or.inr rfl)
  obtain ⟨s, hs3, hs⟩ := last_of_not_base Digit.three w hpre
  have hW : W1Odd w = W1Odd (stripTrailing Digit.three w) := (ConnectedL.W1Odd_strip_three w).symm
  have hc : decide ((stripTrailing Digit.three w).getLast? = some Digit.three) = false := by
    rw [hs]; simpa using hs3
  have hty : (SurgicalAlt.altTypeOf (stripTrailing Digit.three w)).bind
      (fun ty => SurgicalAlt.altP1Coeff (W1Odd (stripTrailing Digit.three w)) ty) =
      SurgicalAlt.altP1Coeff (W1Odd (stripTrailing Digit.three w)) s := by
    simp only [SurgicalAlt.altTypeOf, hs, Option.bind_some]
  have hs2 : decide ((stripTrailing Digit.three w).getLast? = some Digit.two) = decide (s = Digit.two) := by
    rw [hs]; simp
  rw [TileHalfTurnL.eLP_eq S pO pE aO aE w plus elong hreg]
  have hl : ((List.range (trailingCount Digit.three w + 1)).map (fun j =>
      stdPiece (regOdo S pO pE (regsAt (stripTrailing Digit.three w)).1 true) (eStemPos w plus j)
        (eAffAt w plus (eStemC w plus j)))).length = trailingCount Digit.three w + 1 := by simp
  have hnh : 0 < 2 * (trailingCount Digit.three w + 1) - (if elong then 0 else 1) := by split_ifs <;> omega
  refine ⟨eStemPos w plus (trailingCount Digit.three w) -
      altOff (stripTrailing Digit.three w) (SurgicalAlt.altQ0Coeff (W1Odd (stripTrailing Digit.three w)) (if plus then .p1Plus else .p1Minus)),
    eAffAt w plus (eStemC w plus (trailingCount Digit.three w)) -
      altAff (stripTrailing Digit.three w) (SurgicalAlt.altQ0Coeff (W1Odd (stripTrailing Digit.three w)) (if plus then .p1Plus else .p1Minus)),
    ?_, ?_, ?_⟩
  · rw [TileHalfTurnL.get_left _ _ _ _ (by rw [hl]; omega), range_map_get _ _ _ (by omega)]
    simp only [tileAltEvenPieces, hc, hty]
    cases plus <;> cases s <;> simp [mv, stdPiece, SurgicalAlt.altP1Coeff]
  · rw [TileHalfTurnL.get_mid _ _ _ hl]
    simp only [tileAltEvenPieces, hc, hty]
    cases s
    · cases plus <;> simp only [mv, stdPiece, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, List.cons_append, Option.some.injEq, Piece.mk.injEq, true_and,
        and_true] <;>
        refine ⟨?_, ?_⟩ <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.three w)) with h | h <;>
        simp only [eBridgePos, eStemPos, eAffAt, eStemC, eBridgeC, hW, h, hs2, evenKCoeff, altOff, altAff,
          SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, aP2, offsetA, vP1, vP2,
          vQ1, vQ2, if_true, if_false, Bool.false_eq_true] <;>
        ext <;> simp <;> ring
    · cases plus <;> simp only [mv, stdPiece, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, List.cons_append, Option.some.injEq, Piece.mk.injEq, true_and,
        and_true] <;>
        refine ⟨?_, ?_⟩ <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.three w)) with h | h <;>
        simp only [eBridgePos, eStemPos, eAffAt, eStemC, eBridgeC, hW, h, hs2, evenKCoeff, altOff, altAff,
          SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, SurgicalDict.altShifts, aP2, offsetA, vP1, vP2,
          vQ1, vQ2, if_true, if_false, Bool.false_eq_true, decide_true] <;>
        ext <;> simp <;> ring
    · exact absurd rfl hs3
  · rw [show trailingCount Digit.three w + 2 = trailingCount Digit.three w + 1 + 1 + 0 from rfl,
      TileHalfTurnL.get_right _ _ _ hl, range_map_get _ _ _ hnh]
    simp only [tileAltEvenPieces, hc, hty]
    cases s
    · cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.three w)) with h | h <;>
        simp only [mv, stdPiece, SurgicalAlt.altP1Coeff, h, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.map_some, List.cons_append, List.nil_append, Option.some.injEq, Piece.mk.injEq,
          true_and, and_true, reduceCtorEq] <;>
        refine ⟨?_, ?_⟩ <;>
        simp only [eHeadPos, eStemPos, eAffAt, eStemC, eHeadC, hW, h, hs2, evenKCoeff, altOff, altAff,
          SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, vP1, vP2, vQ1, vQ2, if_true,
          if_false, Bool.false_eq_true, decide_false, reduceCtorEq] <;>
        ext <;> simp <;> ring
    · cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd (stripTrailing Digit.three w)) with h | h <;>
        simp only [mv, stdPiece, SurgicalAlt.altP1Coeff, h, if_true, if_false, Bool.false_eq_true, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.map_some, List.cons_append, List.nil_append, Option.some.injEq, Piece.mk.injEq,
          true_and, and_true, reduceCtorEq] <;>
        refine ⟨?_, ?_⟩ <;>
        simp only [eHeadPos, eStemPos, eAffAt, eStemC, eHeadC, hW, h, hs2, evenKCoeff, altOff, altAff,
          SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, SurgicalAlt.altQ0Coeff, vP1, vP2, vQ1, vQ2, if_true,
          if_false, Bool.false_eq_true, decide_true] <;>
        ext <;> simp <;> ring
    · exact absurd rfl hs3

/-! ### Consecutive stems and heads -/

/-- Consecutive heads of the odd L-correction are translates by `∓v_{q,1}` (`q` the even parent of the prefix, the fraction of the
alternate head register), with the same affine factor. -/
theorem odd_head_step (w : Word) (plus : Bool) (i : ℕ) :
    oHeadPos w plus (i + 1) = oHeadPos w plus i + (if W1Odd w == plus then -vQ1 (stripTrailing Digit.two w) else
      vQ1 (stripTrailing Digit.two w)) ∧
      oAffAt w plus (oHeadC w plus (i + 1)) = oAffAt w plus (oHeadC w plus i) := by
  constructor <;> cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    simp only [oHeadPos, oAffAt, oHeadC, h, oddKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
      vQ1, beq_self_eq_true, if_true, if_false, Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.false_eq_true] <;>
    ext <;> simp <;> ring

/-- Consecutive stems of the odd L-correction are translates by `±v_{q,2}` with the affine factor changed by `±a_{q,2}`. -/
theorem odd_stem_step (w : Word) (plus : Bool) (j : ℕ) :
    oStemPos w plus (j + 1) = oStemPos w plus j + (if plus then vQ2 (stripTrailing Digit.two w) else
      -vQ2 (stripTrailing Digit.two w)) ∧
      oAffAt w plus (oStemC w plus (j + 1)) = oAffAt w plus (oStemC w plus j) + (if plus then aQ2 (stripTrailing Digit.two w) else
        -aQ2 (stripTrailing Digit.two w)) := by
  constructor <;> cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    simp only [oStemPos, oAffAt, oStemC, h, oddKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
      vQ2, aQ2, offsetA, if_true, if_false, Bool.false_eq_true] <;>
    ext <;> simp <;> ring

/-- Consecutive heads of the even L-correction are translates by `±v_{p,2}` (`p` the odd parent of the prefix, the fraction of
the alternate head register), with the affine factor changed by `±a_{p,2}`. -/
theorem even_head_step (w : Word) (plus : Bool) (i : ℕ) :
    eHeadPos w plus (i + 1) = eHeadPos w plus i + (if plus then vP2 (stripTrailing Digit.three w) else
      -vP2 (stripTrailing Digit.three w)) ∧
      eAffAt w plus (eHeadC w plus (i + 1)) = eAffAt w plus (eHeadC w plus i) + (if plus then aP2 (stripTrailing Digit.three w) else
        -aP2 (stripTrailing Digit.three w)) := by
  constructor <;> cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    rcases Bool.eq_false_or_eq_true (decide ((stripTrailing Digit.three w).getLast? = some Digit.two)) with h2 | h2 <;>
    simp only [eHeadPos, eAffAt, eHeadC, h, h2, evenKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
      vP2, aP2, offsetA, if_true, if_false, Bool.false_eq_true] <;>
    ext <;> simp <;> ring

/-- Consecutive stems of the even L-correction are translates by `±v_{p,1}`, with the same affine factor. -/
theorem even_stem_step (w : Word) (plus : Bool) (j : ℕ) :
    eStemPos w plus (j + 1) = eStemPos w plus j + (if W1Odd w == plus then vP1 (stripTrailing Digit.three w) else
      -vP1 (stripTrailing Digit.three w)) ∧
      eAffAt w plus (eStemC w plus (j + 1)) = eAffAt w plus (eStemC w plus j) := by
  constructor <;> cases plus <;> rcases Bool.eq_false_or_eq_true (W1Odd w) with h | h <;>
    rcases Bool.eq_false_or_eq_true (decide ((stripTrailing Digit.three w).getLast? = some Digit.two)) with h2 | h2 <;>
    simp only [eStemPos, eAffAt, eStemC, h, h2, evenKCoeff, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine,
      vP1, beq_self_eq_true, if_true, if_false, Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.false_eq_true] <;>
    ext <;> simp <;> ring

end FLatticePaper.Tiles.LTriangle
