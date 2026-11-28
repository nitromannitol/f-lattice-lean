import FLatticePaper.Tiles.WeakStepPaper
import FLatticePaper.Tiles.CorrectedCellsOrdinary
import FLatticePaper.Tiles.JointGlue

/-! # The alternate nodes from the full alternate decompositions

At an alternate child that is not corrected, an odometer that respects the full alternate decomposition (`tileAltOddPieces`,
`tileAltEvenPieces`) satisfies the alternate node (`AltOddNodeP`, `AltEvenNodeP`): each shifted doubling of a register is the
register on its first copy and its translate by the shift (with the affine factor `a_{p_1,2}` and the constant read off the two
copies) on the second, and the plain copies and the alternate parent piece are placed with their constants. The pieces cover the
alternate tile (`altOdd_union`, `altEven_union`). -/

namespace FLatticePaper.Tiles.WeakAltNode

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase oddTile evenTile stateAt shift)
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.WeakStepPaper (dblPieceA dblSecondA dblA_on dblA_respects side_inside)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile altRegs)

/-! ### Pieces, doublings and placements -/

/-- A standard piece of a decomposition that an odometer respects: its placed copy lies in the domain, with the piece's value
plus one constant. -/
theorem std_at {o : PartialOdometer} {ps : List Piece} {P : PartialOdometer} {off aff : Site} (hR : RespectsPieces o ps)
    (hp : stdPiece P off aff ∈ ps) :
    ∃ b : ℤ, ∀ x ∈ P.dom.image (· + off), x ∈ o.dom ∧ o.val x = P.val (x - off) + dotS aff x + b := by
  obtain ⟨b, hb⟩ := hR.2 _ hp
  refine ⟨b, fun x hx => ⟨?_, hb x hx (by simp [stdPiece])⟩⟩
  rw [hR.1]
  exact JointGlue.mem_pieceUnion.2 ⟨_, hp, hx⟩

/-- The respect of the tile translations on the whole side string gives it on the meeting tiles. -/
theorem meeting_of_side {n d : ℤ} {i : Bool} {wh wv : BinaryWord} {s : Side} {v : Site} {o ostar : PartialOdometer}
    (h : DoublingRespect.RespectsSideTranslation n d i wh wv s v o ostar) :
    DoublingRespect.RespectsMeeting n d i wh wv s v o ostar :=
  fun t ht _ => ⟨(h t ht).1, (h t ht).2.2⟩

/-- The alternate doubling with the partial tile on the second copy, from the agreement of the two copies on their overlap. -/
theorem dblAlt_false (s : Side) (n d : ℤ) (i : Bool) (wh wv : BinaryWord) (P : PartialOdometer) (v : Site) (k : ℤ)
    (hcons : ∀ y ∈ P.dom, y - v ∈ P.dom →
      P.val y = P.val (y - v) + ((offsetA n d i).1 * y.1 + (offsetA n d i).2 * y.2) + k)
    (hin : ∀ t ∈ sideString wh wv (0, 0) s, ∀ x ∈ tileShape t.1, x + t.2 ∈ P.dom) :
    IsWeakDoublingAlt false s n d i wh wv P.dom P.dom v P (dblPieceA P v (offsetA n d i) k) := by
  refine ⟨dblSecondA P v (offsetA n d i) k, ?_⟩
  rw [if_neg Bool.false_ne_true]
  exact ⟨dblA_on P v (offsetA n d i) k hcons, meeting_of_side (dblA_respects n d i wh wv s P v k hin)⟩

/-- The alternate doubling with the partial tile on the first copy. -/
theorem dblAlt_true (s : Side) (n d : ℤ) (i : Bool) (wh wv : BinaryWord) (P : PartialOdometer) (v : Site) (k : ℤ)
    (hcons : ∀ y ∈ P.dom, y - v ∈ P.dom →
      P.val y = P.val (y - v) + ((offsetA n d i).1 * y.1 + (offsetA n d i).2 * y.2) + k)
    (hin : ∀ t ∈ sideString wh wv (0, 0) s, ∀ x ∈ tileShape t.1, x + t.2 ∈ P.dom) :
    IsWeakDoublingAlt true s n d i wh wv P.dom P.dom v P (dblPieceA P v (offsetA n d i) k) := by
  refine ⟨P, ?_⟩
  rw [if_pos rfl]
  exact ⟨dblSecondA P v (offsetA n d i) k, k, rfl, ⟨rfl, fun x _ => rfl⟩, dblA_on P v (offsetA n d i) k hcons,
    meeting_of_side (dblA_respects n d i wh wv s P v k hin)⟩

/-- **The two copies of a shifted doubling.** If an odometer equals the register `P` on the copy at `oA` and its translate on the
copy at `oA + v` (affine factor `aA`, resp. `aA + a2`, constants `κ0`, `κ1`), then the register agrees with its translate by `v`
on their overlap, with the constant `κ1 - κ0 + a2^T oA`, and the odometer is the doubled piece placed at `oA` on both copies. -/
theorem dbl_of_copies (child P : PartialOdometer) (oA aA v a2 : Site) (κ0 κ1 : ℤ)
    (h0 : ∀ x ∈ P.dom.image (· + oA), x ∈ child.dom ∧ child.val x = P.val (x - oA) + dotS aA x + κ0)
    (h1 : ∀ x ∈ P.dom.image (· + (oA + v)), x ∈ child.dom ∧
      child.val x = P.val (x - (oA + v)) + dotS (aA + a2) x + κ1) :
    (∀ y ∈ P.dom, y - v ∈ P.dom →
      P.val y = P.val (y - v) + (a2.1 * y.1 + a2.2 * y.2) + (κ1 - κ0 + dotS a2 oA)) ∧
    ∀ K : Set Site, K ⊆ (↑(P.dom.image (· + oA)) : Set Site) ∪ ↑(P.dom.image (· + (v + oA))) →
      PlacedOn child (dblPieceA P v a2 (κ1 - κ0 + dotS a2 oA)) K oA aA := by
  constructor
  · intro y hy hyv
    have e0 := (h0 (y + oA) (Finset.mem_image.2 ⟨y, hy, rfl⟩)).2
    have e1 := (h1 (y + oA) (Finset.mem_image.2 ⟨y - v, hyv, by abel⟩)).2
    have hs : y + oA - (oA + v) = y - v := by abel
    rw [hs] at e1
    rw [add_sub_cancel_right] at e0
    simp only [dotS, Prod.fst_add, Prod.snd_add] at e0 e1 ⊢
    linarith
  · intro K hK
    refine ⟨κ0, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hK hx with h | h
      · exact (h0 x (Finset.mem_coe.1 h)).1
      · exact (h1 x (by rw [add_comm oA v]; exact Finset.mem_coe.1 h)).1
    · rcases hK hx with h | h
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h)
        rw [(h0 _ (Finset.mem_coe.1 h)).2, add_sub_cancel_right]
        simp only [dblPieceA, hy, if_true, dotS]
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h)
        have hs : y + (v + oA) - oA = y + v := by abel
        rw [hs]
        by_cases hm : y + v ∈ P.dom
        · have hx0 : y + (v + oA) ∈ P.dom.image (· + oA) := Finset.mem_image.2 ⟨y + v, hm, by abel⟩
          rw [(h0 _ hx0).2, hs]
          simp only [dblPieceA, hm, if_true, dotS]
        · have hx1 : y + (v + oA) ∈ P.dom.image (· + (oA + v)) := Finset.mem_image.2 ⟨y, hy, by abel⟩
          have hs1 : y + (v + oA) - (oA + v) = y := by abel
          rw [(h1 _ hx1).2, hs1]
          simp only [dblPieceA, hm, if_false, add_sub_cancel_right, dotS, Prod.fst_add, Prod.snd_add]
          ring

/-- A plain copy placed on a subset of it. -/
theorem placed_of_copy (child Q : PartialOdometer) (oC aC : Site) (κ : ℤ)
    (h : ∀ x ∈ Q.dom.image (· + oC), x ∈ child.dom ∧ child.val x = Q.val (x - oC) + dotS aC x + κ)
    (K : Set Site) (hK : K ⊆ ↑(Q.dom.image (· + oC))) : PlacedOn child Q K oC aC :=
  ⟨κ, fun x hx => (h x (Finset.mem_coe.1 (hK hx))).1, fun x hx => by
    rw [(h x (Finset.mem_coe.1 (hK hx))).2]; rfl⟩

/-- A whole copy placed. -/
theorem placedPiece_of_copy (child Q : PartialOdometer) (oC aC : Site) (κ : ℤ)
    (h : ∀ x ∈ Q.dom.image (· + oC), x ∈ child.dom ∧ child.val x = Q.val (x - oC) + dotS aC x + κ) :
    PlacedPiece child Q oC aC :=
  ⟨κ, fun x hx => (h x hx).1, fun x hx => by rw [(h x hx).2]; rfl⟩

/-! ### The alternate registers -/

/-- The alternate registers of a word are the alternate tiles of its registers. -/
theorem altRegs_regs (base : Word → Standard.Tile × Standard.Tile) (w : Word) :
    (∀ u, (regsAt w).1 = some u → (altRegs base w).1 = altOddTile base u) ∧
      (∀ u, (regsAt w).2 = some u → (altRegs base w).2 = altEvenTile base u) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun u h => by simp [regsAt, regRun] at h, fun u h => by simp [regsAt, regRun] at h⟩
  | append_singleton v d ih =>
    rw [WeakStepPaper.regsAt_snoc, AltRotStep.altRegs_snoc]
    cases d
    · exact ⟨fun u h => by cases h; rfl, fun u h => by cases h; rfl⟩
    · exact ⟨fun u h => by cases h; rfl, ih.2⟩
    · exact ⟨ih.1, fun u h => by cases h; rfl⟩

/-! ### The pieces cover the alternate tile -/

private theorem placed_std' (o : PartialOdometer) (v a : Site) : (stdPiece o v a).placed = shift o.dom v := rfl

private theorem piece_cons' (p : Piece) (ps : List Piece) : pieceUnion (p :: ps) = p.placed ∪ pieceUnion ps := rfl

private theorem shift_double' (T : Standard.Tile) (s v : Site) : shift (doubled T s) v = shift T v ∪ shift T (v + s) := by
  rw [doubled, Standard.shift_union, Standard.shift_shift, add_comm s v]

/-- At a word that is not a base word and does not end in `2`, the pieces of the full odd alternate decomposition cover the odd
alternate tile, when the registers carry the standard tiles and the even alternate register the even alternate tile. -/
theorem altOdd_union (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : w.getLast? ≠ some Digit.two)
    (hP : (pOdd u1).dom = oddTile u1) (hQ : (pEven u2).dom = evenTile u2)
    (hQh : (aEven u2).dom = altEvenTile PaperAltBase.paperAltBaseTiles u2) :
    pieceUnion (tileAltOddPieces S pOdd pEven aOdd aEven lOdd w) = altOddTile PaperAltBase.paperAltBaseTiles w := by
  obtain ⟨hr1, -, hr3, -⟩ := WeakStepPaper.regsAt_tiles w
  have hT1 : (stateAt w).tOdd = oddTile u1 := hr1 u1 (by rw [hreg])
  have hT2 : (stateAt w).tEven = evenTile u2 := hr3 u2 (by rw [hreg])
  have hA2 : (altRegs PaperAltBase.paperAltBaseTiles w).2 = altEvenTile PaperAltBase.paperAltBaseTiles u2 :=
    (altRegs_regs _ w).2 u2 (by rw [hreg])
  rw [AltRotStep.altOddTile_of_not_base _ hw]
  simp only [tileAltOddPieces, hc, decide_false, Bool.false_eq_true, if_false, List.cons_append,
    List.nil_append, piece_cons', placed_std', hreg, regOdo, hP, hQ]
  simp only [SurgicalAltTiles.altOddPieces, shift_double', W1Odd, altOff, vP1, vP2, vQ1, vQ2, hT1, hT2, hA2]
  cases h : altTypeOf w with
  | none =>
    simp only [Option.bind_none, show pieceUnion [] = ∅ from rfl, Finset.union_empty]
    ac_rfl
  | some t =>
    simp only [Option.bind_some]
    cases hk : altQ1Coeff (phase w == 1) t <;>
      simp only [piece_cons', placed_std', show pieceUnion [] = ∅ from rfl, Finset.union_empty, hQh] <;>
      ac_rfl

/-- At a word that is not a base word and does not end in `3`, the pieces of the full even alternate decomposition cover the even
alternate tile. -/
theorem altEven_union (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hw : ¬ IsBase w)
    (hreg : regsAt w = (some u1, some u2)) (hc : w.getLast? ≠ some Digit.three)
    (hP : (pOdd u1).dom = oddTile u1) (hQ : (pEven u2).dom = evenTile u2)
    (hPh : (aOdd u1).dom = altOddTile PaperAltBase.paperAltBaseTiles u1) :
    pieceUnion (tileAltEvenPieces S pOdd pEven aOdd aEven lEven w) = altEvenTile PaperAltBase.paperAltBaseTiles w := by
  obtain ⟨hr1, -, hr3, -⟩ := WeakStepPaper.regsAt_tiles w
  have hT1 : (stateAt w).tOdd = oddTile u1 := hr1 u1 (by rw [hreg])
  have hT2 : (stateAt w).tEven = evenTile u2 := hr3 u2 (by rw [hreg])
  have hA1 : (altRegs PaperAltBase.paperAltBaseTiles w).1 = altOddTile PaperAltBase.paperAltBaseTiles u1 :=
    (altRegs_regs _ w).1 u1 (by rw [hreg])
  rw [AltRotStep.altEvenTile_of_not_base _ hw]
  simp only [tileAltEvenPieces, hc, decide_false, Bool.false_eq_true, if_false, List.cons_append,
    List.nil_append, piece_cons', placed_std', hreg, regOdo, hP, hQ]
  simp only [SurgicalAltTiles.altEvenPieces, shift_double', W1Odd, altOff, vP1, vP2, vQ1, vQ2, hT1, hT2, hA1]
  cases h : altTypeOf w with
  | none =>
    simp only [Option.bind_none, show pieceUnion [] = ∅ from rfl, Finset.union_empty]
    ac_rfl
  | some t =>
    simp only [Option.bind_some]
    cases hk : altP1Coeff (phase w == 1) t <;>
      simp only [piece_cons', placed_std', show pieceUnion [] = ∅ from rfl, Finset.union_empty, hPh] <;>
      ac_rfl

/-! ### The nodes -/

/-- **The odd alternate node from the full decomposition**: at a word that does not end in `2`, an odometer that respects the full
odd alternate decomposition satisfies `AltOddNodeP`, when the odd register lies on the boundary tile and respects its boundary
strings. -/
theorem altOddNode_of_respects (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2))
    (hc : w.getLast? ≠ some Digit.two) (o : PartialOdometer)
    (hR : RespectsPieces o (tileAltOddPieces S pOdd pEven aOdd aEven lOdd w))
    (hb : S.bdry (some u1) true = (pOdd u1).dom)
    (hRP : RespectsAnchored (pOdd u1).dom (hWordOf u1 false) (vWordOf u1 false) (pOdd u1).val) :
    AltOddNodeP S o pOdd pEven aOdd aEven w := by
  have hty : (altTypeOf w == some Digit.two) = false := by simp [altTypeOf, hc]
  have hL : tileAltOddPieces S pOdd pEven aOdd aEven lOdd w =
      [stdPiece (pOdd u1) (altOff w (altP0Coeff (W1Odd w) .dsP1Plus)) (altAff w (altP0Coeff (W1Odd w) .dsP1Plus)),
        stdPiece (pOdd u1) (altOff w (altP0Coeff (W1Odd w) .dsP1Plus) + (altShifts (W1Odd w) (vP2 w) (vQ1 w)).1)
          (altAff w (altP0Coeff (W1Odd w) .dsP1Plus) + aP2 w),
        stdPiece (pOdd u1) (altOff w (altP0Coeff (W1Odd w) .dsP1Minus)) (altAff w (altP0Coeff (W1Odd w) .dsP1Minus)),
        stdPiece (pOdd u1) (altOff w (altP0Coeff (W1Odd w) .dsP1Minus) + (altShifts (W1Odd w) (vP2 w) (vQ1 w)).1)
          (altAff w (altP0Coeff (W1Odd w) .dsP1Minus) + aP2 w),
        stdPiece (pEven u2) (altOff w (altP0Coeff (W1Odd w) .q1Plus)) (altAff w (altP0Coeff (W1Odd w) .q1Plus)),
        stdPiece (pEven u2) (altOff w (altP0Coeff (W1Odd w) .q1Minus)) (altAff w (altP0Coeff (W1Odd w) .q1Minus))] ++
      (match (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) with
        | none => []
        | some c => [stdPiece (aEven u2) (altOff w c) (altAff w c)]) := by
    simp only [tileAltOddPieces, hc, decide_false, Bool.false_eq_true, if_false, hreg, regOdo]
    rfl
  rw [hL] at hR
  have h6 : ∀ c, (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) = some c →
      ∃ κ : ℤ, ∀ x ∈ (aEven u2).dom.image (· + altOff w c), x ∈ o.dom ∧
        o.val x = (aEven u2).val (x - altOff w c) + dotS (altAff w c) x + κ := by
    intro c hcq
    rw [hcq] at hR
    exact std_at hR (List.mem_append_right _ (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨κ0, h0⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨κ1, h1⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  obtain ⟨κ2, h2⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inl rfl)))))))
  obtain ⟨κ3, h3⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))
  obtain ⟨κ4, h4⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))))
  obtain ⟨κ5, h5⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))))))
  simp only [altOff, altAff, W1Odd, vP1, vP2, vQ1, vQ2, aP2] at h0 h1 h2 h3 h4 h5
  obtain ⟨hcP, hplP⟩ := dbl_of_copies o (pOdd u1) _ _ _ _ κ0 κ1 h0 h1
  obtain ⟨hcM, hplM⟩ := dbl_of_copies o (pOdd u1) _ _ _ _ κ2 κ3 h2 h3
  have hin := side_inside _ _ _ _ hRP
  unfold AltOddNodeP
  simp only [hreg, regOdo, hty, altPartial, Bool.false_eq_true, if_false, hb, DoublingRespect.regWords, Bool.not_true]
  refine ⟨_, _, dblAlt_false _ _ _ _ _ _ _ _ _ hcP (hin _), dblAlt_true _ _ _ _ _ _ _ _ _ hcM (hin _),
    hplP _ (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)),
    hplM _ (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)),
    placed_of_copy o (pEven u2) _ _ κ4 h4 _ (fun x hx => hx.1),
    placed_of_copy o (pEven u2) _ _ κ5 h5 _ (fun x hx => hx.1), ?_⟩
  cases ht : altTypeOf w with
  | none => trivial
  | some ty =>
    dsimp only
    cases hq : altQ1Coeff (phase w == 1) ty with
    | none => exact trivial
    | some c =>
      obtain ⟨κ6, hk6⟩ := h6 c (by simp only [ht, Option.bind_some, W1Odd]; exact hq)
      simp only [altOff, altAff, vP1, vP2, vQ1, vQ2] at hk6
      exact placedPiece_of_copy o (aEven u2) _ _ κ6 hk6

/-- **The even alternate node from the full decomposition**: at a word that does not end in `3`, an odometer that respects the
full even alternate decomposition satisfies `AltEvenNodeP`, when the even register lies on the boundary tile and respects its
boundary strings. -/
theorem altEvenNode_of_respects (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2))
    (hc : w.getLast? ≠ some Digit.three) (o : PartialOdometer)
    (hR : RespectsPieces o (tileAltEvenPieces S pOdd pEven aOdd aEven lEven w))
    (hb : S.bdry (some u2) false = (pEven u2).dom)
    (hRQ : RespectsAnchored (pEven u2).dom (hWordOf u2 true) (vWordOf u2 true) (pEven u2).val) :
    AltEvenNodeP S o pOdd pEven aOdd aEven w := by
  have hty : (altTypeOf w == some Digit.three) = false := by simp [altTypeOf, hc]
  have hL : tileAltEvenPieces S pOdd pEven aOdd aEven lEven w =
      [stdPiece (pEven u2) (altOff w (altQ0Coeff (W1Odd w) .dsQ1Plus)) (altAff w (altQ0Coeff (W1Odd w) .dsQ1Plus)),
        stdPiece (pEven u2) (altOff w (altQ0Coeff (W1Odd w) .dsQ1Plus) + (altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)
          (altAff w (altQ0Coeff (W1Odd w) .dsQ1Plus) + aP2 w),
        stdPiece (pEven u2) (altOff w (altQ0Coeff (W1Odd w) .dsQ1Minus)) (altAff w (altQ0Coeff (W1Odd w) .dsQ1Minus)),
        stdPiece (pEven u2) (altOff w (altQ0Coeff (W1Odd w) .dsQ1Minus) + (altShifts (W1Odd w) (vP2 w) (vQ1 w)).2)
          (altAff w (altQ0Coeff (W1Odd w) .dsQ1Minus) + aP2 w),
        stdPiece (pOdd u1) (altOff w (altQ0Coeff (W1Odd w) .p1Plus)) (altAff w (altQ0Coeff (W1Odd w) .p1Plus)),
        stdPiece (pOdd u1) (altOff w (altQ0Coeff (W1Odd w) .p1Minus)) (altAff w (altQ0Coeff (W1Odd w) .p1Minus))] ++
      (match (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) with
        | none => []
        | some c => [stdPiece (aOdd u1) (altOff w c) (altAff w c)]) := by
    simp only [tileAltEvenPieces, hc, decide_false, Bool.false_eq_true, if_false, hreg, regOdo]
    rfl
  rw [hL] at hR
  have h6 : ∀ c, (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) = some c →
      ∃ κ : ℤ, ∀ x ∈ (aOdd u1).dom.image (· + altOff w c), x ∈ o.dom ∧
        o.val x = (aOdd u1).val (x - altOff w c) + dotS (altAff w c) x + κ := by
    intro c hcq
    rw [hcq] at hR
    exact std_at hR (List.mem_append_right _ (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨κ0, h0⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inl rfl)))
  obtain ⟨κ1, h1⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  obtain ⟨κ2, h2⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inl rfl)))))))
  obtain ⟨κ3, h3⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))
  obtain ⟨κ4, h4⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))))
  obtain ⟨κ5, h5⟩ := std_at hR (List.mem_append_left _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))))))))))))
  simp only [altOff, altAff, W1Odd, vP1, vP2, vQ1, vQ2, aP2] at h0 h1 h2 h3 h4 h5
  obtain ⟨hcP, hplP⟩ := dbl_of_copies o (pEven u2) _ _ _ _ κ0 κ1 h0 h1
  obtain ⟨hcM, hplM⟩ := dbl_of_copies o (pEven u2) _ _ _ _ κ2 κ3 h2 h3
  have hin := side_inside _ _ _ _ hRQ
  unfold AltEvenNodeP
  simp only [hreg, regOdo, hty, altPartial, Bool.false_eq_true, if_false, hb, DoublingRespect.regWords, Bool.not_false]
  refine ⟨_, _, dblAlt_true _ _ _ _ _ _ _ _ _ hcP (hin _), dblAlt_false _ _ _ _ _ _ _ _ _ hcM (hin _),
    hplP _ (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)),
    hplM _ (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)),
    placed_of_copy o (pOdd u1) _ _ κ4 h4 _ (fun x hx => hx.1),
    placed_of_copy o (pOdd u1) _ _ κ5 h5 _ (fun x hx => hx.1), ?_⟩
  cases ht : altTypeOf w with
  | none => trivial
  | some ty =>
    dsimp only
    cases hq : altP1Coeff (phase w == 1) ty with
    | none => exact trivial
    | some c =>
      obtain ⟨κ6, hk6⟩ := h6 c (by simp only [ht, Option.bind_some, W1Odd]; exact hq)
      simp only [altOff, altAff, vP1, vP2, vQ1, vQ2] at hk6
      exact placedPiece_of_copy o (aOdd u1) _ _ κ6 hk6

end FLatticePaper.Tiles.WeakAltNode
