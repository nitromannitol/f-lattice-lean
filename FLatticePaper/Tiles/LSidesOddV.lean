import FLatticePaper.Tiles.LSidesEvenK
import FLatticePaper.Tiles.GlueStringDecomp
import FLatticePaper.Tiles.TileHalfTurnL
import FLatticePaper.Tiles.VLinVertical
import FLatticePaper.Tiles.VerticalIdentities
import FLatticePaper.Tiles.AltItem3
import FLatticePaper.Tiles.ReflectedCoverConverse
import FLatticePaper.Tiles.ConnectedL
import FLatticePaper.Tiles.TileHalfTurnInput

/-! # The vertical side of the `+` odd L-correction

For `w = pre 2^k` (`pre` not a base word and not ending in `2`), the vertical side of the odd child of `w` that the `+` odd
L-correction contains (`lemma:l_correc_properties` (2), rotated: the left side when `W_1` is even, the right side when odd) is the
same side of the copy `P^-` of the odd register followed by that side of a copy of the even register (`GlueStringDecomp`). Through
the trailing `2`s the copy `P^-` is again the odd child of `pre 2^(k-1)`, so the side is covered by the copies of the even register
of `pre` (the stems of the L-correction, placed with the affine factors `m a_{q_2,2}`) and the copy of the odd register of `pre`
(its bridge). These are copies with the same placement and affine factor in the nested decompositions of the odd child, so the
glued L-corrected odometer and the tile odometer of the child differ by one constant on each, and the consecutive copies meet at
corner points of the registers. -/

namespace FLatticePaper.Tiles.LSidesOddV

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase stateAt oddTile evenTile)
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (PiecesAgree gluedOdo pieceVal)
open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo regStep)
open FLatticePaper.Tiles.StandardClause (fracOdd fracEven)
open FLatticePaper.Tiles.ConnectedAltL (oStemPos)
open FLatticePaper.Tiles.TileHalfTurnL (oBridgePos oAffAt oStemC oBridgeC)

/-! ### Copies placed with an affine factor -/

/-- `o` contains the copy of `q` placed at `s` with affine factor `a`, up to one constant. -/
def PlacedEqA (o q : PartialOdometer) (s a : Site) : Prop :=
  ∃ b : ℤ, ∀ y ∈ q.dom, y + s ∈ o.dom ∧ o.val (y + s) = q.val y + dotS a (y + s) + b

theorem placedEqA_trans {o q r : PartialOdometer} {s t a a' : Site} (h1 : PlacedEqA o q s a)
    (h2 : PlacedEqA q r t a') : PlacedEqA o r (t + s) (a + a') := by
  obtain ⟨b1, h1⟩ := h1
  obtain ⟨b2, h2⟩ := h2
  refine ⟨b1 + b2 - dotS a' s, fun y hy => ?_⟩
  obtain ⟨m2, e2⟩ := h2 y hy
  obtain ⟨m1, e1⟩ := h1 _ m2
  rw [← add_assoc]
  refine ⟨m1, ?_⟩
  rw [e1, e2]
  simp only [dotS, Prod.fst_add, Prod.snd_add]
  ring

/-- A piece of a decomposition that `o` respects is placed in `o`. -/
theorem placedEqA_of_respects {o : PartialOdometer} {ps : List Piece} (h : RespectsPieces o ps) {i : ℕ}
    {q : PartialOdometer} {s a : Site} (hi : ps[i]? = some (stdPiece q s a)) : PlacedEqA o q s a := by
  obtain ⟨b, hb⟩ := h.2 _ (List.mem_of_getElem? hi)
  refine ⟨b, fun y hy => ?_⟩
  have hp : y + s ∈ (stdPiece q s a).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
  refine ⟨h.1 ▸ LSidesEven.mem_pieceUnion_of hi hp, ?_⟩
  rw [hb (y + s) hp (by simp [stdPiece])]
  simp [stdPiece]

/-! ### The words `pre 2^k` -/

/-- The word `pre 2^k`. -/
abbrev wk2 (pre : Word) (k : ℕ) : Word := pre ++ List.replicate k Digit.two

theorem wk2_succ (pre : Word) (k : ℕ) : wk2 pre (k + 1) = wk2 pre k ++ [Digit.two] := by
  simp [wk2, List.replicate_succ', List.append_assoc]

theorem wk2_trailing (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    trailingCount Digit.two (wk2 pre k) = k ∧ stripTrailing Digit.two (wk2 pre k) = pre := by
  induction k with
  | zero =>
    simp only [wk2, List.replicate_zero, List.append_nil]
    exact ⟨h0, by simp [stripTrailing, h0]⟩
  | succ k ih =>
    rw [wk2_succ, JointRot.trailingCount_snoc, JointRot.stripTrailing_snoc, if_pos rfl, if_pos rfl]
    exact ⟨by rw [ih.1], ih.2⟩

theorem notBase_snoc_two (v : Word) (hv : ¬ IsBase v) : ¬ IsBase (v ++ [Digit.two]) := by
  rintro (h | h | h)
  · simp at h
  · exact absurd (h Digit.two (by simp)) (by decide)
  · exact hv (Or.inr (Or.inr fun d hd => h d (List.mem_append_left _ hd)))

theorem wk2_facts (pre : Word) (hpre : ¬ IsBase pre) (k : ℕ) :
    ¬ IsBase (wk2 pre k) ∧ (regsAt (wk2 pre k)).2 = (regsAt pre).2 ∧ W1Odd (wk2 pre k) = W1Odd pre := by
  refine ⟨?_, ?_, JointRot.W1Odd_append_replicate pre k Digit.two (by decide)⟩
  · induction k with
    | zero => simpa [wk2] using hpre
    | succ k ih => rw [wk2_succ]; exact notBase_snoc_two _ ih
  · induction k with
    | zero => simp [wk2]
    | succ k ih => rw [wk2_succ, WeakStepPaper.regsAt_snoc]; exact ih

theorem regsAt_wk2_succ (pre : Word) (k : ℕ) :
    regsAt (wk2 pre (k + 1)) = (some (wk2 pre k), (regsAt (wk2 pre k)).2) := by
  rw [wk2_succ, WeakStepPaper.regsAt_snoc]
  rfl

/-! ### The positions in closed form -/

/-- `v_{p,1}`, `v_{q,1}`, `v_{q,2}` and `a_{q,2}` of the parents of the prefix. -/
abbrev vA (pre : Word) : Site := texV1Odd (parentsAt pre).odd
abbrev vU (pre : Word) : Site := texV1Even (parentsAt pre).even
abbrev vV (pre : Word) : Site := texV2 (parentsAt pre).even
abbrev aQ (pre : Word) : Site := offsetA (parentsAt pre).even.num (parentsAt pre).even.den true

set_option hygiene false in
/-- Unfolds a position of `pre 2^k` into the parents of `pre` and `k`. -/
macro "pos_alg" : tactic => `(tactic| (
  obtain ⟨ht, hs⟩ := wk2_trailing pre h0 k
  have hW := JointRot.W1Odd_append_replicate pre k Digit.two (by decide)
  have hp := JointRot.parents_append_twos pre k
  simp only [oStemPos, oBridgePos, oAffAt, oStemC, oBridgeC, oddLInitOff, oddLInitAff, p0Off, p0Aff,
    SurgicalDict.offsetP0, vP1, vP2, vQ1, vQ2, altOff, altAff, ht, hs, hW, hp, vA, vU, vV, aQ]
  cases hb : W1Odd pre <;> simp only [oddKCoeff, ↓reduceIte, Bool.false_eq_true] <;> ext <;>
    simp [SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine, texV1Odd, texV1Even, texV2, offsetA, pairAffine] <;> ring))

theorem initOff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oddLInitOff (wk2 pre k) true = if W1Odd pre then vA pre + ((2 * k + 1 : ℕ) : ℤ) • vU pre else 0 := by
  pos_alg

theorem stemPos_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k m : ℕ) :
    oStemPos (wk2 pre k) true m =
      (if W1Odd pre then vA pre + ((2 * k + 1 : ℕ) : ℤ) • vU pre else 0) + (m : ℤ) • vV pre := by
  pos_alg

theorem bridgePos_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oBridgePos (wk2 pre k) true =
      (if W1Odd pre then ((2 * k + 2 : ℕ) : ℤ) • vU pre else 0) + ((k + 1 : ℕ) : ℤ) • vV pre := by
  pos_alg

theorem stemAff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k m : ℕ) :
    oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true m) = (m : ℤ) • aQ pre := by
  pos_alg

theorem bridgeAff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oAffAt (wk2 pre k) true (oBridgeC (wk2 pre k) true) = ((k + 1 : ℕ) : ℤ) • aQ pre := by
  pos_alg

theorem p1Minus_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    p0Off (wk2 pre k) .p1Minus = (if W1Odd pre then (2 : ℤ) • vU pre else 0) + vV pre := by
  pos_alg

theorem p1MinusAff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    p0Aff (wk2 pre k) .p1Minus = aQ pre := by
  pos_alg

theorem q1DPlusAff_eq (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    p0Aff (wk2 pre k) .q1DPlus = 0 := by
  pos_alg

theorem stem0 (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oStemPos (wk2 pre k) true 0 = oddLInitOff (wk2 pre k) true ∧
      oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true 0) = p0Aff (wk2 pre k) .q1DPlus := by
  rw [stemPos_eq pre h0, initOff_eq pre h0, stemAff_eq pre h0, q1DPlusAff_eq pre h0]
  simp

theorem stem_succ (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k m : ℕ) :
    oStemPos (wk2 pre (k + 1)) true (m + 1) = oStemPos (wk2 pre k) true m + p0Off (wk2 pre (k + 1)) .p1Minus ∧
      oAffAt (wk2 pre (k + 1)) true (oStemC (wk2 pre (k + 1)) true (m + 1)) =
        p0Aff (wk2 pre (k + 1)) .p1Minus + oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true m) := by
  rw [stemPos_eq pre h0, stemPos_eq pre h0, p1Minus_eq pre h0, stemAff_eq pre h0, stemAff_eq pre h0, p1MinusAff_eq pre h0]
  refine ⟨?_, ?_⟩
  · split_ifs <;> ext <;> simp <;> ring
  · ext <;> simp <;> ring

theorem bridge_succ (pre : Word) (h0 : trailingCount Digit.two pre = 0) (k : ℕ) :
    oBridgePos (wk2 pre (k + 1)) true = oBridgePos (wk2 pre k) true + p0Off (wk2 pre (k + 1)) .p1Minus ∧
      oAffAt (wk2 pre (k + 1)) true (oBridgeC (wk2 pre (k + 1)) true) =
        p0Aff (wk2 pre (k + 1)) .p1Minus + oAffAt (wk2 pre k) true (oBridgeC (wk2 pre k) true) := by
  rw [bridgePos_eq pre h0, bridgePos_eq pre h0, p1Minus_eq pre h0, bridgeAff_eq pre h0, bridgeAff_eq pre h0,
    p1MinusAff_eq pre h0]
  refine ⟨?_, ?_⟩
  · split_ifs <;> ext <;> simp <;> ring
  · ext <;> simp <;> ring

theorem bridge0 (pre : Word) (h0 : trailingCount Digit.two pre = 0) :
    oBridgePos (wk2 pre 0) true = p0Off (wk2 pre 0) .p1Minus ∧
      oAffAt (wk2 pre 0) true (oBridgeC (wk2 pre 0) true) = p0Aff (wk2 pre 0) .p1Minus := by
  rw [bridgePos_eq pre h0, p1Minus_eq pre h0, bridgeAff_eq pre h0, p1MinusAff_eq pre h0]
  refine ⟨?_, ?_⟩ <;> simp

/-! ### The vertical side of the odd child, by copies -/

/-- The vertical side of the `+` odd L-correction of `w`: the right side when `W_1` is odd, the left side when even. -/
def vSide (w : Word) : Side := if W1Odd w then .vPlus else .vMinus

/-- **The vertical side of the odd child is the same side of two copies**: the copy `Q^{+,1}` (`W_1` even) or `Q^{+,2}` (`W_1`
odd) of the even register, at the initial offset of the `+` odd L-correction, and the copy `P^-` of the odd register. -/
theorem vsplit (w u1 u2 : Word) (hreg : regsAt w = (some u1, some u2)) (z : GInt)
    (hz : z ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 (vSide w))) :
    z - oddLInitOff w true ∈ placedSites (sideString (hWordOf u2 true) (vWordOf u2 true) 0 (vSide w)) ∨
      z - p0Off w .p1Minus ∈ placedSites (sideString (hWordOf u1 false) (vWordOf u1 false) 0 (vSide w)) := by
  have hp : (parentsAt w).odd = fracOdd u1 := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq : (parentsAt w).even = fracEven u2 := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  by_cases hph : phase w = 1
  · have hW : W1Odd w = true := by simp [W1Odd, hph]
    obtain ⟨-, -, h3, -⟩ := GlueStringDecomp.odd_of w u1 u2 hreg hph
    simp only [vSide, hW, if_true, sideString] at hz ⊢
    rw [h3, placedSites_append, List.mem_append] at hz
    rw [GlueStringDecomp.lp_bot_even u2 0, GlueStringDecomp.lp_bot_odd u1 0, zero_add, zero_add]
    have e1 : oddLInitOff w true = texV1Odd (fracOdd u1) + texV1Even (fracEven u2) := by
      simp [oddLInitOff, hW, p0Off, SurgicalDict.offsetP0, vP1, vQ1, hp, hq]
    have e2 : p0Off w .p1Minus =
        texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) := by
      simp [p0Off, SurgicalDict.offsetP0, hW, vQ1, vQ2, hq]
    rw [e1, e2]
    rcases hz with h | h
    · left
      rw [show texV1Odd (fracOdd u1) + texV1Even (fracEven u2) + (texV1Even (fracEven u2) - (1, 1)) =
          (texV1Even (fracEven u2) - (1, 1)) + (texV1Odd (fracOdd u1) + texV1Even (fracEven u2)) by abel,
        vStringAt_add, AltItem3.mem_placedSites_map] at h
      exact h
    · right
      rw [show texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2) + (texV1Odd (fracOdd u1) - (1, 1)) =
          (texV1Odd (fracOdd u1) - (1, 1)) + (texV1Even (fracEven u2) + texV1Even (fracEven u2) + texV2 (fracEven u2))
          by abel, vStringAt_add, AltItem3.mem_placedSites_map] at h
      exact h
  · have hW : W1Odd w = false := by simp [W1Odd, hph]
    obtain ⟨-, h2, -, -⟩ := GlueStringDecomp.odd_ef w u1 u2 hreg hph
    simp only [vSide, hW, Bool.false_eq_true, if_false, sideString] at hz ⊢
    rw [h2, placedSites_append, List.mem_append] at hz
    have e1 : oddLInitOff w true = 0 := by simp [oddLInitOff, hW, p0Off, SurgicalDict.offsetP0]
    have e2 : p0Off w .p1Minus = texV2 (fracEven u2) := by simp [p0Off, SurgicalDict.offsetP0, hW, vQ2, hq]
    rw [e1, e2, sub_zero]
    rcases hz with h | h
    · exact Or.inl h
    · right
      rw [show texV2 (fracEven u2) = (0 : GInt) + texV2 (fracEven u2) by rw [zero_add], vRevStringAt_add,
        AltItem3.mem_placedSites_map] at h
      exact h

/-- The side strings of a standard tile lie in the domain of an odometer that respects its anchored strings. -/
theorem side_mem_dom {T : Finset Site} {wh wv : BinaryWord} {S : GInt → ℤ} (hR : SurgicalWeak.RespectsAnchored T wh wv S)
    (s : Side) {x : GInt} (hx : x ∈ placedSites (sideString wh wv 0 s)) : x ∈ T := by
  have h := hR.1 x
  simp only [placedSites_append, List.mem_append, Finset.mem_coe] at h
  cases s <;> simp only [sideString] at hx <;> exact h (by tauto)

/-! ### The entries of the decompositions -/

theorem tOP_entry1 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileOddPieces S pO pE lE v)[1]? =
      some (stdPiece (regOdo S pO pE (regsAt v).1 true) (p0Off v .p1Minus) (p0Aff v .p1Minus)) := by
  simp [tileOddPieces]

theorem tOP_entryQ (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lE : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileOddPieces S pO pE lE v)[if W1Odd v then 3 else 2]? =
      some (stdPiece (regOdo S pO pE (regsAt v).2 false) (oddLInitOff v true) (p0Aff v .q1DPlus)) := by
  cases h : W1Odd v <;> simp [tileOddPieces, h, oddLInitOff]

/-- The stems and the bridge of the `+` odd L-correction of `pre 2^k`. -/
theorem oddL_stems (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (k : ℕ) (elong : Bool) :
    (∀ m ≤ k, (oddLPieces S pO pE aO aE (wk2 pre k) true elong)[m]? =
        some (stdPiece (regOdo S pO pE (regsAt pre).2 false) (oStemPos (wk2 pre k) true m)
          (oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true m)))) ∧
      (oddLPieces S pO pE aO aE (wk2 pre k) true elong)[k + 1]? =
        some (stdPiece (regOdo S pO pE (regsAt pre).1 true) (oBridgePos (wk2 pre k) true)
          (oAffAt (wk2 pre k) true (oBridgeC (wk2 pre k) true))) := by
  obtain ⟨ht, hs⟩ := wk2_trailing pre h0 k
  have hd : (!(stripTrailing Digit.two (wk2 pre k)).isEmpty &&
      (stripTrailing Digit.two (wk2 pre k)).all (fun d => decide (d = Digit.three))) = false := by
    rw [hs]
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hpre (Or.inr (Or.inl hc.2))
  rw [TileHalfTurnL.oLP_eq S pO pE aO aE (wk2 pre k) true elong hd, hs, ht]
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [TileHalfTurnL.get_left _ _ _ m (by simp; omega), List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · rw [TileHalfTurnL.get_mid _ _ _ (by simp)]

/-! ### The nested copies -/

/-- **The nested copies of `pre 2^k`**: an odometer respecting the odd decomposition of `pre 2^k` contains the even register of
`pre` at each stem of the `+` odd L-correction and the odd register of `pre` at its bridge, with the same affine factors, and these
copies cover the vertical side `vSide` of the odd child. -/
theorem nestedV (D : JointData) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (u1 u2 : Word) (hreg : regsAt pre = (some u1, some u2)) :
    ∀ (k : ℕ) (o : PartialOdometer), GoodBelow D f (wk2 pre k).length →
      RespectsPieces o (tileOddPieces D.S (fun u => (below f (wk2 pre k) u).tOdd) (fun u => (below f (wk2 pre k) u).tEven)
        (fun u => (below f (wk2 pre k) u).lEven) (wk2 pre k)) →
      (∀ m ≤ k, PlacedEqA o (f u2).tEven (oStemPos (wk2 pre k) true m)
        (oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true m))) ∧
      PlacedEqA o (f u1).tOdd (oBridgePos (wk2 pre k) true) (oAffAt (wk2 pre k) true (oBridgeC (wk2 pre k) true)) ∧
      ∀ z ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSide (wk2 pre k))),
        (∃ m ≤ k, z - oStemPos (wk2 pre k) true m ∈ (f u2).tEven.dom) ∨
          z - oBridgePos (wk2 pre k) true ∈ (f u1).tOdd.dom := by
  have hl2 : u2.length < pre.length := regsAt_lt pre u2 (Or.inr (by rw [hreg]))
  have hl1 : u1.length < pre.length := regsAt_lt pre u1 (Or.inl (by rw [hreg]))
  intro k
  induction k with
  | zero =>
    intro o hgood hR
    have hr0 : regsAt (wk2 pre 0) = (some u1, some u2) := by simpa [wk2] using hreg
    have hl1' : u1.length < (wk2 pre 0).length := by simpa [wk2] using hl1
    have hl2' : u2.length < (wk2 pre 0).length := by simpa [wk2] using hl2
    have hb1 : below f (wk2 pre 0) u1 = f u1 := by simp only [below, if_pos hl1']
    have hb2 : below f (wk2 pre 0) u2 = f u2 := by simp only [below, if_pos hl2']
    have e1 := tOP_entry1 D.S (fun u => (below f (wk2 pre 0) u).tOdd) (fun u => (below f (wk2 pre 0) u).tEven)
      (fun u => (below f (wk2 pre 0) u).lEven) (wk2 pre 0)
    have eQ := tOP_entryQ D.S (fun u => (below f (wk2 pre 0) u).tOdd) (fun u => (below f (wk2 pre 0) u).tEven)
      (fun u => (below f (wk2 pre 0) u).lEven) (wk2 pre 0)
    rw [hr0] at e1 eQ
    simp only [regOdo, hb1, hb2] at e1 eQ
    obtain ⟨hS1, -⟩ := hgood u1 hl1'
    obtain ⟨hS2, -⟩ := hgood u2 hl2'
    have hR1 := (WeakStepAssembly.slice_respects D f u1 hS1).1
    have hR2 := (WeakStepAssembly.slice_respects D f u2 hS2).2
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · obtain rfl : m = 0 := by omega
      rw [(stem0 pre h0 0).1, (stem0 pre h0 0).2]
      exact placedEqA_of_respects hR eQ
    · rw [(bridge0 pre h0).1, (bridge0 pre h0).2]
      exact placedEqA_of_respects hR e1
    · rcases vsplit (wk2 pre 0) u1 u2 hr0 z hz with h | h
      · left
        refine ⟨0, le_rfl, ?_⟩
        rw [(stem0 pre h0 0).1]
        exact side_mem_dom hR2 _ h
      · right
        rw [(bridge0 pre h0).1]
        exact side_mem_dom hR1 _ h
  | succ k ih =>
    intro o hgood hR
    obtain ⟨-, -, hW⟩ := wk2_facts pre hpre (k + 1)
    obtain ⟨hnb', hr2', hW'⟩ := wk2_facts pre hpre k
    have hws := wk2_succ pre k
    have hlt : (wk2 pre k).length < (wk2 pre (k + 1)).length := by rw [hws]; simp
    have hrs : regsAt (wk2 pre (k + 1)) = (some (wk2 pre k), some u2) := by rw [regsAt_wk2_succ, hr2', hreg]
    have hl2' : u2.length < (wk2 pre (k + 1)).length := lt_of_lt_of_le hl2 (by simp [wk2])
    have hb2 : below f (wk2 pre (k + 1)) u2 = f u2 := by simp only [below, if_pos hl2']
    have hbk : below f (wk2 pre (k + 1)) (wk2 pre k) = f (wk2 pre k) := by simp only [below, if_pos hlt]
    have e1 := tOP_entry1 D.S (fun u => (below f (wk2 pre (k + 1)) u).tOdd)
      (fun u => (below f (wk2 pre (k + 1)) u).tEven) (fun u => (below f (wk2 pre (k + 1)) u).lEven) (wk2 pre (k + 1))
    have eQ := tOP_entryQ D.S (fun u => (below f (wk2 pre (k + 1)) u).tOdd)
      (fun u => (below f (wk2 pre (k + 1)) u).tEven) (fun u => (below f (wk2 pre (k + 1)) u).lEven) (wk2 pre (k + 1))
    rw [hrs] at e1 eQ
    simp only [regOdo, hbk, hb2] at e1 eQ
    have hP := placedEqA_of_respects hR e1
    have hQ := placedEqA_of_respects hR eQ
    have hgood' : GoodBelow D f (wk2 pre k).length := fun u hu => hgood u (lt_trans hu hlt)
    have hRk : RespectsPieces (f (wk2 pre k)).tOdd (tileOddPieces D.S (fun u => (below f (wk2 pre k) u).tOdd)
        (fun u => (below f (wk2 pre k) u).tEven) (fun u => (below f (wk2 pre k) u).lEven) (wk2 pre k)) :=
      (((hgood (wk2 pre k) hlt).1.2.2.1).2.1 hnb').1
    obtain ⟨hn, hbr, hcov⟩ := ih (f (wk2 pre k)).tOdd hgood' hRk
    obtain ⟨hS2, -⟩ := hgood u2 hl2'
    have hR2 := (WeakStepAssembly.slice_respects D f u2 hS2).2
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · rcases m with _ | m
      · rw [(stem0 pre h0 (k + 1)).1, (stem0 pre h0 (k + 1)).2]
        exact hQ
      · rw [(stem_succ pre h0 k m).1, (stem_succ pre h0 k m).2]
        exact placedEqA_trans hP (hn m (by omega))
    · rw [(bridge_succ pre h0 k).1, (bridge_succ pre h0 k).2]
      exact placedEqA_trans hP hbr
    · have hvs : vSide (wk2 pre (k + 1)) = vSide (wk2 pre k) := by simp only [vSide, hW, hW']
      rcases vsplit (wk2 pre (k + 1)) (wk2 pre k) u2 hrs z hz with h | h
      · left
        refine ⟨0, by omega, ?_⟩
        rw [(stem0 pre h0 (k + 1)).1]
        exact side_mem_dom hR2 _ h
      · rw [hvs] at h
        rcases hcov _ h with ⟨m, hm, hm'⟩ | hb
        · left
          refine ⟨m + 1, by omega, ?_⟩
          rw [(stem_succ pre h0 k m).1]
          convert hm' using 1
          abel
        · right
          rw [(bridge_succ pre h0 k).1]
          convert hb using 1
          abel

/-! ### One constant on the vertical side -/

/-- **The stems and the bridge of the `+` odd L-correction after trailing `2`s**: for `w = pre 2^k` with `pre` not a base word and
not ending in `2`, the glued L-corrected odometer and the tile odometer of the odd child differ by one constant on all the stems
(the copies of the even register `u2` of `pre`) and on the bridge (the copy of the odd register `u1`); the vertical side `vSide w`
of the child is covered by them. -/
theorem oddL_stems_const (D : JointData) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (u1 u2 : Word) (hreg : regsAt pre = (some u1, some u2)) (k : ℕ)
    (hgood : GoodBelow D f (wk2 pre k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ) :
    ∃ c : ℤ, (∀ m ≤ k, ∀ y ∈ (f u2).tEven.dom,
        y + oStemPos (wk2 pre k) true m ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧
          y + oStemPos (wk2 pre k) true m ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val (y + oStemPos (wk2 pre k) true m) =
            tod.val (y + oStemPos (wk2 pre k) true m) + c) ∧
      (∀ y ∈ (f u1).tOdd.dom,
        y + oBridgePos (wk2 pre k) true ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧
          y + oBridgePos (wk2 pre k) true ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val (y + oBridgePos (wk2 pre k) true) =
            tod.val (y + oBridgePos (wk2 pre k) true) + c) := by
  obtain ⟨hnb, -, -⟩ := wk2_facts pre hpre k
  have hRt := (hT.2.1 hnb).1
  obtain ⟨hn, hbr, -⟩ := nestedV D f pre hpre h0 u1 u2 hreg k tod hgood hRt
  have hl1 : u1.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u1 (Or.inl (by rw [hreg]))) (by simp [wk2])
  have hl2 : u2.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u2 (Or.inr (by rw [hreg]))) (by simp [wk2])
  have hb1 : below f (wk2 pre k) u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f (wk2 pre k) u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨hLm, hLb⟩ := oddL_stems D.S (fun u => (below f (wk2 pre k) u).tOdd) (fun u => (below f (wk2 pre k) u).tEven)
    (fun u => (below f (wk2 pre k) u).aOdd) (fun u => (below f (wk2 pre k) u).aEven) pre hpre h0 k elong
  rw [hreg] at hLm hLb
  simp only [regOdo, hb1, hb2] at hLm hLb
  choose! b hb using hn
  obtain ⟨bB, hbB⟩ := hbr
  have gs : ∀ m ≤ k, ∀ y ∈ (f u2).tEven.dom,
      y + oStemPos (wk2 pre k) true m ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧
        y + oStemPos (wk2 pre k) true m ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val (y + oStemPos (wk2 pre k) true m) =
          tod.val (y + oStemPos (wk2 pre k) true m) + (κ m - b m) := by
    intro m hm y hy
    have hp : y + oStemPos (wk2 pre k) true m ∈ (stdPiece (f u2).tEven (oStemPos (wk2 pre k) true m)
        (oAffAt (wk2 pre k) true (oStemC (wk2 pre k) true m))).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht, hv⟩ := hb m hm y hy
    refine ⟨LSidesEven.mem_pieceUnion_of (hLm m hm) hp, ht, ?_⟩
    rw [LSidesEven.glued_val _ κ hag m _ (hLm m hm) _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right]
    ring
  have gb : ∀ y ∈ (f u1).tOdd.dom,
      y + oBridgePos (wk2 pre k) true ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧
        y + oBridgePos (wk2 pre k) true ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val (y + oBridgePos (wk2 pre k) true) =
          tod.val (y + oBridgePos (wk2 pre k) true) + (κ (k + 1) - bB) := by
    intro y hy
    have hp : y + oBridgePos (wk2 pre k) true ∈ (stdPiece (f u1).tOdd (oBridgePos (wk2 pre k) true)
        (oAffAt (wk2 pre k) true (oBridgeC (wk2 pre k) true))).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht, hv⟩ := hbB y hy
    refine ⟨LSidesEven.mem_pieceUnion_of hLb hp, ht, ?_⟩
    rw [LSidesEven.glued_val _ κ hag (k + 1) _ hLb _ hp (by simp [stdPiece]), hv]
    simp only [pieceVal, stdPiece, add_sub_cancel_right]
    ring
  -- corner points of the registers
  have hp : (parentsAt u1).current .odd = (parentsAt pre).odd :=
    ((WeakStepAssembly.regsAt_parents pre).1 u1 (by rw [hreg])).symm
  have hq : (parentsAt u2).current .even = (parentsAt pre).even :=
    ((WeakStepAssembly.regsAt_parents pre).2 u2 (by rw [hreg])).symm
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  obtain ⟨αo, βo, -, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (WeakStepAssembly.slice_respects D f u1 hS1).1
  obtain ⟨αe, βe, -, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven (WeakStepAssembly.slice_respects D f u2 hS2).2
  obtain ⟨-, ⟨c10, -⟩, ⟨cX01, -⟩, -, -, -, -, -⟩ := hVo
  obtain ⟨-, ⟨d10, -⟩, -, -, ⟨dY10, -⟩, -, -, ⟨dD10, -⟩⟩ := hVe
  rw [hp] at cX01
  rw [hq] at dY10 dD10
  -- the constants agree along the stems and with the bridge
  have step : ∀ m < k, κ (m + 1) - b (m + 1) = κ m - b m := by
    intro m hm
    have e : oStemPos (wk2 pre k) true (m + 1) = oStemPos (wk2 pre k) true m + vV pre := by
      rw [stemPos_eq pre h0, stemPos_eq pre h0]
      split_ifs <;> ext <;> simp <;> ring
    have g1 := gs m (by omega) _ dY10
    have g2 := gs (m + 1) (by omega) _ d10
    have ex : texV2 (parentsAt pre).even + ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 pre k) true m =
        ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 pre k) true (m + 1) := by rw [e]; abel
    rw [ex] at g1
    rw [g1.2.2] at g2
    linarith [g2.2.2]
  have hall : ∀ m ≤ k, κ m - b m = κ 0 - b 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [step m (by omega), ih (by omega)]
  have hbk : κ (k + 1) - bB = κ k - b k := by
    cases h : W1Odd pre
    · have e : oBridgePos (wk2 pre k) true = oStemPos (wk2 pre k) true k + vV pre := by
        rw [bridgePos_eq pre h0, stemPos_eq pre h0, h]
        ext <;> simp <;> ring
      have g1 := gs k le_rfl _ dY10
      have g2 := gb _ c10
      have ex : ((1 : ℤ), (0 : ℤ)) + oBridgePos (wk2 pre k) true =
          texV2 (parentsAt pre).even + ((1 : ℤ), (0 : ℤ)) + oStemPos (wk2 pre k) true k := by rw [e]; abel
      rw [ex, g1.2.2] at g2
      linarith [g2.2.2]
    · have e : oBridgePos (wk2 pre k) true =
          oStemPos (wk2 pre k) true k + (vU pre + vV pre - vA pre) := by
        rw [bridgePos_eq pre h0, stemPos_eq pre h0, h]
        simp only [if_true]
        ext <;> simp <;> ring
      have g1 := gs k le_rfl _ dD10
      have g2 := gb _ cX01
      have ex : texV1Odd (parentsAt pre).odd - ((0 : ℤ), (1 : ℤ)) + oBridgePos (wk2 pre k) true =
          texV1Even (parentsAt pre).even + texV2 (parentsAt pre).even + ((1 : ℤ), (-1 : ℤ)) - ((1 : ℤ), (0 : ℤ)) +
            oStemPos (wk2 pre k) true k := by
        rw [e]; ext <;> simp <;> ring
      rw [ex, g1.2.2] at g2
      linarith [g2.2.2]
  refine ⟨κ 0 - b 0, fun m hm y hy => ?_, fun y hy => ?_⟩
  · rw [← hall m hm]; exact gs m hm y hy
  · rw [← hall k le_rfl, ← hbk]; exact gb y hy

/-- **The vertical side of the `+` odd L-correction after trailing `2`s** (`lemma:l_correc_properties` (2), rotated, vertical
part): for `w = pre 2^k` with `pre` not a base word and not ending in `2`, the glued L-corrected odometer and the tile odometer of
the odd child differ by one constant on the vertical side `vSide w` of the child. -/
theorem oddL_vert_k (D : JointData) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (k : ℕ) (hgood : GoodBelow D f (wk2 pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSide (wk2 pre k))),
      x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧ x ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val x = tod.val x + c := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase pre hpre
  obtain ⟨hnb, -, -⟩ := wk2_facts pre hpre k
  obtain ⟨-, -, hcov⟩ := nestedV D f pre hpre h0 u1 u2 hreg k tod hgood ((hT.2.1 hnb).1)
  obtain ⟨c, hs, hb⟩ := oddL_stems_const D f pre hpre h0 u1 u2 hreg k hgood wo we wao wae tod tev aod aev hT elong κ hag
  refine ⟨c, fun x hx => ?_⟩
  rcases hcov x hx with ⟨m, hm, hxm⟩ | hxb
  · have g := hs m hm _ hxm
    rw [sub_add_cancel] at g
    exact g
  · have g := hb _ hxb
    rw [sub_add_cancel] at g
    exact g

/-- **The vertical side of the `+` odd L-correction after trailing `2`s**, both parts of `LSidesAgree` for that side: the glued
odometer respects the side string of the odd child and agrees there with its tile odometer up to one constant. -/
theorem oddL_vert_side_k (D : JointData) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.two pre = 0) (k : ℕ) (hgood : GoodBelow D f (wk2 pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ) :
    RespectsTiles (sideOrient (vSide (wk2 pre k))).1 (sideOrient (vSide (wk2 pre k))).2
        (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSide (wk2 pre k)))
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0
          (vSide (wk2 pre k))),
        x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).dom ∧ x ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) true elong) κ).val x = tod.val x + c := by
  obtain ⟨c, hc⟩ := oddL_vert_k D f pre hpre h0 k hgood wo we wao wae tod tev aod aev hT elong κ hag
  obtain ⟨-, -, -, -, hR, -⟩ := hT
  have hRs : RespectsTiles (sideOrient (vSide (wk2 pre k))).1 (sideOrient (vSide (wk2 pre k))).2
      (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSide (wk2 pre k))) tod.val := by
    unfold vSide
    split_ifs
    · exact hR.2.2.2.2
    · exact hR.2.2.2.1
  exact ⟨LSidesEven.respectsTiles_add_const _ _ _ _ _ c hRs (fun x hx => (hc x hx).2.2), c, hc⟩

/-! ### The `-` odd L-correction, by the half-turn -/

/-- The vertical side of the `-` odd L-correction of `w`: the left side when `W_1` is odd, the right side when even. -/
def vSideM (w : Word) : Side := if W1Odd w then .vMinus else .vPlus

/-- **The left side of the odd child is the half-turn of its right side** about the centre `v_1 + v_2 + 1 - i` of the child. -/
theorem left_iff_right (w : Word) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 .vMinus) ↔
      TileHalfTurnStd.cOdd ((parentsAt w).current .odd) - x ∈
        placedSites (sideString (hWordOf w false) (vWordOf w false) 0 .vPlus) := by
  simp only [sideString]
  rw [ReflectedCoverConverse.placed_vRev_iff (vWordOf w false) Letter.q (GlueStringDecomp.vp_last w)
    (lastPosOf (hStringAt (hWordOf w false) 0)) 0 x]
  have e : lastPosOf (hStringAt (hWordOf w false) 0) + lastPosOf (vStringAt (vWordOf w false) (0, 0)) +
      ReflectedCover.shR Letter.q + 0 = TileHalfTurnStd.cOdd ((parentsAt w).current .odd) := by
    have h1 := GlueStringDecomp.lp_bot_odd w 0
    have h2 := GlueStringDecomp.lp_right_odd w (0, 0)
    rw [h1, h2]
    simp only [TileHalfTurnStd.cOdd, ReflectedCover.shR, fracOdd]
    ext <;> (simp; try ring)
  rw [e]

/-- The sides of the `+` and `-` odd L-corrections are exchanged by the half-turn of the child. -/
theorem sideM_iff (w : Word) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf w false) (vWordOf w false) 0 (vSideM w)) ↔
      TileHalfTurnStd.cOdd ((parentsAt w).current .odd) - x ∈
        placedSites (sideString (hWordOf w false) (vWordOf w false) 0 (vSide w)) := by
  unfold vSideM vSide
  cases W1Odd w
  · simp only [Bool.false_eq_true, if_false]
    rw [left_iff_right w (TileHalfTurnStd.cOdd ((parentsAt w).current .odd) - x), sub_sub_cancel]
  · simp only [if_true]
    exact left_iff_right w x

theorem pre_split2 (pre : Word) (hpre : ¬ IsBase pre) (h0 : trailingCount Digit.two pre = 0) :
    ∃ v d, d ≠ Digit.two ∧ pre = v ++ [d] := by
  have hne : pre ≠ [] := fun h => hpre (Or.inl h)
  refine ⟨pre.dropLast, pre.getLast hne, fun hd => ?_, (List.dropLast_append_getLast hne).symm⟩
  have e := List.dropLast_append_getLast hne
  rw [hd] at e
  rw [← e, JointRot.trailingCount_snoc, if_pos rfl] at h0
  omega

/-- **The tile odometer of the odd child is normalised with slope `0`**: it contains, with affine factor `0` at the origin, the
odd register (`W_1` odd, `P^+`) or the even register (`W_1` even, `Q^{+,1}`). -/
theorem tod_slope_zero (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hw : ¬ IsBase w) (hgood : GoodBelow D f w.length) (tod : PartialOdometer)
    (hR : RespectsPieces tod (tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).lEven) w)) : JointRot.SlopeZero tod := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hb1 : below f w u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f w u2 = f u2 := by simp only [below, if_pos hl2]
  have hsl := TileHalfTurnInput.slopes_below D hS hA f w.length hgood
  cases h : W1Odd w
  · have e : (tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).lEven) w)[2]? = some (stdPiece (f u2).tEven (p0Off w .q1DPlus) (p0Aff w .q1DPlus)) := by
      simp [tileOddPieces, hreg, regOdo, hb2, h]
    refine JointRot.slopeZero_of_piece _ _ hR _ (List.mem_of_getElem? e) ?_ ?_ rfl (hsl u2 hl2).2.1
    · simp [stdPiece, p0Off, SurgicalDict.offsetP0, h]
    · simp [stdPiece, p0Aff, h, pairAffine, offsetA]
  · have e : (tileOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).lEven) w)[0]? = some (stdPiece (f u1).tOdd (p0Off w .p1Plus) (p0Aff w .p1Plus)) := by
      simp [tileOddPieces, hreg, regOdo, hb1]
    refine JointRot.slopeZero_of_piece _ _ hR _ (List.mem_of_getElem? e) ?_ ?_ rfl (hsl u1 hl1).1
    · simp [stdPiece, p0Off, SurgicalDict.offsetP0, h]
    · simp [stdPiece, p0Aff, h, pairAffine, offsetA]

/-- **The vertical side of the `-` odd L-correction after trailing `2`s**: for `w = pre 2^k` with `pre` not a base word and not
ending in `2`, the glued `-` L-corrected odometer and the tile odometer of the odd child differ by one constant on the vertical
side `vSideM w`. The `+` and `-` L-corrected odometers are exchanged by the half-turn of the child (`TileHalfTurnL.lHalfTurn_odd`),
the side is the half-turn of the side of the `+` one (`sideM_iff`), and the tile odometer has its half-turn identity. -/
theorem oddL_vert_minus_k (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre) (h0 : trailingCount Digit.two pre = 0) (k : ℕ)
    (hgood : GoodBelow D f (wk2 pre k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev)
    (hTP : TileProps (wk2 pre k) tod tev aod aev) (elong : Bool) (κp κm : ℕ → ℤ)
    (hagp : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true elong) κp)
    (hagm : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSideM (wk2 pre k))),
      x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm).dom ∧ x ∈ tod.dom ∧
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm).val x = tod.val x + c := by
  obtain ⟨v, d, hd, hvd⟩ := pre_split2 pre hpre h0
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase pre hpre
  obtain ⟨htc, hst⟩ := wk2_trailing pre h0 k
  obtain ⟨hnb, -, -⟩ := wk2_facts pre hpre k
  have hpreS : stripTrailing Digit.two (wk2 pre k) = v ++ [d] := by rw [hst, hvd]
  have hregB : (!(stripTrailing Digit.two (wk2 pre k)).isEmpty &&
      (stripTrailing Digit.two (wk2 pre k)).all (fun d => decide (d = Digit.three))) = false := by
    rw [hst]
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hpre (Or.inr (Or.inl hc.2))
  have hdef : OddLDefined (wk2 pre k) := ⟨v, d, k, hd, by rw [wk2, hvd]⟩
  have hRs := JointGlue.respectsPieces_glued _ κp (JointGlue.oddLPieces_covered _ _ _ _ _ _ _ _) hagp
  have hRt := JointGlue.respectsPieces_glued _ κm (JointGlue.oddLPieces_covered _ _ _ _ _ _ _ _) hagm
  have hconn := (ConnectedL.connectedL_of D hS hA f (wk2 pre k) (fun u hu => (hgood u hu).1)
    (fun u hu => (hgood u hu).2.2.1)).1 true elong hdef
  have hr2 : (regsAt (stripTrailing Digit.two (wk2 pre k))).2 = some v := by
    rw [hpreS]; exact ConnectedAltL.regs_pre_snd v d hd
  have hr1 : (regsAt (stripTrailing Digit.two (wk2 pre k))).1 = some u1 := by rw [hst, hreg]
  have hvl : v.length < (wk2 pre k).length := by rw [wk2, hvd]; simp
  have hu1l : u1.length < (wk2 pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u1 (Or.inl (by rw [hreg]))) (by simp [wk2])
  have hSt : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).tOdd)
      (fun u => (below f (wk2 pre k) u).tEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).2 false)
      (TileHalfTurnStd.cEven (parentsAt (stripTrailing Digit.two (wk2 pre k))).even)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two (wk2 pre k))).even) := by
    rw [hr2]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) v).tEven _ _
    rw [JointRot.below_of_lt f (wk2 pre k) v hvl]
    exact TileHalfTurnInput.raw_reg_even D hS hA f (wk2 pre k).length hgood _ v hr2 hvl
  have hBr : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).tOdd)
      (fun u => (below f (wk2 pre k) u).tEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).1 true)
      (TileHalfTurnStd.cOdd (parentsAt (stripTrailing Digit.two (wk2 pre k))).odd)
      (TileHalfTurnStd.aF (parentsAt (stripTrailing Digit.two (wk2 pre k))).odd) := by
    rw [hr1]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) u1).tOdd _ _
    rw [JointRot.below_of_lt f (wk2 pre k) u1 hu1l]
    exact TileHalfTurnInput.raw_reg_odd D hS hA f (wk2 pre k).length hgood _ u1 hr1 hu1l
  have hHd : TileHalfTurnStd.RawHT (regOdo D.S (fun u => (below f (wk2 pre k) u).aOdd)
      (fun u => (below f (wk2 pre k) u).aEven) (regsAt (stripTrailing Digit.two (wk2 pre k))).2 false)
      (altD v false) (altE v) := by
    rw [hr2]
    show TileHalfTurnStd.RawHT (below f (wk2 pre k) v).aEven _ _
    rw [JointRot.below_of_lt f (wk2 pre k) v hvl]
    exact (TileHalfTurnInput.raw_below D hS hA f (wk2 pre k).length hgood v hvl).2.2.2
  have hX := TileHalfTurnL.lHalfTurn_odd D.S _ _ _ _ (wk2 pre k) v d hd hpreS hregB true elong _ _ hRs hRt hconn hSt hBr
    hHd
  have hsz := tod_slope_zero D hS hA f (wk2 pre k) hnb hgood tod (hT.2.1 hnb).1
  have hHt := TileHalfTurnStd.raw_of_tileHalfTurn tod _ _ _ hTP.2.2.1 hsz
  obtain ⟨c0, hc0⟩ := oddL_vert_k D f pre hpre h0 k hgood wo we wao wae tod tev aod aev hT elong κp hagp
  exact LSidesEvenK.top_of_bottom _ _ tod _ _
    {x | x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSideM (wk2 pre k)))}
    {x | x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSide (wk2 pre k)))}
    (fun x => sideM_iff (wk2 pre k) x) ⟨c0, hc0⟩ hX hHt

/-- **The vertical side of the `-` odd L-correction after trailing `2`s**, both parts of `LSidesAgree` for that side. -/
theorem oddL_vert_minus_side_k (D : JointData) (hS : D.S = paperS) (hA : D.altBase = SurgicalAlt.PaperAltBaseCond)
    (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre) (h0 : trailingCount Digit.two pre = 0) (k : ℕ)
    (hgood : GoodBelow D f (wk2 pre k).length) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk2 pre k)) (wk2 pre k) wo we wao wae tod tev aod aev)
    (hTP : TileProps (wk2 pre k) tod tev aod aev) (elong : Bool) (κp κm : ℕ → ℤ)
    (hagp : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) true elong) κp)
    (hagm : PiecesAgree (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm) :
    RespectsTiles (sideOrient (vSideM (wk2 pre k))).1 (sideOrient (vSideM (wk2 pre k))).2
        (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSideM (wk2 pre k)))
        (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0
          (vSideM (wk2 pre k))),
        x ∈ (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm).dom ∧ x ∈ tod.dom ∧
          (gluedOdo (LStepAssembly.oddPs D f (wk2 pre k) false elong) κm).val x = tod.val x + c := by
  obtain ⟨c, hc⟩ := oddL_vert_minus_k D hS hA f pre hpre h0 k hgood wo we wao wae tod tev aod aev hT hTP elong κp κm hagp
    hagm
  obtain ⟨-, -, -, -, hR, -⟩ := hT
  have hRs : RespectsTiles (sideOrient (vSideM (wk2 pre k))).1 (sideOrient (vSideM (wk2 pre k))).2
      (sideString (hWordOf (wk2 pre k) false) (vWordOf (wk2 pre k) false) 0 (vSideM (wk2 pre k))) tod.val := by
    unfold vSideM
    split_ifs
    · exact hR.2.2.2.1
    · exact hR.2.2.2.2
  exact ⟨LSidesEven.respectsTiles_add_const _ _ _ _ _ c hRs (fun x hx => (hc x hx).2.2), c, hc⟩

end FLatticePaper.Tiles.LSidesOddV
