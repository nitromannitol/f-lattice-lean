import FLatticePaper.Tiles.BaseInvariant
import FLatticePaper.Tiles.HorizontalInduction
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.LStepAssembly
import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.StdPseudoAnchoredSets

/-! # The horizontal sides of the even L-corrections

The bottom string of the even child of a word that is not a base word lies in the copy of the even register at `q1Plus` and the
copy of the odd register at `p1DPlus` (`bottom_even_copies`): the child word is the concatenation of the two parent words
(`RegisterLink.childPQ_eq`), each parent word is a block whose junction offset is the first lattice vector of its fraction
(`HorizontalStep.block_odd_blk`, `block_even_blk`), and the parent words lie in the registers (`HorizontalStep.Inv`). -/

namespace FLatticePaper.Tiles.LSidesEven

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase stateAt oddTile evenTile shift)
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily (q0Off)

/-- The horizontal invariant holds at every word. -/
theorem inv_every (w : Word) : HorizontalStep.Inv w :=
  HorizontalInduction.inv_all BaseInvariant.inv_nil
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact BaseInvariant.inv_three j)
    (fun n hn => by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact BaseInvariant.inv_two j) w

/-- **The bottom string of the even child lies in its two bottom copies**: the even register at `q1Plus` and the odd register at
`p1DPlus`. -/
theorem bottom_even_copies (w : Word) (hw : ¬ IsBase w) (z : GInt) (hz : z ∈ stringSites false false (hWordOf w true)) :
    z ∈ shift (stateAt w).tEven (q0Off w .q1Plus) ∨ z ∈ shift (stateAt w).tOdd (q0Off w .p1DPlus) := by
  obtain ⟨-, -, hIP, hIQ⟩ := inv_every w
  have hQ := CeilWords.quadInv_all w
  unfold CeilWords.QuadInv at hQ
  obtain ⟨-, -, c3, c4⟩ := hQ
  have hn3 : ¬ ∀ d ∈ w, d = Digit.three := fun h => hw (Or.inr (Or.inl h))
  have hn2 : ¬ ∀ d ∈ w, d = Digit.two := fun h => hw (Or.inr (Or.inr h))
  obtain ⟨⟨pw', hpw, hpl⟩, hjP⟩ :=
    HorizontalStep.block_odd_blk _ _ c3 (ParentInterior.odd_inner_of_not_threes w hn3)
  obtain ⟨⟨qw', hqw, hql⟩, hjQ⟩ := HorizontalStep.block_even_blk _ _ c4
    (ParentInterior.even_inner_of_not_twos w hn2) (parentsAt_valid w).even_parity
  have hc := (RegisterLink.childPQ_eq w).2
  simp only [hWordOf, if_true] at hz
  rw [hc] at hz
  rw [hpw] at hpl hjP hIP
  rw [hqw] at hql hjQ hIQ
  unfold childWords at hz
  rw [hpw, hqw] at hz
  by_cases h : w.count Digit.one % 2 = 0
  · have hph : JointFamily.W1Odd w = false := by simp [JointFamily.W1Odd, phase, h]
    rw [if_pos h] at hz
    rcases (HorizontalGlue.mem_junction qw' pw' hql z).1 hz with h1 | ⟨y, hy, rfl⟩
    · left
      simp only [q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false, Standard.mem_shift, sub_zero]
      exact hIQ z h1
    · right
      simp only [q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false, Standard.mem_shift, JointFamily.vQ1]
      rw [hjQ, add_sub_cancel_right]
      exact hIP y hy
  · have hph : JointFamily.W1Odd w = true := by
      have h1 : w.count Digit.one % 2 = 1 := by omega
      simp [JointFamily.W1Odd, phase, h1]
    rw [if_neg h] at hz
    rcases (HorizontalGlue.mem_junction pw' qw' hpl z).1 hz with h1 | ⟨y, hy, rfl⟩
    · right
      simp only [q0Off, SurgicalDict.offsetQ0, hph, if_true, Standard.mem_shift, sub_zero]
      exact hIP z h1
    · left
      simp only [q0Off, SurgicalDict.offsetQ0, hph, if_true, Standard.mem_shift, JointFamily.vP1]
      rw [hjP, add_sub_cancel_right]
      exact hIQ y hy

/-! ### The pieces shared by the even L-correction and the even tile decomposition -/

open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue
open FLatticePaper.Tiles.SurgicalWeak (regOdo WeakData regsAt)

/-- The value of the glued odometer on a piece, outside its exceptional points: the value of the piece plus its constant. -/
theorem glued_val (ps : List Piece) (κ : ℕ → ℤ) (hag : PiecesAgree ps κ) (i : ℕ) (p : Piece) (hi : ps[i]? = some p)
    (x : Site) (hx : x ∈ p.placed) (hxe : x ∉ p.exc) : (gluedOdo ps κ).val x = pieceVal p x + κ i := by
  have h : ∃ (i : ℕ) (p : Piece), ps[i]? = some p ∧ x ∈ p.placed ∧ x ∉ p.exc := ⟨i, p, hi, hx, hxe⟩
  simp only [gluedOdo, dif_pos h]
  obtain ⟨hj, hjx, hjxe⟩ := Classical.choose_spec (Classical.choose_spec h)
  exact hag _ i _ p hj hi x hjx hx hjxe hxe

/-- The value of an odometer respecting a decomposition on one of its pieces: the value of the piece plus a constant. -/
theorem respects_val (o : PartialOdometer) (ps : List Piece) (h : RespectsPieces o ps) (i : ℕ) (p : Piece)
    (hi : ps[i]? = some p) : ∃ b : ℤ, ∀ x ∈ p.placed, x ∉ p.exc → o.val x = pieceVal p x + b := by
  obtain ⟨b, hb⟩ := h.2 p (List.mem_of_getElem? hi)
  exact ⟨b, fun x hx hxe => by rw [hb x hx hxe]; rfl⟩

theorem trailing_zero_strip (w : Word) (h : trailingCount Digit.three w = 0) : stripTrailing Digit.three w = w := by
  simp [stripTrailing, h]

/-- The bridge of the even L-correction is placed at the copy `q1Plus` (`+`) or `q1Minus` (`-`) of the even child. -/
theorem bridge_off (w : Word) (plus s2 : Bool) :
    evenLInitOff w plus + altOff w (evenKCoeff (W1Odd w) plus s2).2.1 = q0Off w (if plus then .q1Plus else .q1Minus) := by
  cases plus <;> cases h : W1Odd w <;>
    simp only [evenLInitOff, evenKCoeff, q0Off, SurgicalDict.offsetQ0, h, altOff, SurgicalAlt.coeffOff, if_true,
      if_false, Bool.false_eq_true] <;>
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> ring

/-- The affine factor of the bridge is that of the copy `q1Plus` (`+`) or `q1Minus` (`-`). -/
theorem bridge_aff (w : Word) (plus s2 : Bool) :
    evenLInitAff w plus + altAff w (evenKCoeff (W1Odd w) plus s2).2.1 = q0Aff w (if plus then .q1Plus else .q1Minus) := by
  cases plus <;> cases h : W1Odd w <;>
    simp only [evenLInitAff, evenKCoeff, q0Aff, h, altAff, SurgicalAlt.coeffAffine, aP2, pairAffine, offsetA, if_true,
      if_false, Bool.false_eq_true] <;>
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

/-- The first two pieces of the even L-correction of a word that is not a base word and does not end in `3`: the stem, the odd
register at the initial copy, and the bridge, the even register at `q1Plus` (`+`) or `q1Minus` (`-`). -/
theorem evenL_first (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer) (w : Word) (hw : ¬ IsBase w)
    (hk : trailingCount Digit.three w = 0) (plus elong : Bool) :
    (evenLPieces S pOdd pEven aOdd aEven w plus elong)[0]? =
        some (stdPiece (regOdo S pOdd pEven (regsAt w).1 true) (evenLInitOff w plus) (evenLInitAff w plus)) ∧
      (evenLPieces S pOdd pEven aOdd aEven w plus elong)[1]? =
        some (stdPiece (regOdo S pOdd pEven (regsAt w).2 false) (q0Off w (if plus then .q1Plus else .q1Minus))
          (q0Aff w (if plus then .q1Plus else .q1Minus))) := by
  have hpre := trailing_zero_strip w hk
  have hd : (!w.isEmpty && w.all (fun d => decide (d = Digit.two))) = false := by
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hw (Or.inr (Or.inr hc.2))
  simp only [evenLPieces, hk, hpre, hd, Nat.cast_zero, zero_smul, zero_add, Bool.false_and, Bool.false_eq_true, if_false,
    List.range_one, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getElem?_cons_zero,
    List.getElem?_cons_succ]
  refine ⟨?_, ?_⟩
  · simp [stdPiece, altOff, altAff, SurgicalAlt.coeffOff, SurgicalAlt.coeffAffine]
  · rw [bridge_off, bridge_aff]

/-! ### Agreement on the side from two shared pieces -/

theorem mem_pieceUnion_of {ps : List Piece} {i : ℕ} {p : Piece} (hi : ps[i]? = some p) {x : Site} (hx : x ∈ p.placed) :
    x ∈ pieceUnion ps :=
  mem_pieceUnion.2 ⟨p, List.mem_of_getElem? hi, hx⟩

/-- **Two shared pieces fix the constant.** If two pieces without exceptional points belong to both decompositions and meet,
the glued odometer of the first decomposition and an odometer respecting the second differ by one constant on any set covered by
the two pieces. -/
theorem agree_two (ps qs : List Piece) (κ : ℕ → ℤ) (hag : PiecesAgree ps κ) (o : PartialOdometer) (ho : RespectsPieces o qs)
    (pA pB : Piece) (i j i' j' : ℕ) (hA : ps[i]? = some pA) (hB : ps[j]? = some pB) (hA' : qs[i']? = some pA)
    (hB' : qs[j']? = some pB) (heA : pA.exc = ∅) (heB : pB.exc = ∅) (z : Site) (hzA : z ∈ pA.placed)
    (hzB : z ∈ pB.placed) (Sd : Set Site) (hS : ∀ x ∈ Sd, x ∈ pA.placed ∨ x ∈ pB.placed) :
    ∃ c : ℤ, ∀ x ∈ Sd, x ∈ (gluedOdo ps κ).dom ∧ x ∈ o.dom ∧ (gluedOdo ps κ).val x = o.val x + c := by
  obtain ⟨bA, hbA⟩ := respects_val o qs ho i' pA hA'
  obtain ⟨bB, hbB⟩ := respects_val o qs ho j' pB hB'
  have nA : ∀ x, x ∉ pA.exc := fun x => by rw [heA]; exact Set.notMem_empty x
  have nB : ∀ x, x ∉ pB.exc := fun x => by rw [heB]; exact Set.notMem_empty x
  have e1 := glued_val ps κ hag i pA hA z hzA (nA z)
  have e2 := glued_val ps κ hag j pB hB z hzB (nB z)
  have e3 := hbA z hzA (nA z)
  have e4 := hbB z hzB (nB z)
  refine ⟨κ i - bA, fun x hx => ?_⟩
  have hdo : o.dom = pieceUnion qs := ho.1
  rcases hS x hx with h | h
  · refine ⟨mem_pieceUnion_of hA h, hdo ▸ mem_pieceUnion_of hA' h, ?_⟩
    rw [glued_val ps κ hag i pA hA x h (nA x), hbA x h (nA x)]
    ring
  · refine ⟨mem_pieceUnion_of hB h, hdo ▸ mem_pieceUnion_of hB' h, ?_⟩
    rw [glued_val ps κ hag j pB hB x h (nB x), hbB x h (nB x)]
    linarith

open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.WeakStepPaper (paperS regsAt_tiles)

theorem mem_placed_of (p : Piece) (x : Site) (h : x - p.off ∈ p.odo.dom) : x ∈ p.placed :=
  Finset.mem_image.2 ⟨x - p.off, h, sub_add_cancel x p.off⟩

/-- **The bottom side of the `+` even L-correction** (`lemma:l_correc_properties` (2), horizontal part, `k = 0`): for a word that
is not a base word and does not end in `3`, the glued L-corrected odometer and the tile odometer of the even child differ by one
constant on the bottom string of the even child. The stem and the bridge are the copies `p1DPlus` and `q1Plus` of the even child's
decomposition; they cover the bottom string (`bottom_even_copies`) and meet at the end of the first one (`v_{q_1,1}` or
`v_{p_1,1}`, by the corner values of the registers). -/
theorem evenL_bottom (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word) (hgood : GoodBelow D f w.length)
    (hw : ¬ IsBase w) (hk : trailingCount Digit.three w = 0) (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f w) w wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.evenPs D f w true elong) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus),
      x ∈ (gluedOdo (LStepAssembly.evenPs D f w true elong) κ).dom ∧ x ∈ tev.dom ∧
        (gluedOdo (LStepAssembly.evenPs D f w true elong) κ).val x = tev.val x + c := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase w hw
  have hl1 : u1.length < w.length := regsAt_lt w u1 (Or.inl (by rw [hreg]))
  have hl2 : u2.length < w.length := regsAt_lt w u2 (Or.inr (by rw [hreg]))
  have hb1 : below f w u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f w u2 = f u2 := by simp only [below, if_pos hl2]
  have hp := (WeakStepAssembly.regsAt_parents w).1 u1 (by rw [hreg])
  have hq := (WeakStepAssembly.regsAt_parents w).2 u2 (by rw [hreg])
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
  have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
  obtain ⟨-, -, -, ⟨h0P, -⟩, -, -, ⟨hXP, -⟩, -⟩ :=
    TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (WeakStepAssembly.slice_respects D f u1 hS1).1
  obtain ⟨-, -, -, ⟨h0Q, -⟩, -, -, ⟨hXQ, -⟩, -⟩ :=
    TileTranslationStd.stdCorners_even u2 (f u2).tEven (WeakStepAssembly.slice_respects D f u2 hS2).2
  have hTP : (stateAt w).tOdd = oddTile u1 := (regsAt_tiles w).1 u1 (by rw [hreg])
  have hTQ : (stateAt w).tEven = evenTile u2 := (regsAt_tiles w).2.2.1 u2 (by rw [hreg])
  have hPd : (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).1 true).dom =
      (stateAt w).tOdd := by
    rw [hreg]; simp only [regOdo, hb1]; rw [hdO, hTP]
  have hQd : (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).2 false).dom =
      (stateAt w).tEven := by
    rw [hreg]; simp only [regOdo, hb2]; rw [hdE, hTQ]
  obtain ⟨-, hnb, -⟩ := hT
  have hRt := (hnb hw).2.1
  obtain ⟨hA, hB⟩ := evenL_first D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) w hw hk true elong
  have hA' : (tileEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).lOdd) w)[0]? = some (stdPiece (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt w).1 true) (evenLInitOff w true) (evenLInitAff w true)) := by
    simp [tileEvenPieces, evenLInitOff, evenLInitAff]
  have hB' : (tileEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
      (fun u => (below f w u).lOdd) w)[4]? = some (stdPiece (regOdo D.S (fun u => (below f w u).tOdd)
        (fun u => (below f w u).tEven) (regsAt w).2 false) (q0Off w (if true then .q1Plus else .q1Minus))
        (q0Aff w (if true then .q1Plus else .q1Minus))) := by
    simp [tileEvenPieces]
  have hside : ∀ x ∈ {x : Site | x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus)},
      x ∈ (stdPiece (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).1 true)
        (evenLInitOff w true) (evenLInitAff w true)).placed ∨
      x ∈ (stdPiece (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).2 false)
        (q0Off w (if true then .q1Plus else .q1Minus)) (q0Aff w (if true then .q1Plus else .q1Minus))).placed := by
    intro x hx
    have hx' : x ∈ stringSites false false (hWordOf w true) :=
      (StdPseudoAnchoredSets.placed_hStringAt_iff (hWordOf w true) x).1 hx
    rcases bottom_even_copies w hw x hx' with h | h
    · right
      refine mem_placed_of _ x ?_
      rw [Standard.mem_shift] at h
      simp only [stdPiece, if_true]
      rw [hQd]; exact h
    · left
      refine mem_placed_of _ x ?_
      rw [Standard.mem_shift] at h
      simp only [stdPiece, evenLInitOff, if_true]
      rw [hPd]; exact h
  have hz : ∃ z, z ∈ (stdPiece (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).1 true)
        (evenLInitOff w true) (evenLInitAff w true)).placed ∧
      z ∈ (stdPiece (regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (regsAt w).2 false)
        (q0Off w (if true then .q1Plus else .q1Minus)) (q0Aff w (if true then .q1Plus else .q1Minus))).placed := by
    rw [hdO, ← hTP] at h0P hXP
    rw [hdE, ← hTQ] at h0Q hXQ
    cases hph : W1Odd w
    · refine ⟨vQ1 w, mem_placed_of _ _ ?_, mem_placed_of _ _ ?_⟩
      · simp only [stdPiece, evenLInitOff, if_true, q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false,
          sub_self]
        rw [hPd]; exact h0P
      · simp only [stdPiece, if_true, q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false, sub_zero]
        rw [hQd, vQ1, hq]; exact hXQ
    · refine ⟨vP1 w, mem_placed_of _ _ ?_, mem_placed_of _ _ ?_⟩
      · simp only [stdPiece, evenLInitOff, if_true, q0Off, SurgicalDict.offsetQ0, hph, sub_zero]
        rw [hPd, vP1, hp]; exact hXP
      · simp only [stdPiece, if_true, q0Off, SurgicalDict.offsetQ0, hph, sub_self]
        rw [hQd]; exact h0Q
  obtain ⟨z, hzA, hzB⟩ := hz
  exact agree_two _ _ κ hag tev hRt _ _ 0 1 0 4 hA hB hA' hB' rfl rfl z hzA hzB _ hside

/-! ### Respecting a string is kept by adding a constant -/

theorem slopeOf_add_const (f : Site → ℤ) (T : List Site) (c : ℤ) : slopeOf (fun x => f x + c) T = slopeOf f T := by
  simp only [slopeOf, Int.cast_add, add_sub_add_right_eq_sub]

theorem mem_placedSites_of_dom (F : PTFamily) (k : ℕ) (hk : k < F.n) (x : GInt) (hx : x ∈ F.dom k) :
    x ∈ placedSites F.ts := by
  simp only [PTFamily.dom, PTFamily.tile] at hx
  simp only [placedSites, List.mem_flatMap]
  refine ⟨F.ts.getD k (ZTile.zero, (0 : GInt)), ?_, hx⟩
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- An odometer equal to one respecting a string plus a constant, on the sites of the string, respects it too. -/
theorem respectsTiles_add_const (o : Orientation) (rev : Bool) (ts : List (ZTile × GInt)) (S S' : GInt → ℤ) (c : ℤ)
    (h : RespectsTiles o rev ts S) (hS : ∀ x ∈ placedSites ts, S' x = S x + c) : RespectsTiles o rev ts S' := by
  obtain ⟨F, hts, hval, hresp⟩ := h
  have hodo : ∀ k, (⟨F.ts, F.a, fun k => F.b k + c⟩ : PTFamily).odo k = fun x => F.odo k x + c := by
    intro k; funext x; simp only [PTFamily.odo, PTFamily.tile]; ring
  refine ⟨⟨F.ts, F.a, fun k => F.b k + c⟩, hts, fun k hk x hx => ?_, fun k hk => ?_⟩
  · rw [hodo k]
    show S' x = F.odo k x + c
    rw [← hval k hk x hx]
    exact hS x (hts ▸ mem_placedSites_of_dom F k hk x hx)
  · obtain ⟨h1, h2⟩ := hresp k hk
    refine ⟨?_, fun hne x hx y hy hxy => ?_⟩
    · rw [hodo, hodo, slopeOf_add_const, slopeOf_add_const]
      exact h1
    · obtain ⟨h3, h4⟩ := h2 hne x hx y hy hxy
      refine ⟨fun ho => ?_, fun ho => ?_⟩
      · rw [hodo, hodo]
        have := h3 ho
        simp only [] at this ⊢
        linarith
      · rw [hodo, hodo]
        have := h4 ho
        simp only [] at this ⊢
        linarith

/-- **The bottom side of the `+` even L-correction**, both parts of `LSidesAgree` for the bottom string: the glued odometer
respects the bottom string of the even child and agrees there with its tile odometer up to one constant (words that are not base
words and do not end in `3`). -/
theorem evenL_bottom_side (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (w : Word)
    (hgood : GoodBelow D f w.length) (hw : ¬ IsBase w) (hk : trailingCount Digit.three w = 0)
    (wo we wao wae tod tev aod aev : PartialOdometer) (hT : TilePart D (below f w) w wo we wao wae tod tev aod aev)
    (elong : Bool) (κ : ℕ → ℤ) (hag : PiecesAgree (LStepAssembly.evenPs D f w true elong) κ) :
    RespectsTiles (sideOrient .hPlus).1 (sideOrient .hPlus).2 (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus)
        (gluedOdo (LStepAssembly.evenPs D f w true elong) κ).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus),
        x ∈ (gluedOdo (LStepAssembly.evenPs D f w true elong) κ).dom ∧ x ∈ tev.dom ∧
          (gluedOdo (LStepAssembly.evenPs D f w true elong) κ).val x = tev.val x + c := by
  obtain ⟨c, hc⟩ := evenL_bottom D hS f w hgood hw hk wo we wao wae tod tev aod aev hT elong κ hag
  obtain ⟨-, -, -, -, -, hR, -⟩ := hT
  exact ⟨respectsTiles_add_const _ _ _ _ _ c hR.2.1 (fun x hx => (hc x hx).2.2), c, hc⟩

end FLatticePaper.Tiles.LSidesEven
