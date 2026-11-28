import FLatticePaper.Tiles.LSidesEven
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.ReflectedCoverConverse

/-! # The bottom side of the `+` even L-correction after trailing `3`s

For `w = pre 3^k` (`pre` not a base word and not ending in `3`), the even child of `w` contains, through the Q-copies of the nested
decompositions of the even children of `pre 3^i`, the copies of the odd register of `pre` at the nested offsets (the stems of the
L-correction) and the copy of the even register of `pre` (its bridge); they cover the bottom string. With affine factor `0`
throughout, the tile odometer of the child and the glued L-corrected odometer differ by one constant on each copy, and the
consecutive copies meet at corner points, so by one constant on the bottom string. -/

namespace FLatticePaper.Tiles.LSidesEvenK

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard (IsBase stateAt oddTile evenTile shift)
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointGlue (PiecesAgree gluedOdo)

/-! ### Copies placed with affine factor `0` -/

/-- `o` contains the copy of `q` placed at `s` with affine factor `0`, up to one constant. -/
def PlacedEq (o q : PartialOdometer) (s : Site) : Prop :=
  ∃ b : ℤ, ∀ y ∈ q.dom, y + s ∈ o.dom ∧ o.val (y + s) = q.val y + b

theorem placedEq_trans {o q r : PartialOdometer} {s t : Site} (h1 : PlacedEq o q s) (h2 : PlacedEq q r t) :
    PlacedEq o r (t + s) := by
  obtain ⟨b1, h1⟩ := h1
  obtain ⟨b2, h2⟩ := h2
  refine ⟨b2 + b1, fun y hy => ?_⟩
  obtain ⟨hq, hv⟩ := h2 y hy
  obtain ⟨ho, hv'⟩ := h1 (y + t) hq
  rw [← add_assoc]
  exact ⟨ho, by rw [hv', hv]; ring⟩

/-- A piece of affine factor `0` of a decomposition that `o` respects is placed in `o`. -/
theorem placedEq_of_respects {o : PartialOdometer} {ps : List Piece} (h : RespectsPieces o ps) {i : ℕ}
    {q : PartialOdometer} {s a : Site} (hi : ps[i]? = some (stdPiece q s a)) (ha : a = 0) : PlacedEq o q s := by
  obtain ⟨b, hb⟩ := h.2 _ (List.mem_of_getElem? hi)
  refine ⟨b, fun y hy => ?_⟩
  have hp : y + s ∈ (stdPiece q s a).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
  refine ⟨h.1 ▸ LSidesEven.mem_pieceUnion_of hi hp, ?_⟩
  rw [hb (y + s) hp (by simp [stdPiece]), ha]
  simp [stdPiece, dotS]

/-! ### The bottom string of the even child, by parent words -/

/-- **The bottom string of the even child splits into the parent words**: each point lies, after the offset of its copy, on the
even parent word at `q1Plus` or on the odd parent word at `p1DPlus`. -/
theorem bottom_even_split (w : Word) (hw : ¬ IsBase w) (z : GInt) (hz : z ∈ stringSites false false (hWordOf w true)) :
    z - q0Off w .q1Plus ∈ stringSites false false (quadAt [] w).parentQ ∨
      z - q0Off w .p1DPlus ∈ stringSites false false (quadAt [] w).parentP := by
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
  rw [hpw] at hpl hjP
  rw [hqw] at hql hjQ
  unfold childWords at hz
  rw [hpw, hqw] at hz
  rw [hpw, hqw]
  by_cases h : w.count Digit.one % 2 = 0
  · have hph : W1Odd w = false := by simp [W1Odd, phase, h]
    rw [if_pos h] at hz
    rcases (HorizontalGlue.mem_junction qw' pw' hql z).1 hz with h1 | ⟨y, hy, rfl⟩
    · left
      simp only [q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false, sub_zero]
      exact h1
    · right
      simp only [q0Off, SurgicalDict.offsetQ0, hph, Bool.false_eq_true, if_false, vQ1]
      rw [hjQ, add_sub_cancel_right]
      exact hy
  · have hph : W1Odd w = true := by
      have h1 : w.count Digit.one % 2 = 1 := by omega
      simp [W1Odd, phase, h1]
    rw [if_neg h] at hz
    rcases (HorizontalGlue.mem_junction pw' qw' hpl z).1 hz with h1 | ⟨y, hy, rfl⟩
    · right
      simp only [q0Off, SurgicalDict.offsetQ0, hph, if_true, sub_zero]
      exact h1
    · left
      simp only [q0Off, SurgicalDict.offsetQ0, hph, if_true, vP1]
      rw [hjP, add_sub_cancel_right]
      exact hy

/-- After a `3` the even parent word is the even child word of the prefix. -/
theorem parentQ_snoc_three (v : Word) : (quadAt [] (v ++ [Digit.three])).parentQ = hWordOf v true := by
  simp [hWordOf, quadAt_append_singleton, WordQuad.step]

/-! ### Along trailing `3`s -/

open FLatticePaper.Tiles.SurgicalWeak (regsAt regOdo)

theorem regsAt_snoc_three (v : Word) : regsAt (v ++ [Digit.three]) = ((regsAt v).1, some v) := by
  rw [WeakStepPaper.regsAt_snoc]; rfl

theorem W1Odd_snoc_three (v : Word) : W1Odd (v ++ [Digit.three]) = W1Odd v := by
  simp [W1Odd, phase, List.count_append]

theorem vP1_snoc_three (v : Word) : vP1 (v ++ [Digit.three]) = vP1 v := by
  simp [vP1, CeilWords.parentsAt_snoc_three]

theorem vQ1_snoc_three (v : Word) : vQ1 (v ++ [Digit.three]) = vQ1 v + vP1 v := by
  simp only [vQ1, vP1, CeilWords.parentsAt_snoc_three, Parents.current, Parents.combine]
  ext <;> simp [texV1Odd, texV1Even] <;> ring

theorem notBase_snoc_three (v : Word) (hv : ¬ IsBase v) : ¬ IsBase (v ++ [Digit.three]) := by
  rintro (h | h | h)
  · simp at h
  · exact hv (Or.inr (Or.inl fun d hd => h d (List.mem_append_left _ hd)))
  · exact absurd (h Digit.three (by simp)) (by decide)

/-- The word `pre 3^k`. -/
abbrev wk (pre : Word) (k : ℕ) : Word := pre ++ List.replicate k Digit.three

theorem wk_succ (pre : Word) (k : ℕ) : wk pre (k + 1) = wk pre k ++ [Digit.three] := by
  simp [wk, List.replicate_succ', List.append_assoc]

theorem wk_trailing (pre : Word) (h0 : trailingCount Digit.three pre = 0) (k : ℕ) :
    trailingCount Digit.three (wk pre k) = k ∧ stripTrailing Digit.three (wk pre k) = pre := by
  induction k with
  | zero =>
    simp only [wk, List.replicate_zero, List.append_nil]
    exact ⟨h0, LSidesEven.trailing_zero_strip pre h0⟩
  | succ k ih =>
    rw [wk_succ, JointRot.trailingCount_snoc, JointRot.stripTrailing_snoc, if_pos rfl, if_pos rfl]
    exact ⟨by rw [ih.1], ih.2⟩

theorem wk_facts (pre : Word) (hpre : ¬ IsBase pre) (k : ℕ) :
    ¬ IsBase (wk pre k) ∧ (regsAt (wk pre k)).1 = (regsAt pre).1 ∧ W1Odd (wk pre k) = W1Odd pre ∧
      vP1 (wk pre k) = vP1 pre ∧ vQ1 (wk pre k) = vQ1 pre + (k : ℤ) • vP1 pre := by
  induction k with
  | zero => simp [wk, hpre]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    rw [wk_succ]
    refine ⟨notBase_snoc_three _ h1, by rw [regsAt_snoc_three, h2], by rw [W1Odd_snoc_three, h3],
      by rw [vP1_snoc_three, h4], ?_⟩
    rw [vQ1_snoc_three, h5, h4]
    push_cast
    rw [add_smul, one_smul]
    abel

/-! ### The nested copies -/

/-- The offset of the stem `m` (the copy of the odd register of `pre` in the nested decompositions of `pre 3^k`). -/
def nest (pre : Word) (k m : ℕ) : Site :=
  if W1Odd pre then (m : ℤ) • vP1 pre else vQ1 pre + ((k : ℤ) - m) • vP1 pre

/-- The offset of the bridge (the copy of the even register of `pre`). -/
def bridgeAt (pre : Word) (k : ℕ) : Site := if W1Odd pre then ((k : ℤ) + 1) • vP1 pre else 0

theorem tEP_entry0 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileEvenPieces S pO pE lO v)[0]? =
      some (stdPiece (regOdo S pO pE (regsAt v).1 true) (q0Off v .p1DPlus) (q0Aff v .p1DPlus)) := by
  simp [tileEvenPieces]

theorem tEP_entry4 (S : SurgicalWeak.WeakData) (pO pE : Word → PartialOdometer) (lO : Word → Bool → Bool → PartialOdometer)
    (v : Word) : (tileEvenPieces S pO pE lO v)[4]? =
      some (stdPiece (regOdo S pO pE (regsAt v).2 false) (q0Off v .q1Plus) (q0Aff v .q1Plus)) := by
  simp [tileEvenPieces]

theorem q0Aff_zero (v : Word) : q0Aff v .p1DPlus = 0 ∧ q0Aff v .q1Plus = 0 := by
  cases h : W1Odd v <;> simp [q0Aff, h, pairAffine, offsetA]

theorem nest_zero (pre : Word) : nest pre 0 0 = q0Off pre .p1DPlus ∧ bridgeAt pre 0 = q0Off pre .q1Plus := by
  cases h : W1Odd pre <;> simp [nest, bridgeAt, q0Off, SurgicalDict.offsetQ0, h]

theorem nest_step (pre w : Word) (k : ℕ) (ho : W1Odd w = W1Odd pre) (hp : vP1 w = vP1 pre)
    (hq : vQ1 w = vQ1 pre + ((k + 1 : ℕ) : ℤ) • vP1 pre) :
    nest pre (k + 1) 0 = q0Off w .p1DPlus ∧ (∀ m, nest pre k m + q0Off w .q1Plus = nest pre (k + 1) (m + 1)) ∧
      bridgeAt pre k + q0Off w .q1Plus = bridgeAt pre (k + 1) := by
  cases h : W1Odd pre
  · refine ⟨?_, fun m => ?_, ?_⟩ <;>
      simp only [nest, bridgeAt, q0Off, SurgicalDict.offsetQ0, ho, h, hp, hq, Bool.false_eq_true, if_false, add_zero]
    · push_cast; ring_nf
    · push_cast; congr 1; ring_nf
  · refine ⟨?_, fun m => ?_, ?_⟩ <;>
      simp only [nest, bridgeAt, q0Off, SurgicalDict.offsetQ0, ho, h, hp, if_true]
    · simp
    · push_cast; rw [add_smul, one_smul]
    · push_cast; rw [add_smul (_ + _) 1, one_smul]

open FLatticePaper.Tiles.JointInduction (GoodBelow regsAt_lt)
open FLatticePaper.Tiles.WeakStepPaper (paperS regsAt_tiles)

/-- **The nested copies of `pre 3^k`**: an odometer respecting the even decomposition of `pre 3^k` contains, with affine factor
`0`, the odd register of `pre` at each stem `nest pre k m` (`m ≤ k`) and the even register of `pre` at `bridgeAt pre k`, and these
copies cover the bottom string of the even child. -/
theorem nested (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre) (u1 u2 : Word)
    (hreg : regsAt pre = (some u1, some u2)) :
    ∀ (k : ℕ) (o : PartialOdometer), GoodBelow D f (wk pre k).length →
      RespectsPieces o (tileEvenPieces D.S (fun u => (below f (wk pre k) u).tOdd) (fun u => (below f (wk pre k) u).tEven)
        (fun u => (below f (wk pre k) u).lOdd) (wk pre k)) →
      (∀ m ≤ k, PlacedEq o (f u1).tOdd (nest pre k m)) ∧ PlacedEq o (f u2).tEven (bridgeAt pre k) ∧
        ∀ z ∈ stringSites false false (hWordOf (wk pre k) true),
          (∃ m ≤ k, z - nest pre k m ∈ (f u1).tOdd.dom) ∨ z - bridgeAt pre k ∈ (f u2).tEven.dom := by
  have hl2 : u2.length < pre.length := regsAt_lt pre u2 (Or.inr (by rw [hreg]))
  intro k
  induction k with
  | zero =>
    intro o hgood hR
    have hw0 : wk pre 0 = pre := by simp [wk]
    rw [hw0] at hR hgood ⊢
    have hl1 : u1.length < pre.length := regsAt_lt pre u1 (Or.inl (by rw [hreg]))
    have hb1 : below f pre u1 = f u1 := by simp only [below, if_pos hl1]
    have hb2 : below f pre u2 = f u2 := by simp only [below, if_pos hl2]
    obtain ⟨z0, b0⟩ := nest_zero pre
    obtain ⟨a0, a4⟩ := q0Aff_zero pre
    have e0 := tEP_entry0 D.S (fun u => (below f pre u).tOdd) (fun u => (below f pre u).tEven)
      (fun u => (below f pre u).lOdd) pre
    have e4 := tEP_entry4 D.S (fun u => (below f pre u).tOdd) (fun u => (below f pre u).tEven)
      (fun u => (below f pre u).lOdd) pre
    rw [hreg] at e0 e4
    simp only [regOdo, hb1, hb2] at e0 e4
    obtain ⟨hS1, -⟩ := hgood u1 hl1
    obtain ⟨hS2, -⟩ := hgood u2 hl2
    have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
    have hdE : (f u2).tEven.dom = evenTile u2 := by rw [(WeakStepAssembly.slice_domains D f u2 hS2).2, hS]; rfl
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · obtain rfl : m = 0 := by omega
      rw [z0]; exact placedEq_of_respects hR e0 a0
    · rw [b0]; exact placedEq_of_respects hR e4 a4
    · obtain ⟨-, -, hIP, hIQ⟩ := LSidesEven.inv_every pre
      rcases bottom_even_split pre hpre z hz with h | h
      · right
        rw [b0, hdE, ← (regsAt_tiles pre).2.2.1 u2 (by rw [hreg])]
        exact hIQ _ h
      · left
        refine ⟨0, le_rfl, ?_⟩
        rw [z0, hdO, ← (regsAt_tiles pre).1 u1 (by rw [hreg])]
        exact hIP _ h
  | succ k ih =>
    intro o hgood hR
    obtain ⟨hnb, hr1, hph, hvp, hvq⟩ := wk_facts pre hpre (k + 1)
    obtain ⟨hnb', -, -, -, -⟩ := wk_facts pre hpre k
    have hws := wk_succ pre k
    have hlt : (wk pre k).length < (wk pre (k + 1)).length := by rw [hws]; simp
    have hr2 : (regsAt (wk pre (k + 1))).2 = some (wk pre k) := by rw [hws, regsAt_snoc_three]
    have hr1' : (regsAt (wk pre (k + 1))).1 = some u1 := by rw [hr1, hreg]
    have hl1 : u1.length < (wk pre (k + 1)).length := regsAt_lt _ u1 (Or.inl hr1')
    have hb1 : below f (wk pre (k + 1)) u1 = f u1 := by simp only [below, if_pos hl1]
    have hbk : below f (wk pre (k + 1)) (wk pre k) = f (wk pre k) := by simp only [below, if_pos hlt]
    obtain ⟨s0, sm, sb⟩ := nest_step pre (wk pre (k + 1)) k hph hvp hvq
    obtain ⟨a0, a4⟩ := q0Aff_zero (wk pre (k + 1))
    have e0 := tEP_entry0 D.S (fun u => (below f (wk pre (k + 1)) u).tOdd) (fun u => (below f (wk pre (k + 1)) u).tEven)
      (fun u => (below f (wk pre (k + 1)) u).lOdd) (wk pre (k + 1))
    have e4 := tEP_entry4 D.S (fun u => (below f (wk pre (k + 1)) u).tOdd) (fun u => (below f (wk pre (k + 1)) u).tEven)
      (fun u => (below f (wk pre (k + 1)) u).lOdd) (wk pre (k + 1))
    rw [hr1'] at e0
    rw [hr2] at e4
    simp only [regOdo, hb1, hbk] at e0 e4
    have hP0 := placedEq_of_respects hR e0 a0
    have hQ := placedEq_of_respects hR e4 a4
    have hgood' : GoodBelow D f (wk pre k).length := fun u hu => hgood u (lt_trans hu hlt)
    have hRk : RespectsPieces (f (wk pre k)).tEven (tileEvenPieces D.S (fun u => (below f (wk pre k) u).tOdd)
        (fun u => (below f (wk pre k) u).tEven) (fun u => (below f (wk pre k) u).lOdd) (wk pre k)) :=
      (((hgood (wk pre k) hlt).1.2.2.1).2.1 hnb').2.1
    obtain ⟨hn, hbr, hcov⟩ := ih (f (wk pre k)).tEven hgood' hRk
    have hl1' : u1.length < pre.length := regsAt_lt pre u1 (Or.inl (by rw [hreg]))
    obtain ⟨hS1, -⟩ := hgood u1 hl1
    have hdO : (f u1).tOdd.dom = oddTile u1 := by rw [(WeakStepAssembly.slice_domains D f u1 hS1).1, hS]; rfl
    refine ⟨fun m hm => ?_, ?_, fun z hz => ?_⟩
    · rcases m with _ | m
      · rw [s0]; exact hP0
      · rw [← sm m]; exact placedEq_trans hQ (hn m (by omega))
    · rw [← sb]; exact placedEq_trans hQ hbr
    · obtain ⟨-, -, hIP, -⟩ := LSidesEven.inv_every (wk pre (k + 1))
      rcases bottom_even_split (wk pre (k + 1)) hnb z hz with h | h
      · rw [hws, parentQ_snoc_three, ← hws] at h
        rcases hcov _ h with ⟨m, hm, hm'⟩ | hb
        · left
          refine ⟨m + 1, by omega, ?_⟩
          rw [← sm m]; convert hm' using 1; abel
        · right
          rw [← sb]; convert hb using 1; abel
      · left
        refine ⟨0, by omega, ?_⟩
        rw [s0, hdO, ← (regsAt_tiles _).1 u1 hr1']
        exact hIP _ h

/-! ### The stems and the bridge of the `+` even L-correction -/

/-- The first `k + 2` entries of the `+` even L-correction of `pre 3^k` (`pre` not a base word): the stems, copies of the odd
register of `pre` at `nest pre k m`, and the bridge, the even register of `pre` at `bridgeAt pre k`, all with affine factor `0`. -/
theorem evenL_stems (S : SurgicalWeak.WeakData) (pO pE aO aE : Word → PartialOdometer) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.three pre = 0) (k : ℕ) (elong : Bool) :
    (∀ m ≤ k, (evenLPieces S pO pE aO aE (wk pre k) true elong)[m]? =
        some (stdPiece (regOdo S pO pE (regsAt pre).1 true) (nest pre k m) 0)) ∧
      (evenLPieces S pO pE aO aE (wk pre k) true elong)[k + 1]? =
        some (stdPiece (regOdo S pO pE (regsAt pre).2 false) (bridgeAt pre k) 0) := by
  obtain ⟨htc, hst⟩ := wk_trailing pre h0 k
  obtain ⟨-, -, hph, hvp, hvq⟩ := wk_facts pre hpre k
  have hd : (!pre.isEmpty && pre.all (fun d => decide (d = Digit.two))) = false := by
    by_contra hc
    simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      decide_eq_true_eq] at hc
    exact hpre (Or.inr (Or.inr hc.2))
  have hoff : ∀ m : ℕ, evenLInitOff (wk pre k) true +
      altOff pre ((m : ℤ) • (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).1) =
        nest pre k m := by
    intro m
    rw [hph]
    cases h : W1Odd pre <;> cases decide (pre.getLast? = some Digit.two) <;>
      simp only [evenLInitOff, evenKCoeff, q0Off, SurgicalDict.offsetQ0, hph, h, hvq, hvp, altOff,
        SurgicalAlt.coeffOff, nest, if_true, if_false, Bool.false_eq_true] <;>
      ext <;> simp [vP1, vQ1] <;> ring
  have haff : ∀ m : ℕ, evenLInitAff (wk pre k) true +
      altAff pre ((m : ℤ) • (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).1) = 0 := by
    intro m
    cases h : W1Odd (wk pre k) <;> cases decide (pre.getLast? = some Digit.two) <;>
      simp [evenLInitAff, evenKCoeff, q0Aff, h, altAff, SurgicalAlt.coeffAffine, pairAffine, offsetA]
  have hboff : evenLInitOff (wk pre k) true + altOff pre ((k : ℤ) •
      (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).1 +
      (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).2.1) = bridgeAt pre k := by
    rw [hph]
    cases h : W1Odd pre <;> cases decide (pre.getLast? = some Digit.two) <;>
      simp only [evenLInitOff, evenKCoeff, q0Off, SurgicalDict.offsetQ0, hph, h, hvq, hvp, altOff,
        SurgicalAlt.coeffOff, bridgeAt, if_true, if_false, Bool.false_eq_true] <;>
      ext <;> simp [vP1, vQ1] <;> ring
  have hbaff : evenLInitAff (wk pre k) true + altAff pre ((k : ℤ) •
      (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).1 +
      (evenKCoeff (W1Odd (wk pre k)) true (decide (pre.getLast? = some Digit.two))).2.1) = 0 := by
    cases h : W1Odd (wk pre k) <;> cases decide (pre.getLast? = some Digit.two) <;>
      simp [evenLInitAff, evenKCoeff, q0Aff, h, altAff, SurgicalAlt.coeffAffine, pairAffine, offsetA]
  refine ⟨fun m hm => ?_, ?_⟩
  · simp only [evenLPieces, htc, hst, hd, Bool.false_and, Bool.false_eq_true, if_false, List.append_nil]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_map, List.getElem?_range (by omega : m < k + 1), Option.map_some]
    rw [hoff m, haff m]
  · simp only [evenLPieces, htc, hst, hd, Bool.false_and, Bool.false_eq_true, if_false, List.append_nil]
    rw [List.getElem?_append_left (by simp)]
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero]
    rw [hboff, hbaff]

/-! ### One constant on the bottom string -/

theorem nest_succ (pre : Word) (k m : ℕ) :
    (W1Odd pre = true → nest pre k (m + 1) = nest pre k m + vP1 pre) ∧
      (W1Odd pre = false → nest pre k m = nest pre k (m + 1) + vP1 pre) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [nest, h, if_true, if_false, Bool.false_eq_true] <;> push_cast
  · rw [add_smul, one_smul]
  · rw [show ((k : ℤ) - m) = ((k : ℤ) - (m + 1)) + 1 by ring, add_smul, one_smul]; abel

theorem bridge_rel (pre : Word) (k : ℕ) :
    (W1Odd pre = true → bridgeAt pre k = nest pre k k + vP1 pre) ∧
      (W1Odd pre = false → nest pre k k = vQ1 pre ∧ bridgeAt pre k = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [nest, bridgeAt, h, if_true, if_false, Bool.false_eq_true]
  · rw [add_smul, one_smul]
  · simp

/-- **The bottom side of the `+` even L-correction after trailing `3`s** (`lemma:l_correc_properties` (2), horizontal part):
for `w = pre 3^k` with `pre` not a base word and not ending in `3`, the glued L-corrected odometer and the tile odometer of the even
child differ by one constant on the bottom string of the child. -/
theorem evenL_bottom_k (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.three pre = 0) (k : ℕ) (hgood : GoodBelow D f (wk pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk pre k)) (wk pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.evenPs D f (wk pre k) true elong) κ) :
    ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hPlus),
      x ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).dom ∧ x ∈ tev.dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).val x = tev.val x + c := by
  obtain ⟨u1, u2, hreg⟩ := WeakStepAssembly.regsAt_nonbase pre hpre
  obtain ⟨hnb, -, -, -, -⟩ := wk_facts pre hpre k
  have hRt := (hT.2.1 hnb).2.1
  obtain ⟨hn, hbr, hcov⟩ := nested D hS f pre hpre u1 u2 hreg k tev hgood hRt
  have hl1 : u1.length < (wk pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u1 (Or.inl (by rw [hreg]))) (by simp [wk])
  have hl2 : u2.length < (wk pre k).length :=
    lt_of_lt_of_le (regsAt_lt pre u2 (Or.inr (by rw [hreg]))) (by simp [wk])
  have hb1 : below f (wk pre k) u1 = f u1 := by simp only [below, if_pos hl1]
  have hb2 : below f (wk pre k) u2 = f u2 := by simp only [below, if_pos hl2]
  obtain ⟨hLm, hLb⟩ := evenL_stems D.S (fun u => (below f (wk pre k) u).tOdd) (fun u => (below f (wk pre k) u).tEven)
    (fun u => (below f (wk pre k) u).aOdd) (fun u => (below f (wk pre k) u).aEven) pre hpre h0 k elong
  rw [hreg] at hLm hLb
  simp only [regOdo, hb1, hb2] at hLm hLb
  -- the glue and the tile odometer on a stem or the bridge
  choose! b hb using hn
  obtain ⟨bB, hbB⟩ := hbr
  have gs : ∀ m ≤ k, ∀ y ∈ (f u1).tOdd.dom,
      y + nest pre k m ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).dom ∧
        y + nest pre k m ∈ tev.dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).val (y + nest pre k m) =
          tev.val (y + nest pre k m) + (κ m - b m) := by
    intro m hm y hy
    have hp : y + nest pre k m ∈ (stdPiece (f u1).tOdd (nest pre k m) 0).placed := Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht, hv⟩ := hb m hm y hy
    refine ⟨LSidesEven.mem_pieceUnion_of (hLm m hm) hp, ht, ?_⟩
    rw [LSidesEven.glued_val _ κ hag m _ (hLm m hm) _ hp (by simp [stdPiece]), hv]
    simp [JointGlue.pieceVal, stdPiece, dotS]
  have gb : ∀ y ∈ (f u2).tEven.dom,
      y + bridgeAt pre k ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).dom ∧
        y + bridgeAt pre k ∈ tev.dom ∧
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).val (y + bridgeAt pre k) =
          tev.val (y + bridgeAt pre k) + (κ (k + 1) - bB) := by
    intro y hy
    have hp : y + bridgeAt pre k ∈ (stdPiece (f u2).tEven (bridgeAt pre k) 0).placed :=
      Finset.mem_image.2 ⟨y, hy, rfl⟩
    obtain ⟨ht, hv⟩ := hbB y hy
    refine ⟨LSidesEven.mem_pieceUnion_of hLb hp, ht, ?_⟩
    rw [LSidesEven.glued_val _ κ hag (k + 1) _ hLb _ hp (by simp [stdPiece]), hv]
    simp [JointGlue.pieceVal, stdPiece, dotS]
  -- corner points of the registers
  have hp : (parentsAt u1).current .odd = (parentsAt pre).odd :=
    ((WeakStepAssembly.regsAt_parents pre).1 u1 (by rw [hreg])).symm
  have hq : (parentsAt u2).current .even = (parentsAt pre).even :=
    ((WeakStepAssembly.regsAt_parents pre).2 u2 (by rw [hreg])).symm
  obtain ⟨hS1, -⟩ := hgood u1 hl1
  obtain ⟨hS2, -⟩ := hgood u2 hl2
  obtain ⟨αo, βo, -, hVo⟩ := TileTranslationStd.stdCorners_odd u1 (f u1).tOdd (WeakStepAssembly.slice_respects D f u1 hS1).1
  obtain ⟨αe, βe, -, hVe⟩ := TileTranslationStd.stdCorners_even u2 (f u2).tEven (WeakStepAssembly.slice_respects D f u2 hS2).2
  obtain ⟨⟨c0, -⟩, -, -, ⟨cX, -⟩, -⟩ := hVo
  obtain ⟨⟨d0, -⟩, -, -, ⟨dX, -⟩, -⟩ := hVe
  rw [hp] at cX
  rw [hq] at dX
  -- the constants agree along the stems and the bridge
  have step : ∀ m < k, κ (m + 1) - b (m + 1) = κ m - b m := by
    intro m hm
    cases h : W1Odd pre
    · have e := (nest_succ pre k m).2 h
      have g1 := gs m (by omega) 0 c0
      have g2 := gs (m + 1) (by omega) (vP1 pre) cX
      rw [zero_add, e, add_comm] at g1
      rw [g1.2.2] at g2
      linarith [g2.2.2]
    · have e := (nest_succ pre k m).1 h
      have g1 := gs m (by omega) (vP1 pre) cX
      have g2 := gs (m + 1) (by omega) 0 c0
      rw [zero_add, e, add_comm] at g2
      rw [g2.2.2] at g1
      linarith [g1.2.2]
  have hall : ∀ m ≤ k, κ m - b m = κ 0 - b 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih => rw [step m (by omega), ih (by omega)]
  have hbk : κ (k + 1) - bB = κ k - b k := by
    cases h : W1Odd pre
    · obtain ⟨e1, e2⟩ := (bridge_rel pre k).2 h
      have g1 := gs k le_rfl 0 c0
      have g2 := gb (vP1 pre + (vQ1 pre - vP1 pre)) (by
        have : vP1 pre + (vQ1 pre - vP1 pre) = vQ1 pre := by abel
        rw [this]; exact dX)
      have ex : vP1 pre + (vQ1 pre - vP1 pre) + bridgeAt pre k = 0 + nest pre k k := by
        rw [e1, e2]; abel
      rw [ex] at g2
      rw [g1.2.2] at g2
      linarith [g2.2.2]
    · have e := (bridge_rel pre k).1 h
      have g1 := gs k le_rfl (vP1 pre) cX
      have g2 := gb 0 d0
      rw [zero_add, e, add_comm] at g2
      rw [g2.2.2] at g1
      linarith [g1.2.2]
  refine ⟨κ 0 - b 0, fun x hx => ?_⟩
  have hx' := (StdPseudoAnchoredSets.placed_hStringAt_iff (hWordOf (wk pre k) true) x).1 hx
  rcases hcov x hx' with ⟨m, hm, hxm⟩ | hxb
  · have g := gs m hm _ hxm
    rw [sub_add_cancel, hall m hm] at g
    exact g
  · have g := gb _ hxb
    rw [sub_add_cancel, hbk, hall k le_rfl] at g
    exact g

/-- **The bottom side of the `+` even L-correction after trailing `3`s**, both parts of `LSidesAgree` for the bottom string: the
glued odometer respects the bottom string of the even child and agrees there with its tile odometer up to one constant. -/
theorem evenL_bottom_side_k (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (pre : Word) (hpre : ¬ IsBase pre)
    (h0 : trailingCount Digit.three pre = 0) (k : ℕ) (hgood : GoodBelow D f (wk pre k).length)
    (wo we wao wae tod tev aod aev : PartialOdometer)
    (hT : TilePart D (below f (wk pre k)) (wk pre k) wo we wao wae tod tev aod aev) (elong : Bool) (κ : ℕ → ℤ)
    (hag : PiecesAgree (LStepAssembly.evenPs D f (wk pre k) true elong) κ) :
    RespectsTiles (sideOrient .hPlus).1 (sideOrient .hPlus).2
        (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hPlus)
        (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).val ∧
      ∃ c : ℤ, ∀ x ∈ placedSites (sideString (hWordOf (wk pre k) true) (vWordOf (wk pre k) true) 0 .hPlus),
        x ∈ (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).dom ∧ x ∈ tev.dom ∧
          (gluedOdo (LStepAssembly.evenPs D f (wk pre k) true elong) κ).val x = tev.val x + c := by
  obtain ⟨c, hc⟩ := evenL_bottom_k D hS f pre hpre h0 k hgood wo we wao wae tod tev aod aev hT elong κ hag
  obtain ⟨-, -, -, -, -, hR, -⟩ := hT
  exact ⟨LSidesEven.respectsTiles_add_const _ _ _ _ _ c hR.2.1 (fun x hx => (hc x hx).2.2), c, hc⟩

/-! ### The top string is the half-turn of the bottom string -/

/-- **The top string of the even child is the half-turn of its bottom string** about the centre `D = v_1 + v_2 + 1 - i` of the
child (`ReflectedCoverConverse.placed_hRev_iff` with the end points `StdCornerAnchors.stdAnchorX_even`, `stdAnchorY_even`). -/
theorem top_iff_bottom (w : Word) (x : GInt) :
    x ∈ placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hMinus) ↔
      texV1Even ((parentsAt w).current .even) + texV2 ((parentsAt w).current .even) + ((1 : ℤ), (-1 : ℤ)) - x ∈
        placedSites (sideString (hWordOf w true) (vWordOf w true) 0 .hPlus) := by
  simp only [sideString]
  rw [ReflectedCoverConverse.placed_hRev_iff _ Letter.p (hWordOf_head_last w true).2, StdCornerAnchors.stdAnchorY_even,
    StdCornerAnchors.stdAnchorX_even]
  have e : texV2 (StandardClause.fracEven w) + ((1 : ℤ), (-2 : ℤ)) + (texV1Even (StandardClause.fracEven w) - (1, 1)) +
      ReflectedCover.shR Letter.p =
      texV1Even ((parentsAt w).current .even) + texV2 ((parentsAt w).current .even) + ((1 : ℤ), (-1 : ℤ)) := by
    simp only [StandardClause.fracEven, ReflectedCover.shR]
    ext <;> simp <;> ring
  rw [e]
  exact Iff.rfl

/-- **From the bottom side to the top side by the half-turn**: if the top set is the half-turn of the bottom set about `D`, the
`+` odometer `Lp` agrees with `T` up to a constant on the bottom, `Lp` and the `-` odometer `Lm` are related by the half-turn about
`D` with slope `a` (up to a constant), and `T` has the half-turn identity about `D` with slope `a`, then `Lm` agrees with `T` up
to a constant on the top. -/
theorem top_of_bottom (Lp Lm T : PartialOdometer) (D a : Site) (Top Bot : Set Site) (hTB : ∀ x, x ∈ Top ↔ D - x ∈ Bot)
    (hbot : ∃ c : ℤ, ∀ z ∈ Bot, z ∈ Lp.dom ∧ z ∈ T.dom ∧ Lp.val z = T.val z + c)
    (hX : ∃ K : ℤ, ∀ z ∈ Lp.dom, D - z ∈ Lm.dom ∧ 2 * (Lm.val (D - z) - Lp.val z) = dotS (-(2 : ℤ) • a) z + K)
    (hT : ∀ y ∈ T.dom, D - y ∈ T.dom ∧ 2 * (T.val (D - y) - T.val y) = dotS a D - 2 * dotS a y) :
    ∃ c : ℤ, ∀ x ∈ Top, x ∈ Lm.dom ∧ x ∈ T.dom ∧ Lm.val x = T.val x + c := by
  obtain ⟨c0, hc0⟩ := hbot
  obtain ⟨K, hK⟩ := hX
  have key : ∀ x ∈ Top, x ∈ Lm.dom ∧ x ∈ T.dom ∧ 2 * (Lm.val x - T.val x) = 2 * c0 + K - dotS a D := by
    intro x hx
    have hz := (hTB x).1 hx
    obtain ⟨hzL, hzT, hv⟩ := hc0 _ hz
    obtain ⟨m1, e1⟩ := hK _ hzL
    obtain ⟨m2, e2⟩ := hT _ hzT
    rw [sub_sub_cancel] at m1 m2 e1 e2
    refine ⟨m1, m2, ?_⟩
    simp only [dotS, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub] at e1 e2 ⊢
    linarith
  by_cases hne : ∃ x0, x0 ∈ Top
  · obtain ⟨x0, hx0⟩ := hne
    refine ⟨Lm.val x0 - T.val x0, fun x hx => ?_⟩
    obtain ⟨m1, m2, e⟩ := key x hx
    obtain ⟨-, -, e0⟩ := key x0 hx0
    exact ⟨m1, m2, by linarith⟩
  · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩

end FLatticePaper.Tiles.LSidesEvenK
