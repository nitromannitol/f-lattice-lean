import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.AltParentStair
import FLatticePaper.Tiles.AltParentBase

/-! Rotation of a comparison on the common domain of two placed pieces. -/

namespace FLatticePaper.Tiles.TileCompatRotation

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalDict SurgicalWeak SurgicalAlt JointFamily JointInduction JointGlue JointRot TileCompatInputs

/-- Row `i` of the rotated list against row `j` of the original, in a common coordinate system. -/
def Row (ps qs : List Piece) (i j : ℕ) (c γ : Site) : Prop :=
  ∀ q, qs[i]? = some q → ∃ p, ps[j]? = some p ∧ ∃ b : ℤ, ∀ x ∈ q.placed, x ∉ q.exc →
    mulI x+c ∈ p.placed ∧ mulI x+c ∉ p.exc ∧ pieceVal q x = pieceVal p (mulI x+c) - h0 x + dotS γ x + b

theorem two_rows {ps qs : List Piece} {i j a b : ℕ} {c γ : Site}
    (ri : Row ps qs i a c γ) (rj : Row ps qs j b c γ) (h : PairCompat ps a b) : PairCompat qs i j := by
  intro p q hp hq
  obtain ⟨p',hp',u,hu⟩ := ri p hp
  obtain ⟨q',hq',v,hv⟩ := rj q hq
  obtain ⟨k,hk⟩ := h p' q' hp' hq'
  refine ⟨k+u-v, fun x hx hy he hf => ?_⟩
  obtain ⟨px,pe,eq₁⟩ := hu x hx he
  obtain ⟨qx,qe,eq₂⟩ := hv x hy hf
  have hh := hk _ px qx pe qe
  omega

private theorem row_of_get {ps qs : List Piece} {i j : ℕ} {c γ : Site} (cr γr : Site)
    (hi : i < qs.length) (hj : j < ps.length)
    (hr : RawRot ps[j].odo qs[i].odo cr γr)
    (he : mulI qs[i].off = ps[j].off + cr - c) (hv : EvenSite qs[i].off)
    (ha : qs[i].aff = rotR ps[j].aff + hHalf qs[i].off + γ - γr)
    (hx : ∀ x ∈ qs[i].placed, x ∉ qs[i].exc → mulI x + c ∉ ps[j].exc) : Row ps qs i j c γ := by
  intro q hq
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hq
  subst q
  let p := ps[j]
  let q := qs[i]
  obtain ⟨b,h⟩ := piece_transport ⟨p.placed,pieceVal p⟩ ⟨q.placed,pieceVal q⟩ p q c γ cr γr 0 0
    (fun _ _ _ => (add_zero _).symm) (fun _ _ _ => (add_zero _).symm) hr he hv ha hx
  exact ⟨p,List.getElem?_eq_getElem hj,b, fun x hm hxe => ⟨(h x hm hxe).1,hx x hm hxe,(h x hm hxe).2⟩⟩

def stdIndex (o : Bool) (i : ℕ) : ℕ :=
  (if o then [3,2,5,4,1,0] else [5,4,3,2,0,1])[i]?.getD i

def altIndex (o : Bool) (i : ℕ) : ℕ :=
  (if o then [1,0,3,2,5,4] else [2,3,0,1,4,5])[i]?.getD i

abbrev C (w : Word) := texV1Odd ((parentsAt w).current .odd) - ((0 : ℤ),(1 : ℤ))

section
variable (S : WeakData) (pO pE aO aE : Word → PartialOdometer)
variable (lE lO : Word → Bool → Bool → PartialOdometer) (w : Word)
variable (hl : w.getLast? = some Digit.three)
variable (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false)
  (vP1 w - ((0 : ℤ),(1 : ℤ))) 0)
variable (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true)
  (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0)
variable (hL : ∀ elong : Bool, w.getLast? = some Digit.three → ∀ plus : Bool,
  RawRot (lE w.dropLast plus elong) (lO (swapW w.dropLast) (plus != W1Odd w) elong) (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0)

set_option hygiene false in
local macro "std_parent" : tactic => `(tactic| (
  simp only [tileOddPieces, tileEvenPieces, List.getElem_cons_succ, List.getElem_cons_zero, stdPiece,
    corr_swapW_two, corr_swapW_three, W1Odd_swapW, dropLast_swapW, hl, hWo, reduceCtorEq,
    decide_true, decide_false, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, if_true, if_false]
  first | exact hP | exact hQ | exact lp | exact lm))

set_option hygiene false in
local macro "alt_parent" : tactic => `(tactic| (alt_lists; first | exact hP | exact hQ | exact lp | exact lm))

include hl hP hQ hL
set_option maxHeartbeats 400000 in
theorem standard_rows (i : ℕ) (hi : i < 6) :
    Row (tileOddPieces S pO pE lE w) (tileEvenPieces S pO pE lO (swapW w)) i (stdIndex (W1Odd w) i) (C w) 0 := by
  have lp := hL false hl true
  have lm := hL false hl false
  obtain ⟨e1,e2,e3,e4,e5,e6⟩ := vecs_swapW w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  cases hWo : W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hWo] at lp lm
  all_goals norm_num [stdIndex, C]
  all_goals
    first
    | (apply row_of_get (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 (by simp [tileEvenPieces]) (by simp [tileOddPieces]) <;>
       first | std_parent | rot_id)
    | (apply row_of_get (vP1 w - ((0 : ℤ),(1 : ℤ))) 0 (by simp [tileEvenPieces]) (by simp [tileOddPieces]) <;>
       first | std_parent | rot_id)
set_option maxHeartbeats 400000 in
theorem alternate_rows (i : ℕ) (hi : i < 6) :
    Row (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w)) i
      (altIndex (W1Odd w) i) (altCf w false).1 (altCf w false).2 := by
  have lp := hL true hl true
  have lm := hL true hl false
  obtain ⟨e1,e2,e3,e4,e5,e6⟩ := vecs_swapW w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  cases hWo : W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [hWo] at lp lm
  all_goals norm_num [altIndex]
  all_goals
    first
    | (apply row_of_get (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 (by alt_lists; simp) (by alt_lists; simp) <;>
       first | alt_parent | rot_id_alt)
    | (apply row_of_get (vP1 w - ((0 : ℤ),(1 : ℤ))) 0 (by alt_lists; simp) (by alt_lists; simp) <;>
       first | alt_parent | rot_id_alt)

end

abbrev O (f : Word → JSlice) (w u : Word) := (below f w u).tOdd
abbrev E (f : Word → JSlice) (w u : Word) := (below f w u).tEven
abbrev AO (f : Word → JSlice) (w u : Word) := (below f w u).aOdd
abbrev AE (f : Word → JSlice) (w u : Word) := (below f w u).aEven
abbrev LO (f : Word → JSlice) (w u : Word) := (below f w u).lOdd
abbrev LE (f : Word → JSlice) (w u : Word) := (below f w u).lEven

abbrev oddPs (D : JointData) (f : Word → JSlice) (w : Word) := tileOddPieces D.S (O f w) (E f w) (LE f w) w
abbrev evenPs (D : JointData) (f : Word → JSlice) (w : Word) := tileEvenPieces D.S (O f w) (E f w) (LO f w) w
abbrev altOddPs (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileAltOddPieces D.S (O f w) (E f w) (AO f w) (AE f w) (LO f w) w
abbrev altEvenPs (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileAltEvenPieces D.S (O f w) (E f w) (AO f w) (AE f w) (LE f w) w

theorem parent_rotations (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hn : ¬ IsBase w) :
    RawRot (regOdo D.S (O f w) (E f w) (regsAt w).1 true) (regOdo D.S (O f w) (E f w) (regsAt (swapW w)).2 false)
      (vP1 w - ((0 : ℤ),(1 : ℤ))) 0 ∧
    RawRot (regOdo D.S (O f w) (E f w) (regsAt w).2 false) (regOdo D.S (O f w) (E f w) (regsAt (swapW w)).1 true)
      (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 := by
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := regs_some w hn
  have lu := regsAt_lt w u (Or.inl hu)
  have lv := regsAt_lt w v (Or.inr hv)
  have ls (t : Word) (h : t.length < w.length) : (swapW t).length < w.length := by simpa [length_swapW] using h
  have sl (t : Word) (lt : t.length < w.length) := family_slopes D f t.length
    (fun q hq => (hg q (lt_of_le_of_lt hq lt)).1) (baseSlopes_paper D hS hA) t le_rfl
  have ru : (regsAt (swapW w)).2 = some (swapW u) := by rw [regsAt_swapW,hu]; rfl
  have rv : (regsAt (swapW w)).1 = some (swapW v) := by rw [regsAt_swapW,hv]; rfl
  simp only [hu,hv,ru,rv,regOdo,O,E,below_of_lt f w u lu,below_of_lt f w v lv,
    below_of_lt f w (swapW u) (ls u lu),below_of_lt f w (swapW v) (ls v lv)]
  have hj := (hg u lu).2.2.2.1.1
  have hk := (hg v lv).2.2.2.1.2.1
  rw [(parents_of_regs w).1 u hu] at hj
  rw [(parents_of_regs w).2 v hv] at hk
  exact ⟨rawRot_of_tileRotation_slopes _ _ _ hj (sl u lu).1 (sl _ (ls u lu)).2.1,
    rawRot_of_tileRotation_slopes _ _ _ hk (sl v lv).2.1 (sl _ (ls v lv)).1⟩

abbrev Rows (ps : List Piece) (is : List ℕ) :=
  ∀ i ∈ is, ∀ j < 6, j ≠ i → PairCompat ps i j

private theorem indices (o : Bool) (i j : ℕ) (hi : i ∈ [1,2]) (hj : j < 6) (hne : j ≠ i) :
    (stdIndex o i ∈ (if o then [2,5] else [3,4]) ∧ stdIndex o j < 6 ∧ stdIndex o j ≠ stdIndex o i) ∧
    (altIndex o i ∈ [0,3] ∧ altIndex o j < 6 ∧ altIndex o j ≠ altIndex o i) := by
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  cases o <;> rcases hi with rfl|rfl <;> rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> first | contradiction | decide

/-- At every corrected child ending in three, the full set of ordinary and elongated L comparisons
gives all the corresponding comparisons at the swapped child, including the two L entries with each other. -/
theorem after_two_of_after_three (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hw : CorrectedAfterThree w)
    (std : Rows (oddPs D f w) (oddLIdx w)) (alt : Rows (altEvenPs D f w) altEvenLIdx) :
    Rows (evenPs D f (swapW w)) evenLIdx ∧ Rows (altOddPs D f (swapW w)) altOddLIdx := by
  obtain ⟨hP,hQ⟩ := parent_rotations D hS hA f w hg hw.1
  have hL (elong : Bool) (hl : w.getLast? = some Digit.three) (plus : Bool) :
      RawRot (LE f w w.dropLast plus elong) (LO f w (swapW w.dropLast) (plus != W1Odd w) elong)
        (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 := by
    have lt := dropLast_length_lt hl
    simp only [LE,LO,below_of_lt f w w.dropLast lt,below_of_lt f w _ (by rwa [length_swapW] : (swapW w.dropLast).length < w.length)]
    exact lrot_three f w hw.1 hl (hg _ lt).2.2.2.2.1 elong plus
  constructor <;> intro i hi j hj hne
  all_goals have hin : i ∈ [1,2] := hi
  all_goals have il : i < 6 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hin; omega
  all_goals obtain ⟨s,a⟩ := indices (W1Odd w) i j hin hj hne
  · unfold evenPs O E LO
    rw [below_swapW]
    have r := standard_rows D.S (O f w) (E f w) (LE f w) (LO f w) w hw.2 hP hQ hL
    exact two_rows (r i il) (r j hj) (std _ s.1 _ s.2.1 s.2.2)
  · unfold altOddPs O E AO AE LO
    rw [below_swapW]
    have r := alternate_rows D.S (O f w) (E f w) (AO f w) (AE f w) (LE f w) (LO f w) w hw.2 hP hQ hL
    exact two_rows (r i il) (r j hj) (alt _ a.1 _ a.2.1 a.2.2)

/-- The named comparison for all four corrected decompositions from the two decompositions ending in three. -/
theorem correctedCompatInput_of_after_three (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = PaperAltBaseCond)
    (h : ∀ f w, GoodBelow D f (List.length w) → CorrectedAfterThree w →
      Rows (oddPs D f w) (oddLIdx w) ∧ Rows (altEvenPs D f w) altEvenLIdx) : CorrectedCompatInput D := by
  intro f w hg hn
  have swapped (ht : CorrectedAfterTwo w) : Rows (evenPs D f w) evenLIdx ∧ Rows (altOddPs D f w) altOddLIdx := by
    have t : CorrectedAfterThree (swapW w) := ⟨Standard.nonbase_swap hn, by rw [getLast_swapW,ht.2]; rfl⟩
    have gs : GoodBelow D f (swapW w).length := by rwa [length_swapW]
    obtain ⟨s,a⟩ := h f _ gs t
    have hs := after_two_of_after_three D hS hA f (swapW w) gs t s a
    rw [swapW_swapW'] at hs
    exact hs
  exact ⟨fun ht => (h f w hg ht).1,fun ht => (swapped ht).1,fun ht => (swapped ht).2,fun ht => (h f w hg ht).2⟩

section
variable (S : WeakData) (pO pE aO aE : Word → PartialOdometer)
variable (lE lO : Word → Bool → Bool → PartialOdometer) (w : Word)
variable (hP : RawRot (regOdo S pO pE (regsAt w).1 true) (regOdo S pO pE (regsAt (swapW w)).2 false)
  (vP1 w - ((0 : ℤ),(1 : ℤ))) 0)
variable (hQ : RawRot (regOdo S pO pE (regsAt w).2 false) (regOdo S pO pE (regsAt (swapW w)).1 true)
  (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0)
variable (hH : RawRot (regOdo S aO aE (regsAt w).1 true) (regOdo S aO aE (regsAt (swapW w)).2 false)
  (altParP w).1 (altParP w).2)
private abbrev AltRow (i : ℕ) :=
  Row (tileAltEvenPieces S pO pE aO aE lE w) (tileAltOddPieces S pO pE aO aE lO (swapW w))
    i (altIndex (W1Odd w) i) (altCf w false).1 (altCf w false).2

set_option hygiene false in
local macro "full_row" : tactic => `(tactic| (
  obtain ⟨e1,e2,e3,e4,e5,e6⟩ := vecs_swapW w
  have hp : ((parentsAt w).odd.num + (parentsAt w).odd.den) % 2 = 1 := (parentsAt_valid w).odd_parity
  have hq : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := (parentsAt_valid w).even_parity
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  cases hWo : W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold AltRow
  all_goals rw [hWo]
  all_goals norm_num [altIndex]
  all_goals
    first
    | (apply row_of_get (vQ1 w - ((0 : ℤ),(1 : ℤ))) 0 (by alt_lists; simp) (by alt_lists; simp) <;>
        first | (alt_lists; exact hQ) | rot_id_alt)
    | (apply row_of_get (vP1 w - ((0 : ℤ),(1 : ℤ))) 0 (by alt_lists; simp) (by alt_lists; simp) <;>
        first | (alt_lists; exact hP) | rot_id_alt)
    | (apply row_of_get (altParP w).1 (altParP w).2 (by alt_lists; simp) (by alt_lists; simp) <;>
        first | (alt_lists; exact hH) | rot_id_alt)))

include hP hQ hH
set_option maxHeartbeats 400000 in
private theorem after_one_rows (hl : w.getLast? = some .one) (i : ℕ) (hi : i < 7) :
    AltRow S pO pE aO aE lE lO w i := by full_row

set_option maxHeartbeats 400000 in
private theorem after_two_rows (hl : w.getLast? = some .two) (i : ℕ) (hi : i < 7) :
    AltRow S pO pE aO aE lE lO w i := by full_row
end

private theorem head_rotation (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (t : Digit)
    (ht : t = .one ∨ t = .two) (hl : w.getLast? = some t) :
    RawRot (regOdo D.S (AO f w) (AE f w) (regsAt w).1 true) (regOdo D.S (AO f w) (AE f w) (regsAt (swapW w)).2 false)
      (altParP w).1 (altParP w).2 := by
  let u := w.dropLast
  have lt : u.length < w.length := dropLast_length_lt hl
  have ltr : (swapW u).length < w.length := by rwa [length_swapW]
  have ws : w = u++[t] := eq_dropLast_append hl
  have ru : (regsAt w).1 = some u := by
    conv_lhs => rw [ws,WeakStepPaper.regsAt_snoc]
    rcases ht with rfl|rfl <;> rfl
  have rv : (regsAt (swapW w)).2 = some (swapW u) := by rw [regsAt_swapW,ru]; rfl
  simp only [ru,rv,regOdo,AO,AE,below_of_lt f w u lt,below_of_lt f w (swapW u) ltr]
  have hh := (hg u lt).2.2.2.1.2.2.1
  have cf := altCf_odd_reg u t ht
  rw [←ws] at cf
  rw [cf] at hh
  have sl (v : Word) (lv : v.length < w.length) := family_slopes D f v.length
    (fun q h => (hg q (lt_of_le_of_lt h lv)).1) (baseSlopes_paper D hS hA) v le_rfl
  exact rawRot_of_altRotation_slopes _ _ _ _ hh (sl u lt).2.2.1 (sl _ ltr).2.2.2

/-- The six Case 3 comparisons of the odd alternate child follow from those of the even alternate child of the swapped word. -/
theorem odd_parent_at_swap (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (w : Word) (hg : GoodBelow D f w.length) (hn : ¬ IsBase w)
    (pairs : ∀ j < 6, PairCompat (altEvenPs D f w) 6 j) : ∀ j < 6, PairCompat (altOddPs D f (swapW w)) 6 j := by
  intro j hj
  have bound : altIndex (W1Odd w) j < 6 := by
    have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    cases W1Odd w <;> rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have six : altIndex (W1Odd w) 6 = 6 := by cases W1Odd w <;> rfl
  obtain ⟨hP,hQ⟩ := parent_rotations D hS hA f w hg hn
  unfold altOddPs O E AO AE LO
  rw [below_swapW]
  cases hl : w.getLast? with
  | none =>
    have h : w = [] := List.getLast?_eq_none_iff.mp hl
    exact (hn (Or.inl h)).elim
  | some t =>
    cases t with
    | three =>
      apply AltParentBase.odd_after_two
      rw [getLast_swapW,hl]; rfl
    | one =>
      have hh := head_rotation D hS hA f w hg .one (Or.inl rfl) hl
      have r := after_one_rows D.S (O f w) (E f w) (AO f w) (AE f w) (LE f w) (LO f w) w hP hQ hh hl
      exact two_rows (r 6 (by decide)) (r j (by omega)) (six.symm ▸ pairs _ bound)
    | two =>
      have hh := head_rotation D hS hA f w hg .two (Or.inr rfl) hl
      have r := after_two_rows D.S (O f w) (E f w) (AO f w) (AE f w) (LE f w) (LO f w) w hP hQ hh hl
      exact two_rows (r 6 (by decide)) (r j (by omega)) (six.symm ▸ pairs _ bound)

/-- The named Case 3 input from the even alternate child alone. -/
theorem altParentCompatInput_of_even (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = PaperAltBaseCond)
    (h : ∀ f w, GoodBelow D f (List.length w) → ¬ IsBase w → ∀ j < 6, PairCompat (altEvenPs D f w) 6 j) :
    AltParentCompatInput D := by
  intro f w hg hn j hj
  have hs : GoodBelow D f (swapW w).length := by rwa [length_swapW]
  have nb := Standard.nonbase_swap hn
  have hr := odd_parent_at_swap D hS hA f (swapW w) hs nb (h f _ hs nb)
  rw [swapW_swapW'] at hr
  exact ⟨hr j hj,h f w hg hn j hj⟩


/-- At every one or three exit from a positive run of twos, the even alternate register is compatible with
every one of the first six entries in the odd alternate child. -/
theorem odd_after_twos (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (one : Bool) :
    let w := List.replicate (k+1) Digit.two ++ [if one then .one else .three]
    GoodBelow D f w.length → ∀ j < 6, PairCompat (altOddPs D f w) 6 j := by
  let v := List.replicate (k+1) Digit.three ++ [if one then .one else .two]
  let w := List.replicate (k+1) Digit.two ++ [if one then .one else .three]
  change GoodBelow D f w.length → _
  intro hg
  have sw : swapW v = w := by cases one <;> simp [v,w,swapW,List.map_replicate,Digit.swapTwoThree]
  have hn : ¬ IsBase v := by cases one <;> simp [v,IsBase,List.mem_replicate,List.append_eq_nil_iff]
  have prev : GoodBelow D f v.length := by simpa [w,v] using hg
  have h := odd_parent_at_swap D hS hA f v prev hn (AltParentStair.even_after_threes D hS hA f k one prev)
  rwa [sw] at h

end FLatticePaper.Tiles.TileCompatRotation
