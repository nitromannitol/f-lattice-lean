import FLatticePaper.Tiles.AltParentReflection

/-! The odd alternate register against the six pieces of the even alternate child at exits from a run of threes. -/

namespace FLatticePaper.Tiles.AltParentStair

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard SurgicalWeak SurgicalAlt SurgicalDict JointFamily JointInduction JointGlue TileCompatInputs BaseTileProps

private def tri (y : ℤ) := y*(y+1)/2
private def headTerm (d x y : ℤ) := min 0 x + min 0 (d-x-1) + max (x+y-d) 0 +
  if (x = -1 ∧ y = -1) ∨ (x = d ∧ y = d+2) ∨ (x+y = d ∧ 0 < x ∧ x < d-1) then 1 else 0
private def stairTerm (d x y : ℤ) := y + min (x-1) 0 + if (x=0 ∧ y=0) ∨ (x=2 ∧ y=d+1) then 1 else 0
private def ladderTerm (d x y : ℤ) := y + min (x-1) 0 + min 0 (d+1-x) + max (x+y-d-2) 0 +
  if (x=0 ∧ y=0) ∨ (x=d+2 ∧ y=d+2) ∨ (x+y=d+2 ∧ 1<y ∧ y<d+1) then 1 else 0
private def rawTile (lad : Bool) (d : ℤ) := if lad then ladderF d else stairF d
private noncomputable def rawVal (lad : Bool) (d : ℤ) := if lad then paperLadderValue d else paperStairValue d
private def term (lad : Bool) := if lad then ladderTerm else stairTerm

private theorem val_eq (lad : Bool) (d x y : ℤ) : rawVal lad d (x,y) = -tri y + term lad d x y := by
  cases lad
  · simp only [rawVal, term, Bool.false_eq_true, if_false, paperStairValue, tri, stairTerm, Prod.mk.injEq]; abel
  · simp only [rawVal, term, if_true, plV, tri, ladderTerm, Prod.mk.injEq]; abel

private def row (d e : ℤ) (lad : Bool) (h a : Site) (c : ℤ) : Prop :=
  ∀ x y : ℤ, (x,y) ∈ paperLadderAltTile d → (x+h.1,y+h.2) ∈ rawTile lad e →
    term lad e (x+h.1) (y+h.2) - headTerm d x y - a.1*x - (a.2+h.2)*y = c

private theorem difference (d e : ℤ) (lad : Bool) (h a : Site) (c : ℤ) (r : row d e lad h a c)
    (z : Site) (hz : z ∈ paperLadderAltTile d) (ht : z+h ∈ rawTile lad e) :
    rawVal lad e (z+h) - paperLadderAltValue d z = dotS a z + c - tri h.2 := by
  obtain ⟨x,y⟩ := z
  have t : tri (y+h.2) = tri y + h.2*y + tri h.2 := by
    unfold tri
    nlinarith only [two_mul_T2 (y+h.2), two_mul_T2 y, two_mul_T2 h.2]
  change rawVal lad e (x+h.1,y+h.2) - _ = _
  rw [val_eq, pladA, t]
  have hrow := r x y hz ht
  dsimp only [headTerm, dotS, tri] at hrow ⊢
  linear_combination hrow

local macro "row_geometry" : tactic => `(tactic| (
  intro x y hx hy
  rw [mem_ladAlt] at hx
  first | change _ ∈ stairF _ at hy; rw [mem_stairF_ab _ (by omega)] at hy
        | change _ ∈ ladderF _ at hy; rw [mem_ladderF_ab _ (by omega)] at hy
  simp only [term, if_true, Bool.false_eq_true, if_false, ladderTerm, stairTerm, headTerm, min_def, max_def]
  ring_nf
  grind))

section
variable (d : ℤ) (hd : 4 ≤ d)
include hd
set_option maxHeartbeats 400000

private theorem one_positive : row d (d+1) false (3-2*d,d+1) (1,-d) (3-d) := by row_geometry
private theorem one_negative : row d (d+1) false (d+2,2) (0,0) 3 := by row_geometry
private theorem one_plain : row d d true (3,d+3) (1,-d) (d+8) := by
  intro x y hx hy
  change (x+3,y+(d+3)) ∈ ladderF d at hy
  rw [mem_ladAlt] at hx
  rw [mem_ladderF_ab _ hd] at hy
  have h : y = -1 ∧ 0 ≤ x ∧ x ≤ d-1 := by omega
  clear hx hy
  simp only [term, if_true, ladderTerm, headTerm, min_def, max_def]
  ring_nf
  grind
private theorem two_positive : row d (d-1) false (3-d,d+1) (1,1-d) 4 := by row_geometry
private theorem two_negative : row d (d-1) false (2-2*d,-2) (0,1) 1 := by row_geometry
private theorem two_plain : row d d true (4-2*d,d) (1,1-d) (3-d) := by
  intro x y hx hy
  change (x+(4-2*d),y+d) ∈ ladderF d at hy
  rw [mem_ladAlt] at hx
  rw [mem_ladderF_ab _ hd] at hy
  have h : (d-2 ≤ x ∧ x ≤ d-1 ∧ -1 ≤ y ∧ y ≤ 0) ∨ (d-2 ≤ x ∧ x ≤ 2*d-2 ∧ y = 1) := by omega
  clear hx hy
  simp only [term, if_true, ladderTerm, headTerm, min_def, max_def]
  ring_nf
  grind
end

private def headSpec (o : PartialOdometer) (d : ℤ) : Prop :=
  ∀ z ∈ o.dom, z-(1,1) ∈ paperLadderAltTile d ∧ o.val z = paperLadderAltValue d (z-(1,1))
private def tileSpec (o : PartialOdometer) (lad : Bool) (d : ℤ) : Prop :=
  o.dom = rawTile lad d ∧ ∀ z ∈ o.dom, o.val z = rawVal lad d z

private theorem place_row {ps : List Piece} {j : ℕ} {H T : PartialOdometer} {b t s u h a : Site} {c d e : ℤ} {lad : Bool}
    (hi : ps[6]? = some (stdPiece H b s)) (hj : ps[j]? = some (stdPiece T t u)) (hh : headSpec H d)
    (ht : tileSpec T lad e) (hd : b+(1,1)-t = h) (ha : s-u = a) (cert : row d e lad h a c) : PairCompat ps 6 j := by
  intro p q ep eq
  rw [hi, Option.some.injEq] at ep
  rw [hj, Option.some.injEq] at eq
  subst p; subst q
  refine ⟨dotS a (b+(1,1)) - c + tri h.2, fun x xp xq _ _ => ?_⟩
  have hx := mem_shift.mp (show x ∈ shift H.dom b from xp)
  have tx := mem_shift.mp (show x ∈ shift T.dom t from xq)
  obtain ⟨mem,val⟩ := hh _ hx
  have e' : x-b-(1,1)+h = x-t := by rw [←hd]; abel
  have hv := difference _ _ _ _ _ _ cert _ mem (by rw [e', ←ht.1]; exact tx)
  rw [e'] at hv
  change H.val (x-b) + dotS s x - (T.val (x-t) + dotS u x) = _
  rw [val, ht.2 _ tx]
  rw [← ha] at hv ⊢
  simp only [dotS, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hv ⊢
  linear_combination -hv

private abbrev regT (D : JointData) (f : Word → JSlice) (w : Word) :=
  regOdo D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
private abbrev regH (D : JointData) (f : Word → JSlice) (w : Word) :=
  regOdo D.S (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (regsAt w).1 true
private abbrev pieces (D : JointData) (f : Word → JSlice) (w : Word) :=
  tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
    (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w

private theorem representatives (D : JointData) (f : Word → JSlice) (w : Word) (d : ℤ) (hd : 4 ≤ d) (one : Bool)
    (hl : w.getLast? = some (if one then .one else .two)) (ph : W1Odd w = one)
    (p : (parentsAt w).odd = ⟨1,d⟩) (q : (parentsAt w).even = ⟨1, if one then d+1 else d-1⟩)
    (H : headSpec (regH D f w) d) (P : tileSpec (regT D f w (regsAt w).1 true) true d)
    (Q : tileSpec (regT D f w (regsAt w).2 false) false (if one then d+1 else d-1)) :
    ∀ i ∈ [0,2,4], PairCompat (pieces D f w) 6 i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have geometry : ∀ {a b : Site}, a.1 = b.1 → a.2 = b.2 → a = b := fun hx hy => Prod.ext hx hy
  cases one <;> simp only [Bool.false_eq_true, if_false, if_true] at hl q Q
  all_goals rcases hi with rfl | rfl | rfl
  all_goals simp only [pieces, tileAltEvenPieces, altTypeOf, hl, ph, reduceCtorEq,
    Option.bind_some, altP1Coeff, ↓reduceIte, Bool.false_eq_true]
  case' false.inl => apply place_row rfl rfl H Q ?_ ?_ (two_positive d hd)
  case' false.inr.inl => apply place_row rfl rfl H Q ?_ ?_ (two_negative d hd)
  case' false.inr.inr => apply place_row rfl rfl H P ?_ ?_ (two_plain d hd)
  case' true.inl => apply place_row rfl rfl H Q ?_ ?_ (one_positive d hd)
  case' true.inr.inl => apply place_row rfl rfl H Q ?_ ?_ (one_negative d hd)
  case' true.inr.inr => apply place_row rfl rfl H P ?_ ?_ (one_plain d hd)
  all_goals apply geometry <;> simp [altOff, altAff, altQ0Coeff, coeffOff, coeffAffine, vP1, vP2, vQ1, vQ2,
    texV1Odd, texV1Even, texV2, p, q] <;> ring

private abbrev threes (k : ℕ) := List.replicate k Digit.three

private theorem bases (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (n k : ℕ) (hg : GoodBelow D f n) (hk : k < n) :
    PaperBaseCond (threes k) (f (threes k)).tOdd (f (threes k)).tEven ∧
    PaperAltBaseCond (threes k) (f (threes k)).aOdd (f (threes k)).aEven := by
  have hb := AltRotStep.isBase_replicate_three k
  have H := (hg (threes k) (by simpa [threes] using hk)).1
  obtain ⟨ho,he,ha,hb'⟩ := H.2.2.1.1 hb
  obtain hs := H.1.2.2.1 hb
  obtain ht := H.2.1.2.2.1 hb
  rw [hS] at hs; rw [hA] at ht
  rw [ho,he,ha,hb']
  exact ⟨hs,ht⟩

private theorem standard_even (k : ℕ) (P Q : PartialOdometer) (h : PaperBaseCond (threes k) P Q) :
    tileSpec Q false (2*(k : ℤ)+3) := by
  cases k with
  | zero => exact (h.1 rfl).2.2
  | succ k => exact (h.2.1 _ (by omega) rfl).2.2

/-- Every even alternate child of a positive three-run followed by one or two, including the three half-turned pieces. -/
theorem even_after_threes (D : JointData) (hS : D.S = WeakStepPaper.paperS) (hA : D.altBase = PaperAltBaseCond)
    (f : Word → JSlice) (k : ℕ) (one : Bool) :
    let w := threes (k+1) ++ [if one then Digit.one else .two]
    GoodBelow D f w.length → ∀ j < 6, PairCompat (pieces D f w) 6 j := by
  dsimp only
  intro hg
  let v := threes (k+1)
  let s := if one then Digit.one else .two
  let w := v++[s]
  let d := 2*((k+1 : ℕ) : ℤ)+2
  have ed : d+1 = 2*((k+1 : ℕ) : ℤ)+3 := by dsimp [d]; omega
  have hL : v.length < w.length := by simp [w]
  have hL' : (threes k).length < w.length := by simp [w,v,threes]
  have hw : ¬ IsBase w := by
    cases one <;> simp [w,v,s,threes,IsBase,List.mem_replicate, List.append_eq_nil_iff]
  apply (AltParentReflection.three_representatives D hS hA f w hg hw).2
  have hpq := bases D hS hA f w.length (k+1) hg (by simpa [v,threes] using hL)
  obtain ⟨dp,vp,-⟩ := hpq.1.2.1 (k+1) (by omega) rfl
  obtain ⟨dh,vh,-⟩ := hpq.2.2.1 (k+1) (by omega) rfl
  have hpr : (regsAt w).1 = some v := by cases one <;> simp [w,s,WeakStepPaper.regsAt_snoc,regStep]
  have hH : headSpec (regH D f w) d := by
    simp only [regH,hpr,regOdo,JointRot.below_of_lt _ _ _ hL]
    exact fun z hz => ⟨(dh z).1 hz,vh z hz⟩
  have hP : tileSpec (regT D f w (regsAt w).1 true) true d := by
    simp only [regT,hpr,regOdo,JointRot.below_of_lt _ _ _ hL]
    exact ⟨dp,vp⟩
  refine representatives D f w d (by dsimp [d]; omega) one (by simp [w,s]) ?_ ?_ ?_ hH hP ?_
  · cases one <;> simp [w,v,s,W1Odd,phase,List.count_replicate,threes]
  · change (parentsAt (v++[s])).odd = _
    rw [parentsAt_append_singleton]
    cases one <;> exact cur_odd_three (k+1)
  · change (parentsAt (v++[s])).even = _
    rw [parentsAt_append_singleton]
    cases one with
    | true => change (parentsAt v).current .even = ⟨1,d+1⟩; rw [ed]; exact cur_even_three (k+1)
    | false =>
      change (parentsAt (threes (k+1))).even = ⟨1,d-1⟩
      rw [parents_three, show d-1 = 2*((k+1 : ℕ) : ℤ)+1 by dsimp [d]; omega]
  · cases one with
    | true =>
      have er : (regsAt w).2 = some v := by simp [w,s,WeakStepPaper.regsAt_snoc,regStep]
      simp only [regT,er,regOdo,JointRot.below_of_lt _ _ _ hL,if_true]
      rw [ed]
      exact standard_even _ _ _ hpq.1
    | false =>
      have er : (regsAt w).2 = some (threes k) := by
        simp only [w,s,Bool.false_eq_true,if_false,WeakStepPaper.regsAt_snoc,regStep,v]
        rw [show threes (k+1) = threes k ++ [.three] from List.replicate_succ',WeakStepPaper.regsAt_snoc]; rfl
      simp only [regT,er,regOdo,JointRot.below_of_lt _ _ _ hL',Bool.false_eq_true,if_false]
      have ed : d-1 = 2*(k : ℤ)+3 := by dsimp [d]; omega
      rw [ed]
      exact standard_even _ _ _ (bases D hS hA f w.length k hg (by simpa [threes] using hL')).1

end FLatticePaper.Tiles.AltParentStair
