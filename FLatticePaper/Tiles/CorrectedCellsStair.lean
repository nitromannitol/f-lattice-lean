import FLatticePaper.Tiles.CorrectedCellsEnds
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.CorrectedCellsOrdinary
import FLatticePaper.Tiles.BaseTileProps

/-! The two corrected children after a positive pure-three run, with the shifted zero-tile in each column. -/

namespace FLatticePaper.Tiles.CorrectedCellsStair

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard PaperAltBase JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt SurgicalDict

private abbrev big (d : ℤ) := ladderF (d+1)
private abbrev head (d : ℤ) := stairAltF d
private abbrev fwd (d : ℤ) : Site := (2*d-1,-d)
private abbrev first (d : ℤ) : Site := (d-1,2)
private abbrev lastHead (d : ℤ) : Site := (2*d-1,3)
private def up (d : ℤ) := stairF d ∪ shift zeroTile (1-d,d) ∪ shift (head d) (first d)
private def down (d : ℤ) := shift (stairF d) (d+1,2) ∪ shift zeroTile (2*d+1,1) ∪ shift (head d) (d,1)

private def isStair (d x y : ℤ) :=
  (2-d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d+1 ∧ 1 ≤ x+y ∧ x+y ≤ d+2) ∨ (x=0 ∧ y=0) ∨ (x=2 ∧ y=d+1)
private def isBig (d x y : ℤ) :=
  ((x=0 ∧ y=0) ∨ (x=d+3 ∧ y=d+3) ∨ (x+y=d+3 ∧ 1<y ∧ y<d+2) ∨
    (1-d≤x ∧ x≤2*d+2 ∧ 0≤y ∧ y≤d+3 ∧ 1≤x+y ∧ x+y≤2*d+5)) ∧ ¬((d+1≤x ∧ y=0) ∨ (x≤2 ∧ y=d+3))
private def isHead (d x y : ℤ) :=
  (x=1-d ∧ -1≤y ∧ y≤0) ∨ (x=3 ∧ d≤y ∧ y≤d+1) ∨ (x+y=2 ∧ 0<y ∧ y<d) ∨
  (1-d≤x ∧ x≤0 ∧ y= -1) ∨ (4-d≤x ∧ x≤3 ∧ y=d+1) ∨
  (4-2*d≤x ∧ x≤d ∧ 0≤y ∧ y≤d ∧ -d+2≤x+y ∧ x+y≤d+2)
private def isZero (x y : ℤ) := 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 2

private theorem stair_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ stairF d ↔ isStair d x y := mem_stairF (by omega) _
private theorem big_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ big d ↔ isBig d x y := by
  rw [mem_ladderF (by omega : 2 ≤ d+1)]
  dsimp [isBig]
  omega
private theorem head_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ head d ↔ isHead d x y := by
  simp only [head,stairAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,isHead]
  omega
private theorem zero_mem (x y : ℤ) : (x,y) ∈ zeroTile ↔ isZero x y := by
  simp only [zeroTile,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,isZero]
  omega

private theorem short_sub (d : ℤ) (hd : 3 ≤ d) : up d ⊆ big d ∧ down d ⊆ big d := by
  constructor <;> rintro ⟨x,y⟩ ht
  all_goals simp only [up,down,first,Finset.mem_union,mem_shift,Prod.mk_sub_mk,stair_mem _ _ _ hd,zero_mem,head_mem _ _ _ hd] at ht
  all_goals rw [big_mem _ _ _ hd]; rcases ht with (h|h)|h <;> unfold isBig <;> first | (unfold isStair at h; omega) | (unfold isZero at h; omega) | (unfold isHead at h; omega)

private theorem up_cover (d : ℤ) (hd : 3 ≤ d) :
    big d ⊆ up d ∪ shift (head d) (lastHead d) ∪ shift (big d) (fwd d) := by
  rintro ⟨x,y⟩ hx
  rw [big_mem _ _ _ hd] at hx
  unfold isBig at hx
  simp only [up,first,lastHead,fwd,Finset.mem_union,mem_shift,Prod.mk_sub_mk,stair_mem _ _ _ hd,zero_mem,head_mem _ _ _ hd,big_mem _ _ _ hd]
  by_cases h : x ≤ d-1
  · left; left
    by_cases h₁ : y ≤ d-1
    · by_cases h₂ : x+y ≤ d-1
      · left; left; unfold isStair; omega
      · right; unfold isHead; omega
    · by_cases h₂ : x ≤ 2-d
      · left; right; unfold isZero; omega
      · right; unfold isHead; omega
  · by_cases h₁ : y ≤ 2
    · right; unfold isBig; omega
    · left; right; unfold isHead; omega

private theorem down_cover (d : ℤ) (hd : 3 ≤ d) :
    big d ⊆ down d ∪ head d ∪ shift (big d) (-fwd d) := by
  rintro ⟨x,y⟩ hx
  rw [big_mem _ _ _ hd] at hx
  unfold isBig at hx
  rw [show -fwd d = (1-2*d,d) by ext <;> dsimp [fwd] <;> ring]
  simp only [down,Finset.mem_union,mem_shift,Prod.mk_sub_mk,stair_mem _ _ _ hd,zero_mem,head_mem _ _ _ hd,big_mem _ _ _ hd]
  by_cases h : x ≤ 3
  · by_cases h₁ : y ≤ d
    · left; right; unfold isHead; omega
    · right; unfold isBig; omega
  · left; left
    by_cases h₁ : y ≤ 3
    · by_cases h₂ : x ≤ 2*d
      · right; unfold isHead; omega
      · left; right; unfold isZero; omega
    · by_cases h₂ : x+y ≤ d+5
      · right; unfold isHead; omega
      · left; left; unfold isStair; omega

private theorem end_subset (d : ℤ) (hd : 3 ≤ d) :
    shift (head d) (lastHead d) ⊆ big d ∪ shift (big d) (lastHead d) := by
  rintro ⟨x,y⟩ ht
  simp only [lastHead,mem_shift,Prod.mk_sub_mk,head_mem _ _ _ hd] at ht
  simp only [lastHead,Finset.mem_union,mem_shift,Prod.mk_sub_mk,big_mem _ _ _ hd]
  unfold isHead at ht
  by_cases h : x+y ≤ 2*d+3
  · left; unfold isBig; omega
  · right; unfold isBig; omega

private def upper (d : ℤ) (long : Bool) : Tile := if long then up d ∪ shift (head d) (lastHead d) else up d
private def lower (d : ℤ) (long : Bool) : Tile := if long then down d ∪ head d else down d
private abbrev between (d : ℤ) (long : Bool) : Site := if long then lastHead d else first d

private theorem exchange (d : ℤ) (hd : 3 ≤ d) (long : Bool) :
    let t := between d long
    (upper d long ∪ shift (lower d long) t) ∪ (shift (big d) (fwd d) ∪ shift (big d) (t-fwd d)) =
    (big d ∪ shift (big d) t) ∪ (shift (big d) (fwd d) ∪ shift (big d) (t-fwd d)) := by
  let t := between d long
  have eh : first d + (d,1) = lastHead d := by ext <;> dsimp [first,lastHead]; ring
  have ush : up d ⊆ upper d long := by cases long <;> simp [upper]
  have dsh : down d ⊆ lower d long := by cases long <;> simp [lower]
  have h₁ : shift (head d) (lastHead d) ⊆ upper d long ∪ shift (lower d long) t := by
    cases long
    · have e : lastHead d = (d,1) + first d := by rw [←eh,add_comm]
      change _ ⊆ up d ∪ shift (down d) (first d)
      rw [e,←shift_shift]; intro z hz
      exact Finset.mem_union_right _ (mem_shift.mpr (Finset.mem_union_right _ (mem_shift.mp hz)))
    · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have h₂ : shift (head d) t ⊆ upper d long ∪ shift (lower d long) t := by
    cases long
    · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact fun _ h => Finset.mem_union_right _ (mem_shift.mpr (Finset.mem_union_right _ (mem_shift.mp h)))
  obtain ⟨sp,sm⟩ := short_sub d hd
  ext z
  simp only [Finset.mem_union]
  constructor
  · rintro ((hp|hm)|hr)
    · left
      cases long
      · exact Or.inl (sp hp)
      · rcases Finset.mem_union.mp hp with h|h
        · exact Or.inl (sp h)
        · exact Finset.mem_union.mp (end_subset d hd h)
    · left
      have h := mem_shift.mp hm
      cases long
      · exact Or.inr (mem_shift.mpr (sm h))
      · rcases Finset.mem_union.mp h with h|h
        · exact Or.inr (mem_shift.mpr (sm h))
        · exact Finset.mem_union.mp (end_subset d hd (mem_shift.mpr h))
    · exact Or.inr hr
  · rintro ((hp|hm)|hr)
    · rcases Finset.mem_union.mp (up_cover d hd hp) with hs|hr
      · rcases Finset.mem_union.mp hs with h|h
        · exact Or.inl (Or.inl (ush h))
        · exact Or.inl (Finset.mem_union.mp (h₁ h))
      · exact Or.inr (Or.inl hr)
    · rcases Finset.mem_union.mp (down_cover d hd (mem_shift.mp hm)) with hs|hr
      · rcases Finset.mem_union.mp hs with h|h
        · exact Or.inl (Or.inr (mem_shift.mpr (dsh h)))
        · exact Or.inl (Finset.mem_union.mp (h₂ (mem_shift.mpr h)))
      · apply Or.inr; apply Or.inr; apply mem_shift.mpr
        have hv := mem_shift.mp hr
        convert hv using 1; abel
    · exact Or.inr hr

private abbrev threes (k : ℕ) := List.replicate k Digit.three
private abbrev den (k : ℕ) := 2*(k : ℤ)+3
private theorem three_regs (k : ℕ) : regsAt (threes (k+1)) = (none,some (threes k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show threes (k+1+1) = threes (k+1)++[.three] from List.replicate_succ', WeakStepPaper.regsAt_snoc,ih]
    rfl

private theorem previous_tiles (k : ℕ) :
    stemO (threes (k+1)) = stairF (den k) ∧ bridgeO (threes (k+1)) = zeroTile ∧
    headO (threes (k+1)) = head (den k) := by
  simp only [stemO,bridgeO,headO,three_regs,regOdo,cellData,domOdo,altEvenT,
    AltRotStep.altEvenTile_of_base _ (AltRotStep.isBase_replicate_three k)]
  refine ⟨SiteBase.evenTile_rep_three _,trivial,?_⟩
  change (AltRotStep.B (threes k)).2 = _
  cases k with
  | zero => rfl
  | succ k => rw [AltRotStep.B_three _ (by omega)]

private theorem columns (k : ℕ) (long : Bool) :
    oddLCells (threes (k+1)) true long = upper (den k) long ∧
    oddLCells (threes (k+1)) false long = lower (den k) long := by
  have et : threes (k+1) = threes k++[.three] := List.replicate_succ'
  have hs : stripTrailing .two (threes (k+1)) = threes (k+1) := by rw [et,JointRot.stripTrailing_snoc]; rfl
  have ht : trailingCount .two (threes (k+1)) = 0 := by rw [et,JointRot.trailingCount_snoc]; rfl
  have ho : W1Odd (threes (k+1)) = false := by simp [W1Odd,threes,BaseTileProps.phase_three]
  have htr : (!(threes (k+1)).isEmpty && (threes (k+1)).all (fun d => decide (d = Digit.three))) = true := by
    simp [threes,List.replicate_succ]
  obtain ⟨st,br,hd⟩ := previous_tiles k
  have img (T : Tile) (v : Site) : T.image (· + v) = shift T v := rfl
  have single (F : ℕ → Tile) : (Finset.range 1).biUnion F = F 0 := by simp
  have pair (F : ℕ → Tile) : (Finset.range 2).biUnion F = F 0 ∪ F 1 := by
    rw [show 2 = 1+1 by rfl,Finset.range_add_one,Finset.biUnion_insert,single,Finset.union_comm]
  cases long <;> constructor <;> rw [CorrectedCellsColumn.odd_column,hs,ht,ho]
  all_goals simp only [oddLRel,htr,st,br,hd,pair,single,LCorrections.oddBridgeShift,Bool.not_false,
    Bool.true_and,Bool.false_eq_true,if_true,if_false,zero_smul,zero_add,Int.natCast_zero,Int.natCast_one,
    one_smul,img,shift_union,shift_shift,oddLInitOff,p0Off,offsetP0,ho,oddKCoeff]
  all_goals simp only [upper,lower,if_true,Bool.false_eq_true,if_false,up,down,first,lastHead,altOff,coeffOff,
    vP1,vQ1,vP2,vQ2,BaseTileProps.parents_three,threes,texV1Odd,texV1Even,texV2,den,Prod.mk_add_mk,Prod.fst_add,Prod.snd_add,
    Nat.cast_add,Nat.cast_one,Prod.fst_zero,Prod.snd_zero,add_zero,zero_add,mul_one,one_mul,zero_mul,neg_mul]
  all_goals norm_num
  all_goals ring_nf
  all_goals simp only [show (0,0) = (0 : Site) from rfl,AltRotStep.shift_zero]

private abbrev O (v : Word) := domOdo (oddTile v)
private abbrev E (v : Word) := domOdo (evenTile v)
private abbrev AO (v : Word) := domOdo (altOddT v)
private abbrev AE (v : Word) := domOdo (altEvenT v)
private abbrev LO (v : Word) (s l : Bool) := domOdo (oddLCells v s l)

private abbrev threeExit (k : ℕ) := threes (k+1)++[Digit.two]

private theorem registers (k : ℕ) :
    regsAt (threeExit k) = (some (threes (k+1)),some (threes k)) := by
  rw [threeExit,WeakStepPaper.regsAt_snoc,three_regs]; rfl

private theorem fractions (k : ℕ) :
    (parentsAt (threeExit k)).odd = ⟨1,den k+1⟩ ∧ (parentsAt (threeExit k)).even = ⟨1,den k⟩ := by
  simp only [threeExit,parentsAt_append_singleton,Parents.step]
  constructor
  · rw [BaseTileProps.cur_odd_three]; congr 1
  · rw [BaseTileProps.parents_three]; congr 1

private theorem full_ladder (k : ℕ) : oddTile (threes (k+1)) = big (den k) := by
  rw [SiteBase.oddTile_rep_three _ (by omega)]; congr 1

private theorem cons_union (p : Piece) (ps : List Piece) : pieceUnion (p::ps) = p.placed ∪ pieceUnion ps := rfl
private theorem std_shift (o : PartialOdometer) (v a : Site) : (stdPiece o v a).placed = shift o.dom v := rfl

private theorem translated (k : ℕ) (long : Bool) :
    let w := threeExit k
    let c := vQ2 w
    let r := if long then vQ1 w + vP2 w else vP2 w
    let P := oddTile (threes (k+1))
    let v := threes (k+1)
    (shift (oddLCells v true long) c ∪ shift (oddLCells v false long) (vQ1 w+r)) ∪
      (shift P (vQ1 w) ∪ shift P (c+r)) =
    (shift P c ∪ shift P (vQ1 w+r)) ∪ (shift P (vQ1 w) ∪ shift P (c+r)) := by
  let w := threeExit k
  let d := den k
  let r := if long then vQ1 w + vP2 w else vP2 w
  obtain ⟨p,q⟩ := fractions k
  have et : between d long + vQ2 w = vQ1 w+r := by
    cases long <;> ext <;> simp [between,r,w,vP2,vQ1,vQ2,p,q,texV2,texV1Even,d] <;> ring
  have ef : fwd d + vQ2 w = vQ1 w := by ext <;> simp [w,vQ1,vQ2,q,texV1Even,texV2,d] <;> ring
  have es : between d long - fwd d + vQ2 w = vQ2 w+r := by rw [← add_sub_right_comm,et,←ef];abel
  have h := congrArg (fun T => shift T (vQ2 w)) (exchange d (by unfold d den; omega) long)
  simp only [shift_union,shift_shift,et,ef,es] at h
  dsimp only
  rw [(columns k long).1,(columns k long).2,full_ladder k]
  exact h

/-- The shifted bridges and ordinary heads give the standard even tile at every positive pure-three exit by two. -/
theorem even_three_run_two (k : ℕ) :
    let w := threeExit k
    pieceUnion (tileEvenPieces cellData O E LO w) = evenTile w := by
  let v := threes (k+1)
  let w := threeExit k
  have hn : ¬ IsBase w := by simp [w,threeExit,threes,IsBase,List.mem_replicate,List.append_eq_nil_iff]
  have ho : W1Odd w = false := by simp [w,threeExit,threes,W1Odd,phase,List.count_replicate]
  have last : w.getLast? = some Digit.two := by simp [w,threeExit]
  have dr : w.dropLast = v := by simp [w,threeExit,v]
  have Ro : (regsAt w).1 = some v := congrArg Prod.fst (registers k)
  have Re : (regsAt w).2 = some (threes k) := congrArg Prod.snd (registers k)
  have hT : evenTile w = evenChildB false (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even := by
    unfold evenTile
    rw [SiteInduction.childTiles_nonbase w hn,stateAt_par]
    change evenChildB (W1Odd w) _ _ _ _ = _
    rw [ho]
  change pieceUnion (tileEvenPieces cellData O E LO w) = evenTile w
  rw [hT,(WeakStepPaper.regsAt_tiles w).1 _ Ro,(WeakStepPaper.regsAt_tiles w).2.2.1 _ Re]
  simp only [tileEvenPieces,last,decide_true,if_true,cons_union,std_shift,show pieceUnion [] = ∅ from rfl,
    Finset.union_empty,Ro,Re,regOdo,LO,O,E,domOdo,dr,evenChildB,q0Off,offsetQ0,ho,Bool.false_eq_true,
    if_false,AltRotStep.shift_zero]
  have h := translated k false
  let P := oddTile v
  let Q := evenTile (threes k)
  let x := vP1 w + (vP2 w + vP2 w)
  calc
    _ = (Q ∪ shift Q x) ∪ ((shift (oddLCells v true false) (vQ2 w) ∪ shift (oddLCells v false false) (vQ1 w+vP2 w)) ∪
      (shift P (vQ1 w) ∪ shift P (vQ2 w+vP2 w))) := by dsimp only [Q,x,P]; ac_rfl
    _ = _ := by dsimp only [P,v,w] at *; simp only [Bool.false_eq_true,if_false] at h; rw [h]; dsimp only [Q,x,w,vP1,vP2,vQ1,vQ2,v]; ac_rfl

/-- The elongated corrections give the printed odd alternate tile at these exits. -/
theorem alt_odd_three_run_two (k : ℕ) :
    let w := threeExit k
    pieceUnion (tileAltOddPieces cellData O E AO AE LO w) = altOddT w := by
  let v := threes (k+1)
  let w := threeExit k
  have hn : ¬ IsBase w := by simp [w,threeExit,threes,IsBase,List.mem_replicate,List.append_eq_nil_iff]
  have ho : W1Odd w = false := by simp [w,threeExit,threes,W1Odd,phase,List.count_replicate]
  have last : w.getLast? = some Digit.two := by simp [w,threeExit]
  have dr : w.dropLast = v := by simp [w,threeExit,v]
  have Ro : (regsAt w).1 = some v := congrArg Prod.fst (registers k)
  have Re : (regsAt w).2 = some (threes k) := congrArg Prod.snd (registers k)
  change pieceUnion (tileAltOddPieces cellData O E AO AE LO w) = altOddT w
  unfold altOddT
  rw [AltRotStep.altOddTile_of_not_base _ hn]
  simp only [tileAltOddPieces,SurgicalAltTiles.altOddPieces,altTypeOf,last,ho,show (phase w == 1) = false from ho,
    decide_true,if_true,Bool.false_eq_true,if_false,altQ1Coeff,altP0Coeff,Option.bind_some,
    altShifts,Ro,Re,regOdo,LO,E,O,domOdo,dr,(WeakStepPaper.regsAt_tiles w).1 _ Ro,(WeakStepPaper.regsAt_tiles w).2.2.1 _ Re,
    List.append_nil,cons_union,std_shift,show pieceUnion [] = ∅ from rfl,Finset.union_empty,doubled,shift_union,shift_shift]
  let P := oddTile v
  let Q := evenTile (threes k)
  let s := vQ1 w+vP2 w
  let a := altOff w (0,0,0,0)
  let b := altOff w (1,2,1,0)
  change shift P (altOff w (0,0,1,0)) ∪ (shift (oddLCells v false true) (altOff w (0,0,1,0)+s) ∪
    (shift (oddLCells v true true) (altOff w (0,0,0,1)) ∪ (shift P (altOff w (0,0,0,1)+s) ∪
    (shift Q a ∪ shift Q b)))) =
    (shift P (altOff w (0,0,1,0)) ∪ shift P (s+altOff w (0,0,1,0))) ∪
    (shift P (altOff w (0,0,0,1)) ∪ shift P (s+altOff w (0,0,0,1))) ∪ shift Q a ∪ shift Q b
  have eu : altOff w (0,0,1,0) = vQ1 w := by ext <;> simp [altOff,coeffOff]
  have ev : altOff w (0,0,0,1) = vQ2 w := by ext <;> simp [altOff,coeffOff]
  rw [eu,ev,add_comm s (vQ1 w),add_comm s (vQ2 w)]
  have h := translated k true
  calc
    _ = (shift Q a ∪ shift Q b) ∪ ((shift (oddLCells v true true) (vQ2 w) ∪ shift (oddLCells v false true) (vQ1 w+s)) ∪
      (shift P (vQ1 w) ∪ shift P (vQ2 w+s))) := by ac_rfl
    _ = _ := by dsimp only [v,w,P,s] at *; simp only [if_true] at h; rw [h]; ac_rfl

end FLatticePaper.Tiles.CorrectedCellsStair
