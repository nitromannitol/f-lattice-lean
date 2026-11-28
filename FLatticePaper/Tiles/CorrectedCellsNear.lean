import FLatticePaper.Tiles.CorrectedCellsColumn
import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.CorrectedCellsOrdinary

/-! The ordinary even corrections of a positive run of twos, and the domain of its odd child after a three. -/

namespace FLatticePaper.Tiles.CorrectedCellsNear

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard PaperAltBase JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt

private abbrev stair (d : ℤ) := nstairN d
private abbrev ladder (d : ℤ) := nladderN (d+1)
private abbrev head (d : ℤ) := shift (nearStairAltF d) (0,-1)
private abbrev enlarged := (tileShape ZTile.oneD).toFinset

private def inStair (d x y : ℤ) : Prop :=
  (0 ≤ x ∧ x ≤ d+1 ∧ 0 ≤ y ∧ y ≤ 2*d-2 ∧ -2 ≤ y-x ∧ y-x ≤ d-1) ∨
  (x = 0 ∧ y = d) ∨ (x = d+1 ∧ y = d-2)

private def inLadder (d x y : ℤ) : Prop :=
  ((x = -1 ∧ y = 2*d+2) ∨ (x = d+2 ∧ y = d-1) ∨ (y-x = d ∧ 0 < x ∧ x < d+1) ∨
  (-1 ≤ x ∧ x ≤ d+2 ∧ 0 ≤ y ∧ y ≤ 3*d+1 ∧ -2 ≤ y-x ∧ y-x ≤ 2*d+2)) ∧
  ¬ ((x = -1 ∧ y ≤ d+1) ∨ (x = d+2 ∧ 2*d ≤ y))

private def inHead (d x y : ℤ) : Prop :=
  (-1 ≤ x ∧ x ≤ 0 ∧ y = 2*d-1) ∨ (d ≤ x ∧ x ≤ d+1 ∧ y = d-3) ∨
  (y-x = d-2 ∧ 0 < x ∧ x < d) ∨ (x = -1 ∧ d ≤ y ∧ y ≤ 2*d-1) ∨
  (x = d+1 ∧ d-3 ≤ y ∧ y ≤ 2*d-4) ∨
  (0 ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ 3*d-4 ∧ -2 ≤ y-x ∧ y-x ≤ 2*d-2)

private def inSquare (x y : ℤ) : Prop := 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1
private def inEnlarged (x y : ℤ) : Prop := inSquare x y ∨ (x = -1 ∧ y = 1) ∨ (x = 1 ∧ y = -1)

private theorem stair_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ stair d ↔ inStair d x y := by
  simp only [stair, nstairN, mem_shift, mem_nstairF (by omega : 2 ≤ d), inStair, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem ladder_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ ladder d ↔ inLadder d x y := by
  simp only [ladder, nladderN, mem_shift, mem_nladderF (by omega : 2 ≤ d+1), inLadder, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem head_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ head d ↔ inHead d x y := by
  simp only [head, mem_shift, nearStairAltF, boxF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    inHead, Prod.fst_sub, Prod.snd_sub]
  omega

private theorem square_mem (x y : ℤ) : (x,y) ∈ oneTile ↔ inSquare x y := by
  simp only [oneTile, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, inSquare]
  omega

private theorem enlarged_mem (x y : ℤ) : (x,y) ∈ enlarged ↔ inEnlarged x y := by
  simp only [enlarged, tileShape, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
    Prod.ext_iff, inEnlarged, inSquare]
  omega

private def plusColumn (d : ℤ) : Tile :=
  shift (stair d) (1,1) ∪ oneTile ∪ shift enlarged (1,1) ∪ shift (head d) (0,2)

private def minusColumn (d : ℤ) : Tile :=
  shift (stair d) (-1,d+2) ∪ shift enlarged (d,3*d) ∪ shift (head d) (1,3)

private theorem plus_mem (d x y : ℤ) (hd : 3 ≤ d) :
    (x,y) ∈ plusColumn d ↔ inStair d (x-1) (y-1) ∨ inSquare x y ∨ inEnlarged (x-1) (y-1) ∨ inHead d x (y-2) := by
  simp only [plusColumn, Finset.mem_union, mem_shift, Prod.mk_sub_mk, sub_zero, stair_mem _ _ _ hd,
    square_mem, enlarged_mem, head_mem _ _ _ hd, or_assoc]

private theorem minus_mem (d x y : ℤ) (hd : 3 ≤ d) : (x,y) ∈ minusColumn d ↔
    inStair d (x+1) (y-(d+2)) ∨ inEnlarged (x-d) (y-3*d) ∨ inHead d (x-1) (y-3) := by
  simp only [minusColumn, Finset.mem_union, mem_shift, Prod.mk_sub_mk, sub_neg_eq_add,
    stair_mem _ _ _ hd, enlarged_mem, head_mem _ _ _ hd, or_assoc]

private theorem columns_sub (d : ℤ) (hd : 3 ≤ d) : plusColumn d ⊆ ladder d ∧ minusColumn d ⊆ ladder d := by
  constructor
  · rintro ⟨x,y⟩ h
    rw [plus_mem _ _ _ hd] at h
    rw [ladder_mem _ _ _ hd]
    rcases h with h | h | h | h <;> simp only [inStair, inSquare, inHead, inEnlarged, inLadder] at * <;> omega
  · rintro ⟨x,y⟩ h
    rw [minus_mem _ _ _ hd] at h
    rw [ladder_mem _ _ _ hd]
    rcases h with h | h | h <;> simp only [inStair, inSquare, inHead, inEnlarged, inLadder] at * <;> omega

/-- In the first missing ladder frame, the other head is at `(-1,d+2)` and the retained ladder at `(d,2*d-1)`. -/
private theorem plus_cover (d x y : ℤ) (hd : 3 ≤ d) (h : inLadder d x y) :
    ((x,y) ∈ plusColumn d ∨ inHead d (x+1) (y-(d+2))) ∨ inLadder d (x-d) (y-(2*d-1)) := by
  rw [plus_mem _ _ _ hd]
  unfold inLadder at h
  by_cases hs : y ≤ 2*d-2
  · left; left
    by_cases ht : y-x ≤ 2
    · by_cases hx : x ≤ 1
      · by_cases hy : y ≤ 1
        · exact Or.inr (Or.inl (by unfold inSquare; omega))
        · exact Or.inr (Or.inr (Or.inr (by unfold inHead; omega)))
      · by_cases hy : y ≤ 0
        · exact Or.inr (Or.inr (Or.inl (by unfold inEnlarged inSquare; omega)))
        · exact Or.inl (by unfold inStair; omega)
    · by_cases hx : x ≤ d-2
      · exact Or.inr (Or.inr (Or.inr (by unfold inHead; omega)))
      · exact Or.inl (by unfold inStair; omega)
  · by_cases hx : x ≤ d-1
    · exact Or.inl (Or.inr (by unfold inHead; omega))
    · exact Or.inr (by unfold inLadder; omega)

/-- In the second missing ladder frame the opposite head is at `(2,3-d)`. -/
private theorem minus_cover (d x y : ℤ) (hd : 3 ≤ d) (h : inLadder d x y) :
    ((x,y) ∈ minusColumn d ∨ inHead d (x-2) (y-(3-d))) ∨ inLadder d (x+d) (y+(2*d-1)) := by
  rw [minus_mem _ _ _ hd]
  unfold inLadder at h
  by_cases hs : y ≤ d+2
  · by_cases hx : x ≤ 1
    · exact Or.inr (by unfold inLadder; omega)
    · exact Or.inl (Or.inr (by unfold inHead; omega))
  · left; left
    by_cases ht : y-x ≤ 2*d-3
    · by_cases hx : x ≤ 2
      · exact Or.inl (by unfold inStair; omega)
      · exact Or.inr (Or.inr (by unfold inHead; omega))
    · by_cases hy : y ≤ 3*d-2
      · exact Or.inl (by unfold inStair; omega)
      · by_cases hx : x ≤ d-2
        · exact Or.inl (by unfold inStair; omega)
        · by_cases hb : x ≤ d ∧ y ≤ 3*d
          · exact Or.inl (by unfold inStair; omega)
          · exact Or.inr (Or.inl (by unfold inEnlarged inSquare; omega))

private abbrev twos (k : ℕ) := List.replicate k Digit.two
private def denom (k : ℕ) : ℤ := 2*(k : ℤ)+3
private abbrev U (d : ℤ) : Site := (d+2,d)
private abbrev B (d : ℤ) : Site := (d,2*d-1)

private theorem exchange (d : ℤ) (hd : 3 ≤ d) :
    (shift (plusColumn d) (U d) ∪ shift (minusColumn d) (B d)) ∪ (ladder d ∪ shift (ladder d) (B d+U d)) =
    (shift (ladder d) (U d) ∪ shift (ladder d) (B d)) ∪ (ladder d ∪ shift (ladder d) (B d+U d)) := by
  obtain ⟨sp,sm⟩ := columns_sub d hd
  ext ⟨x,y⟩
  simp only [Finset.mem_union, mem_shift, U, B, Prod.mk_add_mk, Prod.mk_sub_mk]
  constructor
  · rintro ((hp|hm)|hr)
    exacts [Or.inl (Or.inl (sp hp)), Or.inl (Or.inr (sm hm)), Or.inr hr]
  · rintro ((hp|hm)|hr)
    · rcases plus_cover d _ _ hd ((ladder_mem _ _ _ hd).1 hp) with (h|h)|h
      · exact Or.inl (Or.inl h)
      · apply Or.inl; apply Or.inr; apply (minus_mem _ _ _ hd).2; right; right
        convert h using 1 <;> ring
      · apply Or.inr; apply Or.inr; apply (ladder_mem _ _ _ hd).2
        convert h using 1 <;> ring
    · rcases minus_cover d _ _ hd ((ladder_mem _ _ _ hd).1 hm) with (h|h)|h
      · exact Or.inl (Or.inr h)
      · apply Or.inl; apply Or.inl; apply (plus_mem _ _ _ hd).2; right; right; right
        convert h using 1 <;> ring
      · apply Or.inr; apply Or.inl; apply (ladder_mem _ _ _ hd).2
        convert h using 1 <;> ring
    · exact Or.inr hr

private theorem two_regs (k : ℕ) : regsAt (twos (k+1)) = (some (twos k), none) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show twos (k+1+1) = twos (k+1)++[.two] from List.replicate_succ', WeakStepPaper.regsAt_snoc, ih]
    rfl

private theorem prefix_pieces (k : ℕ) :
    stemE (twos (k+1)) = stair (denom k) ∧ bridgeE (twos (k+1)) = oneTile ∧ headE (twos (k+1)) = head (denom k) := by
  simp only [stemE, bridgeE, headE, two_regs, regOdo, cellData, domOdo, altOddT,
    AltRotStep.altOddTile_of_base _ (AltRotStep.isBase_replicate_two k)]
  refine ⟨SiteBase.oddTile_rep_two _, trivial, ?_⟩
  change (AltRotStep.B (twos k)).1 = _
  cases k with
  | zero => rfl
  | succ k => rw [AltRotStep.B_two _ (by omega)]; rfl

private theorem pos_last (k : ℕ) : (twos (k+1)).getLast? = some .two := by
  rw [show twos (k+1) = twos k++[.two] from List.replicate_succ']; simp

private theorem two_column (k : ℕ) :
    evenLCells (twos (k+1)) true false = plusColumn (denom k) ∧
    evenLCells (twos (k+1)) false false = minusColumn (denom k) := by
  have et : twos (k+1) = twos k++[.two] := List.replicate_succ'
  have hs : stripTrailing .three (twos (k+1)) = twos (k+1) := by rw [et,JointRot.stripTrailing_snoc]; rfl
  have ht : trailingCount .three (twos (k+1)) = 0 := by rw [et,JointRot.trailingCount_snoc]; rfl
  have ho : W1Odd (twos (k+1)) = false := by simp [W1Odd,twos,BaseTileProps.phase_two]
  have hdb : (!(twos (k+1)).isEmpty && (twos (k+1)).all (fun d => decide (d = Digit.two))) = true := by
    simp [twos,List.replicate_succ]
  obtain ⟨st,br,hd⟩ := prefix_pieces k
  have img (T : Tile) (v : Site) : T.image (· + v) = shift T v := rfl
  have single (F : ℕ → Tile) : (Finset.range 1).biUnion F = F 0 := by simp
  constructor <;> rw [CorrectedCellsColumn.even_column,hs,ht,ho]
  all_goals simp only [evenLRel, pos_last, hdb, st, br, hd, single, decide_true, Bool.not_false, Bool.not_true,
    Bool.true_and, Bool.false_eq_true, if_true, if_false, zero_smul, zero_add,
    Int.natCast_zero, one_smul, Finset.union_empty, img, shift_union, shift_shift,
    evenLInitOff, q0Off, SurgicalDict.offsetQ0, ho, evenKCoeff]
  all_goals
    simp only [plusColumn, minusColumn, head, shift_shift, altOff, coeffOff, vP1, vQ1, vP2, vQ2,
      BaseTileProps.parents_two, twos, texV1Odd, texV1Even, texV2, denom, Prod.mk_add_mk,
      Nat.cast_add, Nat.cast_one, Prod.fst_zero, Prod.snd_zero, add_zero, zero_add, mul_one, one_mul,
      zero_mul, neg_mul, sub_self]
    ring_nf
  rw [show shift oneTile (0,0) = oneTile from AltRotStep.shift_zero _]

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev LE (v : Word) (s e : Bool) := domOdo (evenLCells v s e)

private theorem prefix_ladder (k : ℕ) : evenTile (twos (k+1)) = ladder (denom k) := by
  rw [SiteBase.evenTile_rep_two _ (by omega)]
  unfold ladder denom
  congr 1

/-- Both short L-corrections are contained in the full even tile at every positive pure-two prefix. -/
theorem short_subset (k : ℕ) (s : Bool) : evenLCells (twos (k+1)) s false ⊆ evenTile (twos (k+1)) := by
  rw [prefix_ladder]
  obtain ⟨hp,hm⟩ := columns_sub (denom k) (by unfold denom; omega)
  cases s
  · rw [(two_column k).2]; exact hm
  · rw [(two_column k).1]; exact hp

private theorem cons_union (p : Piece) (ps : List Piece) :
    pieceUnion (p::ps) = p.placed ∪ pieceUnion ps := rfl

private theorem std_shift (o : PartialOdometer) (v a : Site) : (stdPiece o v a).placed = shift o.dom v := rfl

/-- After any positive pure-two prefix, the ordinary even corrections cover exactly the standard odd child. -/
theorem odd_two_run_three (k : ℕ) :
    let w := twos (k+1) ++ [.three]
    pieceUnion (tileOddPieces cellData O E LE w) = oddTile w := by
  let v := twos (k+1)
  let w := v++[.three]
  change pieceUnion (tileOddPieces cellData O E LE w) = oddTile w
  have hn : ¬ IsBase w := by simp [w,v,twos,IsBase,List.mem_replicate,List.append_eq_nil_iff]
  have ho : W1Odd w = false := by simp [w,v,twos,W1Odd,phase,List.count_replicate]
  have R : regsAt w = (some (twos k), some v) := by
    change regsAt (twos (k+1) ++ [.three]) = _
    rw [WeakStepPaper.regsAt_snoc,two_regs]; rfl
  have Ro : (regsAt w).1 = some (twos k) := congrArg Prod.fst R
  have Re : (regsAt w).2 = some v := congrArg Prod.snd R
  have hp := (WeakStepPaper.regsAt_tiles w).1 _ Ro
  have hq := (WeakStepPaper.regsAt_tiles w).2.2.1 _ Re
  have p : (parentsAt w).odd = ⟨(k : ℤ)+1,(k : ℤ)+2⟩ := by
    change (parentsAt (v++[.three])).odd = _
    rw [parentsAt_append_singleton]; change (parentsAt v).odd = _
    simp [v,twos,BaseTileProps.parents_two,add_assoc]
  have q : (parentsAt w).even = ⟨2*((k+1 : ℕ) : ℤ)+1,2*((k+1 : ℕ) : ℤ)+3⟩ := by
    change (parentsAt (v++[.three])).even = _
    rw [parentsAt_append_singleton]; exact BaseTileProps.cur_even_two (k+1)
  have uq : vQ1 w = U (denom k) := by
    ext <;> simp [vQ1,q,texV1Even,denom] <;> ring
  have bp : vP1 w + vP2 w = B (denom k) := by
    ext <;> simp [vP1,vP2,p,texV1Odd,texV2,denom] <;> ring
  have hT : oddTile w = oddChildB false (stateAt w).tOdd (stateAt w).tEven (parentsAt w).odd (parentsAt w).even := by
    unfold oddTile
    rw [SiteInduction.childTiles_nonbase w hn, stateAt_par]
    change oddChildB (W1Odd w) _ _ _ _ = _
    rw [ho]
  have last : w.getLast? = some Digit.three := by simp [w]
  have drop : w.dropLast = v := by simp [w]
  rw [hT, hp, hq]
  simp only [tileOddPieces, last, decide_true, ho, Bool.true_and, Bool.not_false, Bool.false_eq_true, if_false,
    if_true, cons_union, std_shift, show pieceUnion [] = ∅ from rfl, Finset.union_empty, Ro, Re, regOdo, O, E,
    domOdo, LE, drop, p0Off, SurgicalDict.offsetP0, zero_add, AltRotStep.shift_zero, oddChildB]
  change shift (oddTile _) (vQ1 w + vQ1 w) ∪ (shift (oddTile _) (vQ2 w) ∪ (evenTile v ∪
    (shift (evenLCells v true false) (vQ1 w) ∪ (shift (evenLCells v false false) (vP1 w + vP2 w) ∪
    shift (evenTile v) (vP1 w + vP2 w + vQ1 w))))) =
    evenTile v ∪ shift (evenTile v) (vQ1 w) ∪ shift (evenTile v) (vP1 w + vP2 w) ∪
      shift (evenTile v) (vP1 w + vP2 w + vQ1 w) ∪ shift (oddTile _) (vQ1 w + vQ1 w) ∪ shift (oddTile _) (vQ2 w)
  rw [show evenTile v = _ from prefix_ladder k, show evenLCells v true false = _ from (two_column k).1,
    show evenLCells v false false = _ from (two_column k).2, bp, uq]
  have hx := exchange (denom k) (by unfold denom; omega)
  let d := denom k
  calc
    _ = (shift (oddTile (twos k)) (U d + U d) ∪ shift (oddTile (twos k)) (vQ2 w)) ∪
      ((shift (plusColumn d) (U d) ∪ shift (minusColumn d) (B d)) ∪ (ladder d ∪ shift (ladder d) (B d + U d))) := by ac_rfl
    _ = _ := by rw [hx]; ac_rfl

private def upFoot (d x y : ℤ) := inStair d (x-1) (y+1) ∨ inSquare x (y+2) ∨ inEnlarged (x-1) (y+1)
private def downFoot (d x y : ℤ) := inStair d (x+3) (y-2*d+1) ∨ inEnlarged (x+2-d) (y+3-4*d)

private theorem foot_disjoint (d x y : ℤ) (hd : 3 ≤ d) (p : upFoot d x y) (m : downFoot d x y) : False := by
  unfold upFoot downFoot inEnlarged inStair inSquare at *
  omega

private theorem upper_pivot (d x y : ℤ) (hd : 3 ≤ d) (p : upFoot d x y) (m : inHead d (x+1) (y-d)) :
    x = d ∧ y = 2*d-3 := by
  unfold upFoot inHead inEnlarged inStair inSquare at *
  omega

private theorem lower_pivot (d x y : ℤ) (hd : 3 ≤ d) (p : inHead d x y) (m : downFoot d x y) :
    x = -1 ∧ y = 2*d-1 := by
  unfold downFoot inHead inEnlarged inStair inSquare at *
  omega

private theorem footprints (d x y : ℤ) (hd : 3 ≤ d)
    (p : upFoot d x y ∨ inHead d x y) (m : downFoot d x y ∨ inHead d (x+1) (y-d)) :
    inHead d x y ∧ inHead d (x+1) (y-d) := by
  rcases p with p|p <;> rcases m with m|m
  · exact (foot_disjoint _ _ _ hd p m).elim
  · obtain ⟨rfl,rfl⟩ := upper_pivot _ _ _ hd p m
    exact ⟨by unfold inHead;omega,m⟩
  · obtain ⟨rfl,rfl⟩ := lower_pivot _ _ _ hd p m
    exact ⟨p,by unfold inHead;omega⟩
  · exact ⟨p,m⟩

private theorem good_pair (d x y : ℤ) (hd : 3 ≤ d) (p : inHead d x y) (m : inHead d (x+1) (y-d)) :
    ((x,y+1) ∈ paperNearStairAltTile d ∧ ¬((x,y+1) ∈ paperNearStairAltA d ∧ inStair d (x-1) (y+1))) ∧
    ((x+1,y-d+1) ∈ paperNearStairAltTile d ∧ ¬((x+1,y-d+1) ∈ paperNearStairAltA d ∧ inStair d (x+3) (y-2*d+1))) := by
  simp only [BaseTileProps.mem_nsAlt,paperNearStairAltA,Set.mem_union,Set.mem_setOf_eq,inStair]
  unfold inHead at p m
  iterate 2 constructor
  all_goals first | constructor <;> omega | omega

/-- The common domain of the ordinary corrections at a pure-two exit lies on both adjacent alternate heads.
Each marked exceptional set is avoided there, including the endpoint of the enlarged square. -/
theorem common_heads (k : ℕ) (z : Site) :
    let d := denom k
    let v := twos (k+1)
    let up : Site := (d+2,d+2)
    let down : Site := (d+1,2*d+2)
    z ∈ shift (evenLCells v true false) (U d) → z ∈ shift (evenLCells v false false) (B d) →
    (z-up+(0,1) ∈ paperNearStairAltTile d ∧ ¬(z-up+(0,1) ∈ paperNearStairAltA d ∧
       z-(U d+(1,1)) ∈ stair d)) ∧
    (z-down+(0,1) ∈ paperNearStairAltTile d ∧ ¬(z-down+(0,1) ∈ paperNearStairAltA d ∧
       z-(B d+(-1,d+2)) ∈ stair d)) := by
  dsimp only
  let d := denom k
  have hd : 3 ≤ d := by unfold d denom; omega
  obtain ⟨x,y⟩ := z
  intro p m
  rw [(two_column k).1, mem_shift] at p
  rw [(two_column k).2, mem_shift] at m
  change (x-(d+2),y-d) ∈ plusColumn d at p
  change (x-d,y-(2*d-1)) ∈ minusColumn d at m
  rw [plus_mem _ _ _ hd] at p
  rw [minus_mem _ _ _ hd] at m
  let a := x-(d+2)
  let b := y-(d+2)
  have h₁ : upFoot d a b ∨ inHead d a b := by
    unfold upFoot a b
    rcases p with p|p|p|p
    · left;left; convert p using 1; ring
    · left;right;left;convert p using 1; ring
    · left;right;right;convert p using 1; ring
    · right;convert p using 1; ring
  have h₂ : downFoot d a b ∨ inHead d (a+1) (b-d) := by
    unfold downFoot a b
    rcases m with m|m|m
    · left;left;convert m using 1 <;> ring
    · left;right;convert m using 1 <;> ring
    · right;convert m using 1 <;> ring
  obtain ⟨p',m'⟩ := footprints d a b hd h₁ h₂
  have h := good_pair d a b hd p' m'
  change (((x,y)-(d+2,d+2)+((0,1):Site) ∈ paperNearStairAltTile d) ∧
    ¬((x,y)-(d+2,d+2)+((0,1):Site) ∈ paperNearStairAltA d ∧ (x,y)-(U d+(1,1)) ∈ stair d)) ∧
    (((x,y)-(d+1,2*d+2)+((0,1):Site) ∈ paperNearStairAltTile d) ∧
    ¬((x,y)-(d+1,2*d+2)+((0,1):Site) ∈ paperNearStairAltA d ∧ (x,y)-(B d+(-1,d+2)) ∈ stair d))
  simp only [U,B,Prod.mk_sub_mk,Prod.mk_add_mk,stair_mem _ _ _ hd,add_zero]
  dsimp only [a,b] at h
  ring_nf at h ⊢
  exact h

end FLatticePaper.Tiles.CorrectedCellsNear
