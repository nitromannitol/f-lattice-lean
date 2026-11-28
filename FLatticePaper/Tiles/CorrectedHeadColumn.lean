import FLatticePaper.Tiles.CorrectedColumnRuns

/-! The two strings of alternate parents in a corrected child occupy consecutive positions of one column. -/

namespace FLatticePaper.Tiles.CorrectedHeadColumn

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion SurgicalWeak SurgicalAlt SurgicalDict CorrectedColumnRuns

private abbrev O (w : Word) := domOdo (oddTile w)
private abbrev E (w : Word) := domOdo (evenTile w)
private abbrev AO (w : Word) := domOdo (altOddT w)
private abbrev AE (w : Word) := domOdo (altEvenT w)
private abbrev eHead := JointRot.eHead cellData O E AO AE
private abbrev oHead := JointRot.oHead cellData O E AO AE

/-- The placement of the even L entry of the child obtained by appending a three. -/
def evenOff (v : Word) (plus long : Bool) : Site :=
  let w := v++[Digit.three]
  let o := W1Odd w
  if long then
    if plus then altOff w (altQ0Coeff o .dsQ1Plus)
    else altOff w (altQ0Coeff o .dsQ1Minus)+(altShifts o (vP2 w) (vQ1 w)).2
  else if plus then p0Off w .q1DPlus + (if o then 0 else vQ1 w)
    else p0Off w .q1DMinus + (if o then vQ1 w else 0)

/-- The placement of the odd L entry of the child obtained by appending a two. -/
def oddOff (v : Word) (plus long : Bool) : Site :=
  let w := v++[Digit.two]
  let o := W1Odd w
  if long then
    if plus then altOff w (altP0Coeff o .dsP1Minus)
    else altOff w (altP0Coeff o .dsP1Plus)+(altShifts o (vP2 w) (vQ1 w)).1
  else if plus then q0Off w .p1DMinus else q0Off w .p1DPlus + vP2 w

private abbrev count (k : ℕ) (long : Bool) := 2*(k+1) - if long then 0 else 1

private theorem join (T : Tile) (b a : Site) (m : ℕ) (hm : 0 < m) :
    (Finset.range m).biUnion (fun j => shift T (a+(j : ℤ) • b)) ∪
      (Finset.range m).biUnion (fun j => shift T (a+(m : ℤ) • b-(j : ℤ) • b)) =
      shift (column T b m) a := by
  ext z
  simp only [Finset.mem_union,Finset.mem_biUnion,Finset.mem_range,mem_shift,mem_column]
  constructor
  · rintro (⟨j,hj,h⟩|⟨j,hj,h⟩)
    · exact ⟨j,by omega,by rwa [sub_sub]⟩
    · refine ⟨m-j,by omega,?_⟩
      rw [Nat.cast_sub (by omega),sub_smul]
      convert h using 1; abel
  · rintro ⟨j,hj,h⟩
    by_cases he : j=m
    · subst j; right; refine ⟨0,hm,?_⟩; simpa only [Nat.cast_zero,zero_smul,sub_zero,←sub_sub] using h
    · left; exact ⟨j,by omega,by rwa [←sub_sub]⟩

private theorem head_union (p q : ℕ → Piece) (c d a b : Site) (T : Tile) (m : ℕ) (hm : 0 < m)
    (hp : ∀ i, shift (p i).placed c = shift T (a+(i : ℤ) • b))
    (hq : ∀ i, shift (q i).placed d = shift T (a+(m : ℤ) • b-(i : ℤ) • b)) :
    shift (pieceUnion ((List.range m).map p)) c ∪ shift (pieceUnion ((List.range m).map q)) d = shift (column T b m) a := by
  have hpart (P : ℕ → Piece) (u : Site) : shift (pieceUnion ((List.range m).map P)) u =
      (Finset.range m).biUnion (fun i => shift (P i).placed u) := by
    ext z
    simp only [mem_shift,JointGlue.mem_pieceUnion,List.mem_map,List.mem_range,Finset.mem_biUnion,Finset.mem_range]
    constructor
    · rintro ⟨_,⟨i,hi,rfl⟩,hz⟩; exact ⟨i,hi,hz⟩
    · rintro ⟨i,hi,hz⟩; exact ⟨P i,⟨i,hi,rfl⟩,hz⟩
  simp only [hpart,hp,hq,join T b a m hm]

private abbrev ePre (v : Word) := stripTrailing Digit.three v
private abbrev oPre (v : Word) := stripTrailing Digit.two v
private abbrev eK := JointRot.eK
private abbrev oK := JointRot.oK
private abbrev eStep (v : Word) := vP2 (ePre v)
private abbrev oStep (v : Word) := if W1Odd v then -vQ1 (oPre v) else vQ1 (oPre v)

private theorem e_stride (v : Word) (plus : Bool) : altOff (ePre v) (eK v plus).2.2.2 =
    if plus then eStep v else -eStep v := by
  cases plus <;> cases h : W1Odd v <;> ext <;> simp [eK,JointRot.eK,evenKCoeff,h,altOff,coeffOff,eStep]
private theorem o_stride (v : Word) (plus : Bool) : altOff (oPre v) (oK v plus).2.2.2 =
    if plus then oStep v else -oStep v := by
  cases plus <;> cases h : W1Odd v <;> ext <;> simp [oK,JointRot.oK,oddKCoeff,h,altOff,coeffOff,oStep]

private theorem e_at (v : Word) (plus : Bool) (i : ℕ) : (eHead v plus i).off =
    (eHead v plus 0).off + (i : ℤ) • (if plus then eStep v else -eStep v) := by
  change evenLInitOff v plus + altOff (ePre v) (_ + ((i : ℤ)+1) • (eK v plus).2.2.2) =
    evenLInitOff v plus + altOff (ePre v) (_ + (((0 : ℕ) : ℤ)+1) • (eK v plus).2.2.2) + _
  simp only [altOff_add,altOff_smul,Nat.cast_zero,zero_add,add_smul,one_smul,e_stride]
  abel

private theorem o_at (v : Word) (plus : Bool) (i : ℕ) : (oHead v plus i).off =
    (oHead v plus 0).off + (i : ℤ) • (if plus then oStep v else -oStep v) := by
  change oddLInitOff v plus + altOff (oPre v) (_ + ((i : ℤ)+1) • (oK v plus).2.2.2) =
    oddLInitOff v plus + altOff (oPre v) (_ + (((0 : ℕ) : ℤ)+1) • (oK v plus).2.2.2) + _
  simp only [altOff_add,altOff_smul,Nat.cast_zero,zero_add,add_smul,one_smul,o_stride]
  abel

private theorem three_periods (w : Word) (k : ℕ) :
    let v := w++List.replicate k Digit.three
    vP1 v = vP1 w ∧ vP2 v = vP2 w ∧ vQ1 v = vQ1 w + (k : ℤ) • vP1 w ∧
      vQ2 v = vQ2 w + (2*(k : ℤ)) • vP2 w := by
  dsimp only
  simp only [vP1,vP2,vQ1,vQ2,JointRot.parents_append_threes,texV1Odd,texV1Even,texV2]
  refine ⟨trivial,trivial,?_,?_⟩ <;> ext <;> dsimp <;> ring

private theorem two_periods (w : Word) (k : ℕ) :
    let v := w++List.replicate k Digit.two
    vP1 v = vP1 w + (2*(k : ℤ)) • vQ1 w ∧ vP2 v = vP2 w + (k : ℤ) • vQ2 w ∧
      vQ1 v = vQ1 w ∧ vQ2 v = vQ2 w := by
  dsimp only
  simp only [vP1,vP2,vQ1,vQ2,JointRot.parents_append_twos,texV1Odd,texV1Even,texV2]
  refine ⟨?_,?_,trivial,trivial⟩ <;> ext <;> dsimp <;> ring

set_option maxHeartbeats 400000 in
private theorem even_ends (v : Word) (long : Bool) :
    (eHead v false 0).off + evenOff v false long =
      (eHead v true 0).off + evenOff v true long +
      (count (trailingCount .three v) long : ℤ) • eStep v := by
  let pre := ePre v
  let k := trailingCount .three v
  have ev : pre++List.replicate k .three = v := JointRot.strip_append_replicate _ _
  have ew : pre++List.replicate (k+1) .three = v++[.three] := by rw [List.replicate_succ',←List.append_assoc,ev]
  obtain ⟨a,b,c,d⟩ := ev ▸ three_periods pre k
  obtain ⟨a',b',c',d'⟩ := ew ▸ three_periods pre (k+1)
  have hw : W1Odd (v++[.three]) = W1Odd v := JointRot.phase_snoc_three _
  have n (l : Bool) : (count k l : ℤ) = 2*(k : ℤ)+ (if l then 2 else 1) := by cases l <;> dsimp [count] <;> omega
  change _ = _ + (count k long : ℤ) • eStep v
  rw [n]
  cases h : W1Odd v <;> cases long <;> cases s : decide ((ePre v).getLast? = some Digit.two)
  all_goals apply Prod.ext
  all_goals simp [eHead,JointRot.eHead,JointRot.eK,evenOff,evenLInitOff,evenKCoeff,hw,h,s,
    ePre,eStep,altQ0Coeff,altShifts,q0Off,p0Off,offsetQ0,offsetP0,
    altOff,coeffOff,b,c,d,a',b',c',d',k,pre]; ring

set_option maxHeartbeats 400000 in
private theorem odd_ends (v : Word) (long : Bool) :
    (oHead v false 0).off + oddOff v false long =
      (oHead v true 0).off + oddOff v true long +
      (count (trailingCount .two v) long : ℤ) • oStep v := by
  let pre := oPre v
  let k := trailingCount .two v
  have ev : pre++List.replicate k .two = v := JointRot.strip_append_replicate _ _
  have ew : pre++List.replicate (k+1) .two = v++[.two] := by rw [List.replicate_succ',←List.append_assoc,ev]
  obtain ⟨a,b,c,d⟩ := ev ▸ two_periods pre k
  obtain ⟨a',b',c',d'⟩ := ew ▸ two_periods pre (k+1)
  have hw : W1Odd (v++[.two]) = W1Odd v := JointRot.phase_snoc_two _
  have n (l : Bool) : (count k l : ℤ) = 2*(k : ℤ)+ (if l then 2 else 1) := by cases l <;> dsimp [count] <;> omega
  change _ = _ + (count k long : ℤ) • oStep v
  rw [n]
  cases h : W1Odd v <;> cases long
  all_goals apply Prod.ext
  all_goals simp [oHead,JointRot.oHead,JointRot.oK,oddOff,oddLInitOff,oddKCoeff,hw,h,
    oPre,oStep,altP0Coeff,altShifts,q0Off,p0Off,offsetQ0,offsetP0,
    altOff,coeffOff,a,b,c,a',b',c',d',k,pre]; ring

/-- In the ordinary odd child and the elongated even alternate child, all the actual even-L heads together
occupy every translate from the positive initial head to the negative initial head. -/
theorem even_heads (v : Word) (long : Bool) :
    let m := count (trailingCount .three v) long
    shift (pieceUnion ((List.range m).map (eHead v true))) (evenOff v true long) ∪
      shift (pieceUnion ((List.range m).map (eHead v false))) (evenOff v false long) =
    shift (column (headE (ePre v)) (eStep v) m) ((eHead v true 0).off + evenOff v true long) := by
  dsimp only
  apply head_union
  · cases long <;> dsimp [count] <;> omega
  · intro i
    change shift (shift (headE (ePre v)) _) _ = _
    rw [shift_shift,e_at]
    simp only [if_true]; congr 1; abel
  · intro i
    change shift (shift (headE (ePre v)) _) _ = _
    rw [shift_shift,e_at]
    simp only [Bool.false_eq_true,if_false,smul_neg]
    congr 1; rw [add_right_comm,even_ends]; abel

/-- The corresponding odd-L heads of the standard even and alternate odd children, in their signed horizontal direction. -/
theorem odd_heads (v : Word) (long : Bool) :
    let m := count (trailingCount .two v) long
    shift (pieceUnion ((List.range m).map (oHead v true))) (oddOff v true long) ∪
      shift (pieceUnion ((List.range m).map (oHead v false))) (oddOff v false long) =
    shift (column (headO (oPre v)) (oStep v) m) ((oHead v true 0).off + oddOff v true long) := by
  dsimp only
  apply head_union
  · cases long <;> dsimp [count] <;> omega
  · intro i
    change shift (shift (headO (oPre v)) _) _ = _
    rw [shift_shift,o_at]
    simp only [if_true]; congr 1; abel
  · intro i
    change shift (shift (headO (oPre v)) _) _ = _
    rw [shift_shift,o_at]
    simp only [Bool.false_eq_true,if_false,smul_neg]
    congr 1; rw [add_right_comm,odd_ends]; abel

end FLatticePaper.Tiles.CorrectedHeadColumn
