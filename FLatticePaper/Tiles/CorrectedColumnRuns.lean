import FLatticePaper.Tiles.CorrectedCellsEnds
import FLatticePaper.Tiles.AltRotStep
import FLatticePaper.Tiles.JointRot

/-! Exterior ends, interior joins and the extra vertical segments in columns of base alternate parents. -/

namespace FLatticePaper.Tiles.CorrectedColumnRuns

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open Standard PaperAltBase JointFamily LCorrecProps LCorrecRecursion SurgicalWeak

/-- The copies of a tile at offsets from zero through `k • v`. -/
def column (T : Tile) (v : Site) (k : ℕ) : Tile :=
  (Finset.range (k+1)).biUnion (fun i => shift T ((i : ℤ) • v))

theorem mem_column (T : Tile) (v : Site) (k : ℕ) (z : Site) :
    z ∈ column T v k ↔ ∃ i ≤ k, z - (i : ℤ) • v ∈ T := by
  simp only [column,Finset.mem_biUnion,Finset.mem_range,mem_shift,Nat.lt_succ_iff]

theorem column_union (P Q : Tile) (v : Site) (k : ℕ) :
    column (P ∪ Q) v k = column P v k ∪ column Q v k := by
  ext z
  simp only [mem_column,Finset.mem_union]
  constructor
  · rintro ⟨j,hj,h|h⟩
    exacts [Or.inl ⟨j,hj,h⟩,Or.inr ⟨j,hj,h⟩]
  · rintro (⟨j,hj,h⟩|⟨j,hj,h⟩)
    exacts [⟨j,hj,Or.inl h⟩,⟨j,hj,Or.inr h⟩]

theorem column_shift (T : Tile) (u v : Site) (k : ℕ) :
    column (shift T u) v k = shift (column T v k) u := by
  ext z
  simp only [mem_column,mem_shift]
  constructor <;> rintro ⟨j,hj,h⟩ <;> refine ⟨j,hj,?_⟩ <;> convert h using 1 <;> abel

private abbrev B (d : ℤ) : Site := (1-d,d+1)
private abbrev L (d : ℤ) : Tile := {(d+1,0),(d+1,1)}
private abbrev U (d : ℤ) : Tile := {(0,d+2),(0,d+3)}
private def H (d : ℤ) := shift (ladderAltF d) (1,1)

private theorem holes (d : ℤ) (hd : 4 ≤ d) :
    (∀ z ∈ H d, 0 ≤ z.2 ∧ z.2 ≤ d+3 ∧ z ∉ L d ∧ z ∉ U d) ∧
    (∀ z ∈ L d, z+B d ∈ H d) ∧ (∀ z ∈ U d, z-B d ∈ H d) := by
  constructor
  · rintro ⟨x,y⟩ h
    simp only [H,mem_shift,ladderAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
      Prod.mk_sub_mk,Prod.mk.injEq] at h
    simp only [L,U,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
    omega
  constructor <;> rintro z hz
  all_goals simp only [L,U,Finset.mem_insert,Finset.mem_singleton] at hz
  all_goals rcases hz with rfl|rfl <;> simp only [H,B,mem_shift,ladderAltF,boxF,Finset.mem_filter,
    Finset.mem_product,Finset.mem_Icc,Prod.mk_add_mk,Prod.mk_sub_mk,Prod.mk.injEq] <;> omega

/-- For the odd alternate parent in a pure-three base family, filling its two pairs of missing sites and taking an
arbitrarily long column introduces precisely the lower pair in the first copy and the upper pair in the last copy. -/
theorem ladder_column (d : ℤ) (hd : 4 ≤ d) (k : ℕ) :
    column (H d) (B d) k =
      column (H d ∪ L d ∪ U d) (B d) k \ (L d ∪ shift (U d) ((k : ℤ) • B d)) := by
  obtain ⟨bound,lo,hi⟩ := holes d hd
  ext z
  simp only [Finset.mem_sdiff,Finset.mem_union,mem_column,mem_shift]
  constructor
  · rintro ⟨i,ik,h⟩
    obtain ⟨yl,yu,ol,ou⟩ := bound _ h
    refine ⟨⟨i,ik,Or.inl (Or.inl h)⟩,?_⟩
    rintro (xz|xz)
    · by_cases eq : i=0
      · subst i; simp only [Nat.cast_zero,zero_smul,sub_zero] at ol; exact ol xz
      have hp : d+1 ≤ (i : ℤ)*(d+1) := by nlinarith [mul_nonneg (show 0 ≤ (i : ℤ)-1 by omega) (show 0 ≤ d+1 by omega)]
      change 0 ≤ z.2 - (i : ℤ)*(d+1) at yl
      rcases Finset.mem_insert.mp xz with rfl|xz
      · dsimp at yl; omega
      · rw [Finset.mem_singleton] at xz; subst z; dsimp at yl; omega
    · by_cases eq : i=k
      · subst i; exact ou xz
      have hp : (i : ℤ)*(d+1)+(d+1) ≤ (k : ℤ)*(d+1) := by
        nlinarith [mul_nonneg (show 0 ≤ (k : ℤ)-(i : ℤ)-1 by omega) (show 0 ≤ d+1 by omega)]
      have htop : d+2 ≤ (z-(k : ℤ) • B d).2 := by
        change _ ∈ ({(0,d+2),(0,d+3)} : Tile) at xz
        simp only [Finset.mem_insert,Finset.mem_singleton] at xz
        rcases xz with e|e
        · rw [e]
        · rw [e]; dsimp; omega
      change z.2 - (i : ℤ)*(d+1) ≤ d+3 at yu
      change d+2 ≤ z.2 - (k : ℤ)*(d+1) at htop
      omega
  · rintro ⟨⟨i,ik,(h|h)|h⟩,hout⟩
    · exact ⟨i,ik,h⟩
    · cases i with
      | zero =>
        simp only [Nat.cast_zero,zero_smul,sub_zero] at h
        exact (hout (Or.inl h)).elim
      | succ i =>
        refine ⟨i,by omega,?_⟩
        have good := lo _ h
        convert good using 1
        push_cast
        rw [add_smul,one_smul];abel
    · by_cases eq : i=k
      · subst i; exact (hout (Or.inr h)).elim
      refine ⟨i+1,by omega,?_⟩
      have good := hi _ h
      convert good using 1
      push_cast
      rw [add_smul,one_smul];abel

private def vertical (d : ℤ) : Tile := {0} ×ˢ Finset.Icc 0 (d-1)

/-- The union of the extra strips of a pure-two head has exactly one vertical segment on each of the columns
`0,-1,...,-k`. The transverse coordinate is free throughout the segment, including its ends. -/
theorem near_segments (d : ℤ) (k : ℕ) (x y : ℤ) :
    (x,y) ∈ column (vertical d) (-1,d) k ↔ -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d := by
  rw [mem_column]
  change (∃ i ≤ k, (x,y)-(i : ℤ) • ((-1,d):Site) ∈ _ ×ˢ Finset.Icc 0 (d-1)) ↔ _
  simp only [Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc]
  change (∃ i : ℕ, i ≤ k ∧ x - (i : ℤ)*(-1) = 0 ∧ 0 ≤ y-(i : ℤ)*d ∧ y-(i : ℤ)*d ≤ d-1) ↔ _
  constructor
  · rintro ⟨i,ik,h,hl,hu⟩
    have eq : x = -(i : ℤ) := by omega
    subst x
    rw [mul_neg,mul_comm d]
    omega
  · rintro ⟨hk,hx,hl,hu⟩
    refine ⟨(-x).toNat,by omega,?_⟩
    have eq : (((-x).toNat : ℕ) : ℤ) = -x := by omega
    rw [eq]
    constructor
    · ring
    · rw [show y-(-x)*d = y+d*x by ring]; omega

/-- The part of the normalized near-stair alternate parent in the closed strip of columns from 0 to d. -/
def nearInterior (d : ℤ) : Tile :=
  (shift (nearStairAltF d) (0,-1)).filter (fun z => 0 ≤ z.1 ∧ z.1 ≤ d)

private theorem near_split (d : ℤ) (hd : 3 ≤ d) :
    shift (nearStairAltF d) (0,-1) = nearInterior d ∪
      shift (vertical d) (-1,d) ∪ shift (vertical d) (d+1,d-3) := by
  ext ⟨x,y⟩
  simp only [nearInterior,Finset.mem_union,Finset.mem_filter]
  constructor
  · intro h
    by_cases mid : 0 ≤ x ∧ x ≤ d
    · exact Or.inl (Or.inl ⟨h,mid⟩)
    simp only [mem_shift,nearStairAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,Prod.mk_sub_mk] at h
    by_cases e : x < 0
    · apply Or.inl; apply Or.inr
      simp only [mem_shift,vertical,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,Prod.mk_sub_mk]
      omega
    · apply Or.inr
      simp only [mem_shift,vertical,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,Prod.mk_sub_mk]
      omega
  · rintro ((⟨h,_⟩|h)|h)
    · exact h
    all_goals
      simp only [mem_shift,vertical,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,Prod.mk_sub_mk] at h
      simp only [mem_shift,nearStairAltF,boxF,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,Prod.mk_sub_mk]
      omega

/-- In every column of pure-two alternate heads the two extra segments run along the exterior columns of the
base tile. Their placements include both endpoints of all the segments. -/
theorem near_column (d : ℤ) (hd : 3 ≤ d) (k : ℕ) (z : Site) :
    z ∈ column (shift (nearStairAltF d) (0,-1)) (-1,d) k ↔
    z ∈ column (nearInterior d) (-1,d) k ∨
      (let x := z.1+1; let y := z.2-d; -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) ∨
      (let x := z.1-(d+1); let y := z.2-(d-3); -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) := by
  obtain ⟨x,y⟩ := z
  rw [near_split d hd,column_union,column_union,column_shift,column_shift]
  simp only [Finset.mem_union,mem_shift,Prod.mk_sub_mk,sub_neg_eq_add,near_segments,or_assoc]

private theorem after_register (u : Word) (s : Digit) (hs : s = .one ∨ s = .two) :
    headE (u++[s]) = altOddT u := by
  rcases hs with rfl|rfl <;> simp only [headE,WeakStepPaper.regsAt_snoc,regStep,regOdo,domOdo]

/-- The column at either eligible exit from a positive pure-three word loses exactly its two exterior pairs. -/
theorem three_register (j k : ℕ) (s : Digit) (hs : s = .one ∨ s = .two) :
    let u := List.replicate (j+1) Digit.three
    let d := 2*((j+1 : ℕ) : ℤ)+2
    column (headE (u++[s])) (B d) k =
      column (H d ∪ L d ∪ U d) (B d) k \ (L d ∪ shift (U d) ((k : ℤ) • B d)) := by
  dsimp only
  rw [after_register _ _ hs,altOddT,AltRotStep.altOddTile_of_base _ (AltRotStep.isBase_replicate_three _)]
  change column (AltRotStep.B (List.replicate (j+1) Digit.three)).1 _ _ = _
  rw [AltRotStep.B_three (j+1) (by omega)]
  exact ladder_column _ (by omega) k

/-- The actual odd alternate register at either eligible exit from a pure-two word, including the empty word. -/
theorem two_register (j k : ℕ) (s : Digit) (hs : s = .one ∨ s = .two) (z : Site) :
    let u := List.replicate j Digit.two
    let d := 2*(j : ℤ)+3
    z ∈ column (headE (u++[s])) (-1,d) k ↔ z ∈ column (nearInterior d) (-1,d) k ∨
      (let x := z.1+1; let y := z.2-d; -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) ∨
      (let x := z.1-(d+1); let y := z.2-(d-3); -(k : ℤ) ≤ x ∧ x ≤ 0 ∧ 0 ≤ y+d*x ∧ y+d*x < d) := by
  dsimp only
  rw [after_register _ _ hs,altOddT,AltRotStep.altOddTile_of_base _ (AltRotStep.isBase_replicate_two _)]
  change z ∈ column (AltRotStep.B (List.replicate j Digit.two)).1 _ _ ↔ _
  cases j with
  | zero => exact near_column 3 (by decide) k z
  | succ j =>
    rw [AltRotStep.B_two _ (by omega)]
    exact near_column _ (by omega) k z

end FLatticePaper.Tiles.CorrectedColumnRuns
