import FLatticePaper.Tiles.ClosedPathAssembly
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.SiteBase
import FLatticePaper.Tiles.WeakStepPaper

/-! Mixed interfaces after a run of twos. The heights of the two near-one
parents have the same square term in the diagonal coordinate. All placement
vectors preserve its parity. Multiplying by four removes the integer division
before the comparisons of linear terms on the two tiles. -/

namespace FLatticePaper.Tiles.MixedCompatNear

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathCycle
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.BaseTileProps

private def stairTerm (e x y : ℤ) : ℤ :=
  min (e-y) 0 + if (x=0 ∧ y=e+1) ∨ (x=e+1 ∧ y=e-1) then 1 else 0

private def ladderTerm (d x y : ℤ) : ℤ :=
  min 0 (d-y) + min 0 (2*d-y) + max (y-x-d) 0 +
    if (x= -1 ∧ y=2*d+1) ∨ (x=d+1 ∧ y=d-1) ∨ (y-x=d ∧ 0<x ∧ x<d) then 1 else 0

private def diag (a : Site) := a.2-a.1

private theorem four_square (x : ℤ) : 4 * (x^2 / 4) = x^2 - x % 2 := by
  by_cases h : x % 2 = 0
  · have he : x = 2*(x/2) := by omega
    rw [sq4_even x _ he, h]
    conv_rhs => rw [he]
    ring
  · have ho : x = 2*(x/2)+1 := by omega
    rw [sq4_odd x _ ho, show x%2=1 by omega]
    conv_rhs => rw [ho]
    ring

private def row (k : ℤ) (one : Bool) (a b s t : Site) (c : ℤ) : Prop :=
  let d := 2*k+2
  let e := if one then d+1 else d-1
  (diag a - diag b) % 2 = 0 ∧
  ∀ x y : ℤ, (x-a.1,y-a.2) ∈ nstairN e → (x-b.1,y-b.2) ∈ nladderN d →
    4*(stairTerm e (x-a.1) (y-a.2+1) - ladderTerm d (x-b.1) (y-b.2+1)) +
      (4*(s.1-t.1)-2*(diag a-diag b))*x + (4*(s.2-t.2)+2*(diag a-diag b))*y = 4*c

private abbrev d (k : ℤ) := 2*k+2
private abbrev e (k : ℤ) (one : Bool) := if one then d k+1 else d k-1
private abbrev p (k : ℤ) (one : Bool) : Fraction := if one then ⟨k+1,k+2⟩ else ⟨k,k+1⟩
private abbrev q (k : ℤ) : Fraction := ⟨2*k+1,2*k+3⟩

private theorem raw_row (k : ℤ) (one : Bool) (a b s t z : Site) (c : ℤ) (hr : row k one a b s t c)
    (hp : z-a ∈ nstairN (e k one)) (hq : z-b ∈ nladderN (d k)) :
    paperNearStairValue (e k one) (z-a+(0,1)) + dot2 s z -
      (paperNearLadderValue (d k) (z-b+(0,1)) + dot2 t z) =
      (4*c + 2*(diag a-diag b) - (diag a)^2 + (diag b)^2)/4 := by
  obtain ⟨hmod, hrow⟩ := hr
  have hv := hrow z.1 z.2 hp hq
  let U := z.2-a.2+1-(z.1-a.1)
  let V := z.2-b.2+1-(z.1-b.1)
  have hUV : U % 2 = V % 2 := by dsimp [U,V,diag] at hmod ⊢; omega
  have sq : 4*(U^2/4)-4*(V^2/4)=U^2-V^2 := by rw [four_square, four_square,hUV]; ring
  have hP : paperNearStairValue (e k one) (z-a+(0,1)) =
      -(U^2/4) + stairTerm (e k one) (z.1-a.1) (z.2-a.2+1) := by
    change paperNearStairValue _ (z.1-a.1+0,z.2-a.2+1) = _
    simp only [paperNearStairValue, stairTerm, Prod.mk.injEq, add_zero, U]
    abel
  have hQ : paperNearLadderValue (d k) (z-b+(0,1)) =
      -(V^2/4) + ladderTerm (d k) (z.1-b.1) (z.2-b.2+1) := by
    change paperNearLadderValue _ (z.1-b.1+0,z.2-b.2+1) = _
    rw [pnlV]
    simp only [ladderTerm, Prod.mk.injEq, add_zero, V]
    abel
  rw [hP,hQ]
  have he : 4 * (-(U^2/4) + stairTerm (e k one) (z.1-a.1) (z.2-a.2+1) + dot2 s z -
      (-(V^2/4) + ladderTerm (d k) (z.1-b.1) (z.2-b.2+1) + dot2 t z)) =
      4*c + 2*(diag a-diag b) - (diag a)^2 + (diag b)^2 := by
    dsimp only [U,V,diag,dot2,e,d] at hv sq ⊢
    linear_combination hv - sq
  omega

private def oddRows (k : ℤ) (one : Bool) : List ℤ :=
  if one then [-2,0,0,2*k+2,-8*k-9,-8*k-13,0,-6*k-5]
  else [0,4,0,4*k+6,1,0,2*k+3,0]

private def evenRows (k : ℤ) (one : Bool) : List ℤ :=
  if one then [-2,0,-2,-1,-4*k-7,-4*k-6,0,-6*k-7]
  else [2,0,-2*k-1,2*k+2,1,4*k+4,0,4*k+6]

local macro "check_odd" kk:ident flag:term : tactic =>
  `(tactic| (
    have he : 3 ≤ e $kk $flag := by unfold e d; omega
    have hd : 4 ≤ d $kk := by unfold d; omega
    constructor
    · simp [diag, pOffsetsOdd, qOffsetsOdd, texV1Even, texV1Odd, texV2, p, q] <;> omega
    · intro x y hx hy
      rw [mem_nstairN_ab, mem_nstairF_ab _ he] at hx
      rw [mem_nladderN_ab, mem_nladderF_ab _ hd] at hy
      simp [pOffsetsOdd, qOffsetsOdd, affOdd, p, q, texV1Even, texV1Odd, texV2, oddRows,
        diag, e, d, ladderTerm, stairTerm, min_def, max_def] at hx hy ⊢
      ring_nf
      grind))

local macro "check_even" kk:ident flag:term : tactic =>
  `(tactic| (
    have he : 3 ≤ e $kk $flag := by unfold e d; omega
    have hd : 4 ≤ d $kk := by unfold d; omega
    constructor
    · simp [diag, pOffsetsEven, qOffsetsEven, texV1Even, texV1Odd, texV2, p, q] <;> omega
    · intro x y hx hy
      rw [mem_nstairN_ab, mem_nstairF_ab _ he] at hx
      rw [mem_nladderN_ab, mem_nladderF_ab _ hd] at hy
      simp [pOffsetsEven, qOffsetsEven, affEven, p, q, texV1Even, texV1Odd, texV2, evenRows,
        diag, e, d, ladderTerm, stairTerm, min_def, max_def] at hx hy ⊢
      ring_nf
      grind))

section
variable (k : ℤ) (hk : 1 ≤ k)
include hk
set_option maxHeartbeats 400000

private abbrev oddRow (k : ℤ) (one : Bool) (i j : ℕ) :=
  row k one ((pOffsetsOdd one (p k one) (q k)).getD i 0)
    ((qOffsetsOdd one (p k one) (q k)).getD j 0)
    (affOdd (p k one) (q k) i) (affOdd (p k one) (q k) (j + 2))
    ((oddRows k one).getD (4 * i + j) 0)

private theorem odd_false_00 : oddRow k false 0 0 := by
  check_odd k false
private theorem odd_false_01 : oddRow k false 0 1 := by
  check_odd k false
private theorem odd_false_02 : oddRow k false 0 2 := by
  check_odd k false
private theorem odd_false_03 : oddRow k false 0 3 := by
  check_odd k false
private theorem odd_false_10 : oddRow k false 1 0 := by
  check_odd k false
private theorem odd_false_11 : oddRow k false 1 1 := by
  check_odd k false
private theorem odd_false_12 : oddRow k false 1 2 := by
  check_odd k false
private theorem odd_false_13 : oddRow k false 1 3 := by
  check_odd k false
private theorem odd_true_00 : oddRow k true 0 0 := by
  check_odd k true
private theorem odd_true_01 : oddRow k true 0 1 := by
  check_odd k true
private theorem odd_true_02 : oddRow k true 0 2 := by
  check_odd k true
private theorem odd_true_03 : oddRow k true 0 3 := by
  check_odd k true
private theorem odd_true_10 : oddRow k true 1 0 := by
  check_odd k true
private theorem odd_true_11 : oddRow k true 1 1 := by
  check_odd k true
private theorem odd_true_12 : oddRow k true 1 2 := by
  check_odd k true
private theorem odd_true_13 : oddRow k true 1 3 := by
  check_odd k true

private theorem odd_table (one : Bool) (i : Fin 2) (j : Fin 4) :
    oddRow k one i j := by
  cases one <;> fin_cases i <;> fin_cases j
  · exact odd_false_00 k hk
  · exact odd_false_01 k hk
  · exact odd_false_02 k hk
  · exact odd_false_03 k hk
  · exact odd_false_10 k hk
  · exact odd_false_11 k hk
  · exact odd_false_12 k hk
  · exact odd_false_13 k hk
  · exact odd_true_00 k hk
  · exact odd_true_01 k hk
  · exact odd_true_02 k hk
  · exact odd_true_03 k hk
  · exact odd_true_10 k hk
  · exact odd_true_11 k hk
  · exact odd_true_12 k hk
  · exact odd_true_13 k hk

private abbrev evenRow (k : ℤ) (one : Bool) (i j : ℕ) :=
  row k one ((pOffsetsEven one (p k one) (q k)).getD i 0)
    ((qOffsetsEven one (p k one) (q k)).getD j 0)
    (affEven (p k one) (q k) i) (affEven (p k one) (q k) (j + 4))
    ((evenRows k one).getD (2 * i + j) 0)

private theorem even_false_00 : evenRow k false 0 0 := by
  check_even k false
private theorem even_false_01 : evenRow k false 0 1 := by
  check_even k false
private theorem even_false_10 : evenRow k false 1 0 := by
  check_even k false
private theorem even_false_11 : evenRow k false 1 1 := by
  check_even k false
private theorem even_false_20 : evenRow k false 2 0 := by
  check_even k false
private theorem even_false_21 : evenRow k false 2 1 := by
  check_even k false
private theorem even_false_30 : evenRow k false 3 0 := by
  check_even k false
private theorem even_false_31 : evenRow k false 3 1 := by
  check_even k false
private theorem even_true_00 : evenRow k true 0 0 := by
  check_even k true
private theorem even_true_01 : evenRow k true 0 1 := by
  check_even k true
private theorem even_true_10 : evenRow k true 1 0 := by
  check_even k true
private theorem even_true_11 : evenRow k true 1 1 := by
  check_even k true
private theorem even_true_20 : evenRow k true 2 0 := by
  check_even k true
private theorem even_true_21 : evenRow k true 2 1 := by
  check_even k true
private theorem even_true_30 : evenRow k true 3 0 := by
  check_even k true
private theorem even_true_31 : evenRow k true 3 1 := by
  check_even k true

private theorem even_table (one : Bool) (i : Fin 4) (j : Fin 2) :
    evenRow k one i j := by
  cases one <;> fin_cases i <;> fin_cases j
  · exact even_false_00 k hk
  · exact even_false_01 k hk
  · exact even_false_10 k hk
  · exact even_false_11 k hk
  · exact even_false_20 k hk
  · exact even_false_21 k hk
  · exact even_false_30 k hk
  · exact even_false_31 k hk
  · exact even_true_00 k hk
  · exact even_true_01 k hk
  · exact even_true_10 k hk
  · exact even_true_11 k hk
  · exact even_true_20 k hk
  · exact even_true_21 k hk
  · exact even_true_30 k hk
  · exact even_true_31 k hk
end

private def parentValues (k : ℤ) (one : Bool) (u v : Word) (P Q : Site → ℤ) : Prop :=
  oddTile u = nstairN (e k one) ∧ evenTile v = nladderN (d k) ∧
  (∀ x ∈ oddTile u, P x = paperNearStairValue (e k one) (x+(0,1))) ∧
  (∀ x ∈ evenTile v, Q x = paperNearLadderValue (d k) (x+(0,1)))

private theorem placed_pair {k : ℤ} {one : Bool} {u v : Word} {P Q : Site → ℤ}
    (h : parentValues k one u v P Q) (a b s t : Site) (c₁ c₂ K : ℤ) (hr : row k one a b s t K) :
    ∃ C : ℤ, ∀ z, z - a ∈ oddTile u → z - b ∈ evenTile v →
      P (z - a) + dot2 s z + c₁ - (Q (z - b) + dot2 t z + c₂) = C := by
  obtain ⟨hu, hv, hP, hQ⟩ := h
  refine ⟨(4*K+2*(diag a-diag b)-(diag a)^2+(diag b)^2)/4+c₁-c₂, fun z hz hy => ?_⟩
  rw [hP _ hz, hQ _ hy]
  have := raw_row k one a b s t z K hr (hu ▸ hz) (hv ▸ hy)
  omega

private theorem both (w u v : Word) (P Q : Site → ℤ) (c : ℕ → ℤ) (k : ℤ) (hk : 1 ≤ k) (one : Bool)
    (hflag : (phase w == 1) = one) (hP : (parentsAt w).odd = p k one) (hQ : (parentsAt w).even = q k)
    (hval : parentValues k one u v P Q) :
    MixedCompatOdd w u v (placedOdd w P Q c) ∧ MixedCompatEven w u v (placedEven w P Q c) := by
  constructor
  · intro i j hi hj hj'
    have hr := odd_table k hk one ⟨i, hi⟩ ⟨j - 2, by omega⟩
    simp only [oddRow, Nat.sub_add_cancel hj] at hr
    have hrow : row k one ((oddP w).getD i 0) ((oddQ w).getD (j - 2) 0)
        (affOdd (parentsAt w).odd (parentsAt w).even i) (affOdd (parentsAt w).odd (parentsAt w).even j) ((oddRows k one).getD (4 * i + (j - 2)) 0) := by
      simpa only [oddP, oddQ, hflag, hP, hQ] using hr
    obtain ⟨K, hK⟩ := placed_pair hval _ _ _ _ (c i) (c j) _ hrow
    refine ⟨K, fun z hx hy => ?_⟩
    have hp := mOdd_sub w u v i hx
    have hq := mOdd_sub w u v j hy
    simp only [dOdd, pieceSet, oddP_length, if_pos hi, if_neg (Nat.not_lt_of_ge hj)] at hp hq
    simp only [placedOdd, if_pos hi, if_neg (Nat.not_lt_of_ge hj)]
    exact hK z (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)
  · intro i j hi hj hj'
    have hr := even_table k hk one ⟨i, hi⟩ ⟨j - 4, by omega⟩
    simp only [evenRow, Nat.sub_add_cancel hj] at hr
    have hrow : row k one ((evenP w).getD i 0) ((evenQ w).getD (j - 4) 0)
        (affEven (parentsAt w).odd (parentsAt w).even i) (affEven (parentsAt w).odd (parentsAt w).even j) ((evenRows k one).getD (2 * i + (j - 4)) 0) := by
      simpa only [evenP, evenQ, hflag, hP, hQ] using hr
    obtain ⟨K, hK⟩ := placed_pair hval _ _ _ _ (c i) (c j) _ hrow
    refine ⟨K, fun z hx hy => ?_⟩
    have hp := mEven_sub w u v i hx
    have hq := mEven_sub w u v j hy
    simp only [dEven, pieceSet, evenP_length, if_pos hi, if_neg (Nat.not_lt_of_ge hj)] at hp hq
    simp only [placedEven, if_pos hi, if_neg (Nat.not_lt_of_ge hj)]
    exact hK z (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)

private theorem odd_values (k : ℕ) (P Q : PartialOdometer) (h : PaperBaseCond (List.replicate k .two) P Q) :
    ∀ z ∈ oddTile (List.replicate k .two), P.val z = paperNearStairValue (2*(k : ℤ)+3) (z+(0,1)) := by
  rw [SiteBase.oddTile_rep_two]
  by_cases hk : k=0
  · subst k
    obtain ⟨hd,hv,-⟩ := h.1 rfl
    simpa [hd] using hv
  · obtain ⟨hd,hv,-⟩ := h.2.2 k (by omega) rfl
    rwa [hd] at hv

/-- The two standard children after a positive run of twos followed by one. -/
theorem two_run_one (k : ℕ) (hk : 1 ≤ k) (P Q : PartialOdometer)
    (h : PaperBaseCond (List.replicate k .two) P Q) (c : ℕ → ℤ) :
    let u := List.replicate k Digit.two
    let w := u ++ [.one]
    MixedCompatOdd w u u (placedOdd w P.val Q.val c) ∧ MixedCompatEven w u u (placedEven w P.val Q.val c) := by
  dsimp only
  apply both _ _ _ _ _ _ (k : ℤ) (by omega) true
  · simp [phase,List.count_replicate]
  · rw [parentsAt_append_singleton]
    exact cur_odd_two k
  · rw [parentsAt_append_singleton]
    exact cur_even_two k
  · obtain ⟨-, -, hd,hv⟩ := h.2.2 k hk rfl
    have he : e (k : ℤ) true = 2*(k : ℤ)+3 := by
      change 2*(k : ℤ)+2+1 = 2*(k : ℤ)+3
      ring
    rw [parentValues,he]
    refine ⟨SiteBase.oddTile_rep_two k, SiteBase.evenTile_rep_two k hk, odd_values k P Q h, ?_⟩
    simpa only [SiteBase.evenTile_rep_two k hk, ← hd] using hv

/-- The two standard children after a positive run of twos followed by three. -/
theorem two_run_three (k : ℕ) (P Q P' Q' : PartialOdometer) (h : PaperBaseCond (List.replicate (k+1) .two) P Q)
    (h' : PaperBaseCond (List.replicate k .two) P' Q') (c : ℕ → ℤ) :
    let u := List.replicate k Digit.two
    let v := List.replicate (k+1) Digit.two
    let w := v ++ [.three]
    MixedCompatOdd w u v (placedOdd w P'.val Q.val c) ∧ MixedCompatEven w u v (placedEven w P'.val Q.val c) := by
  dsimp only
  apply both _ _ _ _ _ _ ((k+1 : ℕ) : ℤ) (by omega) false
  · simp [phase,List.count_replicate]
  · rw [parentsAt_append_singleton]
    change (parentsAt (List.replicate (k+1) .two)).odd = _
    rw [parents_two]
    rfl
  · rw [parentsAt_append_singleton]
    exact cur_even_two (k+1)
  · obtain ⟨-, -, hd, hv⟩ := h.2.2 (k+1) (by omega) rfl
    have he : e ((k+1 : ℕ) : ℤ) false = 2*(k : ℤ)+3 := by
      change 2*((k+1 : ℕ) : ℤ)+2-1 = 2*(k : ℤ)+3
      push_cast
      ring
    rw [parentValues,he]
    refine ⟨SiteBase.oddTile_rep_two k, SiteBase.evenTile_rep_two (k+1) (by omega), odd_values k P' Q' h', ?_⟩
    simpa only [SiteBase.evenTile_rep_two (k+1) (by omega), ← hd] using hv

end FLatticePaper.Tiles.MixedCompatNear
