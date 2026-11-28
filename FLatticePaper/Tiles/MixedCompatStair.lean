import FLatticePaper.Tiles.ClosedPathAssembly
import FLatticePaper.Tiles.BaseTileProps
import FLatticePaper.Tiles.SiteBase

/-! Mixed interfaces whose two parents are a ladder and a staircase. Both heights have
the same quadratic part in the second coordinate. After removing it, each of the
sixteen comparisons is an inequality calculation in the two coordinates and the
denominator, with no length bound. -/

namespace FLatticePaper.Tiles.MixedCompatStair

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.ChildGlue FLatticePaper.Tiles.ClosedPathAssembly
open FLatticePaper.Tiles.MixedPieces FLatticePaper.Tiles.ClosedPathCycle
open FLatticePaper.Tiles.ClosedPathSum FLatticePaper.Tiles.BaseTileProps

private def ladderTerm (d x y : ℤ) : ℤ :=
  y + min (x - 1) 0 + min 0 (d + 1 - x) + max (x + y - d - 2) 0 +
    if (x = 0 ∧ y = 0) ∨ (x = d + 2 ∧ y = d + 2) ∨ (x + y = d + 2 ∧ 1 < y ∧ y < d + 1) then 1 else 0

private def stairTerm (e x y : ℤ) : ℤ :=
  y + min (x - 1) 0 + if (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = e + 1) then 1 else 0

private def tri (y : ℤ) := y * (y + 1) / 2

private theorem tri_sub (y r : ℤ) : tri (y - r) = tri y - r * y + tri (r - 1) := by
  unfold tri
  nlinarith only [two_mul_T2 (y - r), two_mul_T2 y, two_mul_T2 (r - 1)]

private def row (d e : ℤ) (a b s t : Site) (c : ℤ) : Prop :=
  ∀ x y : ℤ, (x - a.1, y - a.2) ∈ ladderF d → (x - b.1, y - b.2) ∈ stairF e →
    ladderTerm d (x - a.1) (y - a.2) - stairTerm e (x - b.1) (y - b.2) +
      (s.1 - t.1) * x + (s.2 - t.2 + a.2 - b.2) * y = c

private theorem raw_row (d e : ℤ) (a b s t z : Site) (c : ℤ) (hr : row d e a b s t c)
    (hp : z - a ∈ ladderF d) (hq : z - b ∈ stairF e) :
    paperLadderValue d (z - a) + dot2 s z - (paperStairValue e (z - b) + dot2 t z) =
      c - tri (a.2 - 1) + tri (b.2 - 1) := by
  have hL (x y : ℤ) : paperLadderValue d (x, y) = -tri y + ladderTerm d x y := by
    rw [plV]
    simp only [tri, ladderTerm, Prod.mk.injEq]
    abel
  have hS (x y : ℤ) : paperStairValue e (x, y) = -tri y + stairTerm e x y := by
    simp only [paperStairValue, tri, stairTerm, Prod.mk.injEq]
    abel
  rw [show z - a = (z.1 - a.1, z.2 - a.2) from rfl, show z - b = (z.1 - b.1, z.2 - b.2) from rfl,
    hL, hS, tri_sub z.2 a.2, tri_sub z.2 b.2]
  unfold dot2
  linear_combination hr z.1 z.2 hp hq

private def oddRows (d : ℤ) (one : Bool) : List ℤ :=
  if one then [-1, 0, -1, -d - 2, 2*d + 3, 2*d + 1, 0, d + 2]
  else [0, 1, -2*d - 1, -3*d - 4, 1, 1, -2*d - 1, 0]

private def evenRows (d : ℤ) (one : Bool) : List ℤ :=
  if one then [-1, 0, 0, -3, d, d - 3, 0, 2*d + 2]
  else [0, 0, 0, -3*d - 6, 1, 0, 0, -4*d - 3]

private abbrev p (d : ℤ) : Fraction := ⟨1, d⟩
private abbrev q (d : ℤ) (one : Bool) : Fraction := ⟨1, if one then d + 1 else d - 1⟩

-- Removing the quadratic term leaves only linear constraints in each entry.
local macro "check_odd" ds:ident h:ident flag:term : tactic =>
  `(tactic| (
    have he : 3 ≤ (q $ds $flag).den := by dsimp; omega
    intro x y hx hy
    rw [mem_ladderF_ab $ds $h] at hx
    rw [mem_stairF_ab _ he] at hy
    simp [pOffsetsOdd, qOffsetsOdd, affOdd, texV1Even, texV1Odd, texV2, oddRows, ladderTerm, stairTerm, min_def, max_def] at hx hy ⊢
    ring_nf
    split_ifs <;> omega))

local macro "check_even" ds:ident h:ident flag:term : tactic =>
  `(tactic| (
    have he : 3 ≤ (q $ds $flag).den := by dsimp; omega
    intro x y hx hy
    rw [mem_ladderF_ab $ds $h] at hx
    rw [mem_stairF_ab _ he] at hy
    simp [pOffsetsEven, qOffsetsEven, affEven, texV1Even, texV1Odd, texV2, evenRows, ladderTerm, stairTerm, min_def, max_def] at hx hy ⊢
    ring_nf
    split_ifs <;> omega))

section
variable (d : ℤ) (hd : 4 ≤ d)
include hd
set_option maxHeartbeats 400000

private abbrev oddRow (d : ℤ) (one : Bool) (i j : ℕ) :=
  row d (q d one).den ((pOffsetsOdd one (p d) (q d one)).getD i 0)
    ((qOffsetsOdd one (p d) (q d one)).getD j 0)
    (affOdd (p d) (q d one) i) (affOdd (p d) (q d one) (j + 2))
    ((oddRows d one).getD (4 * i + j) 0)

private theorem odd_false_00 : oddRow d false 0 0 := by
  check_odd d hd false
private theorem odd_false_01 : oddRow d false 0 1 := by
  check_odd d hd false
private theorem odd_false_02 : oddRow d false 0 2 := by
  check_odd d hd false
private theorem odd_false_03 : oddRow d false 0 3 := by
  check_odd d hd false
private theorem odd_false_10 : oddRow d false 1 0 := by
  check_odd d hd false
private theorem odd_false_11 : oddRow d false 1 1 := by
  check_odd d hd false
private theorem odd_false_12 : oddRow d false 1 2 := by
  check_odd d hd false
private theorem odd_false_13 : oddRow d false 1 3 := by
  check_odd d hd false
private theorem odd_true_00 : oddRow d true 0 0 := by
  check_odd d hd true
private theorem odd_true_01 : oddRow d true 0 1 := by
  check_odd d hd true
private theorem odd_true_02 : oddRow d true 0 2 := by
  check_odd d hd true
private theorem odd_true_03 : oddRow d true 0 3 := by
  check_odd d hd true
private theorem odd_true_10 : oddRow d true 1 0 := by
  check_odd d hd true
private theorem odd_true_11 : oddRow d true 1 1 := by
  check_odd d hd true
private theorem odd_true_12 : oddRow d true 1 2 := by
  check_odd d hd true
private theorem odd_true_13 : oddRow d true 1 3 := by
  check_odd d hd true

private theorem odd_table (one : Bool) (i : Fin 2) (j : Fin 4) :
    oddRow d one i j := by
  cases one <;> fin_cases i <;> fin_cases j
  · exact odd_false_00 d hd
  · exact odd_false_01 d hd
  · exact odd_false_02 d hd
  · exact odd_false_03 d hd
  · exact odd_false_10 d hd
  · exact odd_false_11 d hd
  · exact odd_false_12 d hd
  · exact odd_false_13 d hd
  · exact odd_true_00 d hd
  · exact odd_true_01 d hd
  · exact odd_true_02 d hd
  · exact odd_true_03 d hd
  · exact odd_true_10 d hd
  · exact odd_true_11 d hd
  · exact odd_true_12 d hd
  · exact odd_true_13 d hd

private abbrev evenRow (d : ℤ) (one : Bool) (i j : ℕ) :=
  row d (q d one).den ((pOffsetsEven one (p d) (q d one)).getD i 0)
    ((qOffsetsEven one (p d) (q d one)).getD j 0)
    (affEven (p d) (q d one) i) (affEven (p d) (q d one) (j + 4))
    ((evenRows d one).getD (2 * i + j) 0)

private theorem even_false_00 : evenRow d false 0 0 := by
  check_even d hd false
private theorem even_false_01 : evenRow d false 0 1 := by
  check_even d hd false
private theorem even_false_10 : evenRow d false 1 0 := by
  check_even d hd false
private theorem even_false_11 : evenRow d false 1 1 := by
  check_even d hd false
private theorem even_false_20 : evenRow d false 2 0 := by
  check_even d hd false
private theorem even_false_21 : evenRow d false 2 1 := by
  check_even d hd false
private theorem even_false_30 : evenRow d false 3 0 := by
  check_even d hd false
private theorem even_false_31 : evenRow d false 3 1 := by
  check_even d hd false
private theorem even_true_00 : evenRow d true 0 0 := by
  check_even d hd true
private theorem even_true_01 : evenRow d true 0 1 := by
  check_even d hd true
private theorem even_true_10 : evenRow d true 1 0 := by
  check_even d hd true
private theorem even_true_11 : evenRow d true 1 1 := by
  check_even d hd true
private theorem even_true_20 : evenRow d true 2 0 := by
  check_even d hd true
private theorem even_true_21 : evenRow d true 2 1 := by
  check_even d hd true
private theorem even_true_30 : evenRow d true 3 0 := by
  check_even d hd true
private theorem even_true_31 : evenRow d true 3 1 := by
  check_even d hd true

private theorem even_table (one : Bool) (i : Fin 4) (j : Fin 2) :
    evenRow d one i j := by
  cases one <;> fin_cases i <;> fin_cases j
  · exact even_false_00 d hd
  · exact even_false_01 d hd
  · exact even_false_10 d hd
  · exact even_false_11 d hd
  · exact even_false_20 d hd
  · exact even_false_21 d hd
  · exact even_false_30 d hd
  · exact even_false_31 d hd
  · exact even_true_00 d hd
  · exact even_true_01 d hd
  · exact even_true_10 d hd
  · exact even_true_11 d hd
  · exact even_true_20 d hd
  · exact even_true_21 d hd
  · exact even_true_30 d hd
  · exact even_true_31 d hd
end

private def parentValues (d e : ℤ) (u v : Word) (P Q : Site → ℤ) : Prop :=
  oddTile u = ladderF d ∧ evenTile v = stairF e ∧
  (∀ x ∈ oddTile u, P x = paperLadderValue d x) ∧ (∀ x ∈ evenTile v, Q x = paperStairValue e x)

private theorem placed_pair {d e : ℤ} {u v : Word} {P Q : Site → ℤ} (h : parentValues d e u v P Q)
    (a b s t : Site) (c₁ c₂ k : ℤ) (hr : row d e a b s t k) :
    ∃ C : ℤ, ∀ z, z - a ∈ oddTile u → z - b ∈ evenTile v →
      P (z - a) + dot2 s z + c₁ - (Q (z - b) + dot2 t z + c₂) = C := by
  obtain ⟨hu, hv, hP, hQ⟩ := h
  refine ⟨k - tri (a.2 - 1) + tri (b.2 - 1) + c₁ - c₂, fun z hz hy => ?_⟩
  rw [hP _ hz, hQ _ hy]
  have := raw_row d e a b s t z k hr (hu ▸ hz) (hv ▸ hy)
  omega

private theorem both (w u v : Word) (P Q : Site → ℤ) (c : ℕ → ℤ) (d : ℤ) (hd : 4 ≤ d) (one : Bool)
    (hflag : (phase w == 1) = one) (hP : (parentsAt w).odd = p d) (hQ : (parentsAt w).even = q d one)
    (hval : parentValues d (q d one).den u v P Q) :
    MixedCompatOdd w u v (placedOdd w P Q c) ∧ MixedCompatEven w u v (placedEven w P Q c) := by
  constructor
  · intro i j hi hj hj'
    have hr := odd_table d hd one ⟨i, hi⟩ ⟨j - 2, by omega⟩
    simp only [oddRow, Nat.sub_add_cancel hj] at hr
    have hrow : row d (q d one).den ((oddP w).getD i 0) ((oddQ w).getD (j - 2) 0)
        (affOdd (parentsAt w).odd (parentsAt w).even i) (affOdd (parentsAt w).odd (parentsAt w).even j) ((oddRows d one).getD (4 * i + (j - 2)) 0) := by
      simpa only [oddP, oddQ, hflag, hP, hQ] using hr
    obtain ⟨K, hK⟩ := placed_pair hval _ _ _ _ (c i) (c j) _ hrow
    refine ⟨K, fun z hx hy => ?_⟩
    have hp := mOdd_sub w u v i hx
    have hq := mOdd_sub w u v j hy
    simp only [dOdd, pieceSet, oddP_length, if_pos hi, if_neg (Nat.not_lt_of_ge hj)] at hp hq
    simp only [placedOdd, if_pos hi, if_neg (Nat.not_lt_of_ge hj)]
    exact hK z (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)
  · intro i j hi hj hj'
    have hr := even_table d hd one ⟨i, hi⟩ ⟨j - 4, by omega⟩
    simp only [evenRow, Nat.sub_add_cancel hj] at hr
    have hrow : row d (q d one).den ((evenP w).getD i 0) ((evenQ w).getD (j - 4) 0)
        (affEven (parentsAt w).odd (parentsAt w).even i) (affEven (parentsAt w).odd (parentsAt w).even j) ((evenRows d one).getD (2 * i + (j - 4)) 0) := by
      simpa only [evenP, evenQ, hflag, hP, hQ] using hr
    obtain ⟨K, hK⟩ := placed_pair hval _ _ _ _ (c i) (c j) _ hrow
    refine ⟨K, fun z hx hy => ?_⟩
    have hp := mEven_sub w u v i hx
    have hq := mEven_sub w u v j hy
    simp only [dEven, pieceSet, evenP_length, if_pos hi, if_neg (Nat.not_lt_of_ge hj)] at hp hq
    simp only [placedEven, if_pos hi, if_neg (Nat.not_lt_of_ge hj)]
    exact hK z (sub_mem_of_shift _ _ _ hp) (sub_mem_of_shift _ _ _ hq)

private abbrev threes (k : ℕ) : Word := List.replicate k Digit.three

private theorem even_values (k : ℕ) (P Q : PartialOdometer) (h : PaperBaseCond (threes k) P Q) :
    ∀ z ∈ evenTile (threes k), Q.val z = paperStairValue (2 * (k : ℤ) + 3) z := by
  rw [SiteBase.evenTile_rep_three]
  by_cases hk : k = 0
  · subst k
    obtain ⟨-, -, hd, hv⟩ := h.1 rfl
    simpa [hd] using hv
  · obtain ⟨-, -, hd, hv⟩ := h.2.1 k (by omega) rfl
    rwa [hd] at hv

/-- Both mixed inputs after a positive run of threes followed by one. The two register
odometers are exactly the pair from the base word. -/
theorem three_run_one (k : ℕ) (hk : 1 ≤ k) (P Q : PartialOdometer)
    (h : PaperBaseCond (List.replicate k .three) P Q) (c : ℕ → ℤ) :
    let u := List.replicate k Digit.three
    let w := u ++ [.one]
    MixedCompatOdd w u u (placedOdd w P.val Q.val c) ∧ MixedCompatEven w u u (placedEven w P.val Q.val c) := by
  dsimp only
  apply both _ _ _ _ _ _ (2 * (k : ℤ) + 2) (by omega) true
  · simp [phase, List.count_replicate]
  · rw [parentsAt_append_singleton]
    exact cur_odd_three k
  · rw [parentsAt_append_singleton]
    change (parentsAt (threes k)).current .even = _
    rw [cur_even_three]
    congr 1
  · obtain ⟨hdom, hv, -⟩ := h.2.1 k hk rfl
    have he : (q (2 * (k : ℤ) + 2) true).den = 2 * (k : ℤ) + 3 := by dsimp; omega
    rw [parentValues, he]
    refine ⟨SiteBase.oddTile_rep_three k hk, SiteBase.evenTile_rep_three k, ?_, even_values k P Q h⟩
    simpa only [SiteBase.oddTile_rep_three k hk, ← hdom] using hv

/-- Both mixed inputs after a positive run of threes followed by two. The even parent
is the staircase from the preceding register, including the empty word at run length one. -/
theorem three_run_two (k : ℕ) (P Q P' Q' : PartialOdometer)
    (h : PaperBaseCond (List.replicate (k + 1) .three) P Q) (h' : PaperBaseCond (List.replicate k .three) P' Q') (c : ℕ → ℤ) :
    let u := List.replicate (k + 1) Digit.three
    let v := List.replicate k Digit.three
    let w := u ++ [.two]
    MixedCompatOdd w u v (placedOdd w P.val Q'.val c) ∧ MixedCompatEven w u v (placedEven w P.val Q'.val c) := by
  dsimp only
  apply both _ _ _ _ _ _ (2 * ((k + 1 : ℕ) : ℤ) + 2) (by omega) false
  · simp [phase, List.count_replicate]
  · rw [parentsAt_append_singleton]
    exact cur_odd_three (k + 1)
  · rw [parentsAt_append_singleton]
    change (parentsAt (threes (k + 1))).even = _
    rw [parents_three]
    unfold q
    simp only [Bool.false_eq_true, if_false]
    congr 1
    omega
  · obtain ⟨hdom, hv, -⟩ := h.2.1 (k + 1) (by omega) rfl
    have he : (q (2 * ((k + 1 : ℕ) : ℤ) + 2) false).den = 2 * (k : ℤ) + 3 := by dsimp; omega
    rw [parentValues, he]
    refine ⟨SiteBase.oddTile_rep_three (k + 1) (by omega), SiteBase.evenTile_rep_three k, ?_, even_values k P' Q' h'⟩
    simpa only [SiteBase.oddTile_rep_three (k + 1) (by omega), ← hdom] using hv

end FLatticePaper.Tiles.MixedCompatStair
