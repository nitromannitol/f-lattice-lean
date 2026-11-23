import FLatticePaper.Tiles.RegionBoundary

/-! Task 55 (R1/R2 converse): the rows of a cell tile from its boundary walk.

If `T` is a cell tile whose directed boundary is the four-arc walk of `boundaryWordOf w1 w2`, then the rows of `T` are the arc
intervals `[c - FF(H-k-1), FF k)` of the arcs `w1`, `w2`. The argument: for a cell `(x,k)`, the boundary records the change of
membership along row `k`: `[(x,k)∈T] - [(x-1,k)∈T] = [S-edge at x] - [N-edge at x]`, so two cell sets with the same
boundary have the same membership on each row (induction from a point left of every cell). The walk's north and south edges
at row `k` are the two ends of the arc interval (`north_iff`, `south_iff`), which gives the rows. -/

namespace FLatticePaper.Tiles.RowsOfBoundary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.RegionRuns
open FLatticePaper.Tiles.FourWalks FLatticePaper.Tiles.RegionBoundary FLatticePaper.Tiles.RegionArith

/-- The arc interval of row `k` for the arc column function `F`, height `H` and endpoint `c`. -/
def RowG (H c : ℤ) (F : ℤ → ℤ) (x k : ℤ) : Prop :=
  0 ≤ k ∧ k < H ∧ c - F (H - k - 1) ≤ x ∧ x < F k

/-- A propositional step: membership of the next cell is determined by the boundary relations and the previous cell. -/
theorem prop_step {Q Pm G G' : Prop} (h1 : Q ∧ ¬Pm ↔ G ∧ ¬G') (h2 : Pm ∧ ¬Q ↔ G' ∧ ¬G) (hP : Pm ↔ G') :
    Q ↔ G := by
  tauto

theorem rows_of_boundary (T : CellTile) (w1 w2 : F2Word)
    (h1 : ∀ x ∈ w1, x = .one ∨ x = .i)
    (h2 : ∀ x ∈ w2, x = .i ∨ x = .negOne)
    (hn : (F2Word.sum w1).2 < (F2Word.sum w2).2) (ha : 0 < (F2Word.sum w1).1 + (F2Word.sum w2).1)
    (hRa : ¬ (w1.getLast? = some .one ∧ w2.head? = some .negOne))
    (hRb : ¬ (w1.head? = some .i ∧ w2.getLast? = some .i))
    (hlast : w2.getLast? = some .i)
    (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2)) (x k : ℤ) :
    ((x, k) : GInt) ∈ T ↔
      RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k := by
  -- the arc setup, as in region_boundary_word
  have hw1n : ∀ x ∈ w1, x ≠ .negI := fun x hx => by
    rcases h1 x hx with rfl | rfl <;> simp
  have hw2n : ∀ x ∈ w2, x ≠ .negI := fun x hx => by
    rcases h2 x hx with rfl | rfl <;> simp
  have hU : ∀ x ∈ w1 ++ w2, x = .one ∨ x = .i ∨ x = .negOne := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases h1 x hx with rfl | rfl <;> simp
    · rcases h2 x hx with rfl | rfl <;> simp
  have hUn : ∀ x ∈ w1 ++ w2, x ≠ .negI := fun x hx => by
    rcases hU x hx with rfl | rfl | rfl <;> simp
  have hNC : NoEWChain (w1 ++ w2) := by
    apply noEW_append w1 w2
    · exact noEW_of_no_negOne w1 (fun y hy => by rcases h1 y hy with rfl | rfl <;> simp)
    · exact noEW_of_no_one w2 (fun y hy => by rcases h2 y hy with rfl | rfl <;> simp)
    · intro y hy x hx
      rw [Option.mem_def] at hy hx
      show ¬((y = .one ∧ x = .negOne) ∨ (y = .negOne ∧ x = .one))
      rintro (⟨rfl, rfl⟩ | ⟨rfl, hx1⟩)
      · exact hRa ⟨hy, hx⟩
      · rcases h1 _ (List.mem_of_mem_getLast? hy) with h | h <;> cases h
  have RD := runData_of (w1 ++ w2) hU hNC
  have hsnd : (F2Word.sum (w1 ++ w2)).2 = cntI (w1 ++ w2) := sum_snd (w1 ++ w2) hUn
  have hz : F2Word.sum (w1 ++ w2) = ((F2Word.sum (w1 ++ w2)).1, cntI (w1 ++ w2)) := Prod.ext rfl hsnd
  have hcnt : cntI (w1 ++ w2) = (F2Word.sum w1).2 + (F2Word.sum w2).2 := by
    rw [cntI_append, sum_snd w1 hw1n, sum_snd w2 hw2n]
  have hsum1 : (F2Word.sum (w1 ++ w2)).1 = (F2Word.sum w1).1 + (F2Word.sum w2).1 := by
    rw [arc_sum_append, Prod.fst_add]
  have hn0 : 0 ≤ (F2Word.sum w1).2 := by
    rw [sum_snd w1 hw1n]
    exact cntI_nonneg w1
  have hH1 : 1 ≤ cntI (w1 ++ w2) := by omega
  have hFneg : FF (w1 ++ w2) (-1) = 0 := by simp [FF]
  have hFH : FF (w1 ++ w2) (cntI (w1 ++ w2)) = (F2Word.sum (w1 ++ w2)).1 := by
    unfold FF
    rw [if_neg (by have := cntI_nonneg (w1 ++ w2); omega), if_neg (lt_irrefl _)]
  have hl : (w1 ++ w2).getLast? = some .i := by simp [List.getLast?_append, hlast]
  have hF1 : FF (w1 ++ w2) (cntI (w1 ++ w2) - 1) = (F2Word.sum (w1 ++ w2)).1 :=
    le_antisymm (RD.inv1 (by rw [hl]; simp)) (RD.inv2 (by rw [hl]; simp))
  have hF0 : ∀ j : ℤ, 0 ≤ j → j < cntI (w1 ++ w2) → 0 ≤ FF (w1 ++ w2) j := by
    intro j hj0 hj
    rw [FF_eq_colN _ _ hj0 hj]
    by_cases hjn : j < cntI w1
    · rw [arc_F_lo w1 w2 h1 j hj0 hjn]
      exact arc_colN_nonneg w1 h1 j
    · rw [arc_F_hi w1 w2 h1 j (not_lt.mp hjn)]
      have := arc_colN_ge_sum w2 h2 (j - cntI w1)
      omega
  have hkey : ∀ q r : ℤ, 0 ≤ q → q < cntI (w1 ++ w2) → 0 ≤ r → r < cntI (w1 ++ w2) →
      cntI (w1 ++ w2) - 2 ≤ q + r → q + r ≤ cntI (w1 ++ w2) →
      (F2Word.sum (w1 ++ w2)).1 + 1 ≤ FF (w1 ++ w2) q + FF (w1 ++ w2) r := by
    intro q r hq0 hq hr0 hr hs1 hs2
    rw [FF_eq_colN _ _ hq0 hq, FF_eq_colN _ _ hr0 hr, hsum1]
    exact arc_key w1 w2 h1 h2 hn ha hRb hq0 (by omega) hr0 (by omega) (by omega) (by omega)
  have D : ArcData (FF (w1 ++ w2)) (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 :=
    ⟨hH1, hFneg, hFH, hF1, hF0, hkey⟩
  have hcol : ∀ y j : ℤ, (0 ≤ j ∧ j < cntI (w1 ++ w2) ∧ y = colN (w1 ++ w2) (0, 0) j) ↔
      (0 ≤ j ∧ j < cntI (w1 ++ w2) ∧ y = FF (w1 ++ w2) j) := by
    intro y j
    constructor
    · rintro ⟨hj0, hj1, hj2⟩
      exact ⟨hj0, hj1, by rw [FF_eq_colN _ _ hj0 hj1]; exact hj2⟩
    · rintro ⟨hj0, hj1, hj2⟩
      exact ⟨hj0, hj1, by rw [← FF_eq_colN _ _ hj0 hj1]; exact hj2⟩
  -- the boundary of T is the walk
  have hB : ∀ e, e ∈ T.boundaryEdges ↔ e ∈ edgesFrom (0, 0) (boundaryWordOf w1 w2) := fun e => by
    rw [← hT.2.2.2, List.mem_toFinset, zip_walk_eq]
  -- the north and south boundary edges of row k are the ends of the arc interval
  have hNe : ∀ x k : ℤ, ((x, k), (x, k + 1)) ∈ T.boundaryEdges ↔
      (RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) (x - 1) k ∧
        ¬ RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k) := by
    intro x k
    rw [hB, walk_N w1 w2 RD hU _ hz x k, hcol x k]
    exact ArcData.north_iff D x k
  have hSe : ∀ x k : ℤ, ((x, k + 1), (x, k)) ∈ T.boundaryEdges ↔
      (RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k ∧
        ¬ RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) (x - 1) k) := by
    intro x k
    rw [hB, walk_S w1 w2 RD hU _ hz x k, hcol _ _]
    exact ArcData.south_iff D x k
  -- the row k of T, by induction from a point left of every cell
  have hrow : ∀ k x : ℤ, ((x, k) : GInt) ∈ T ↔
      RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k := by
    intro k
    obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ p ∈ T, N < p.1 := by
      refine ⟨-(T.sum fun p => |p.1|) - 1, fun p hp => ?_⟩
      have h1' : |p.1| ≤ T.sum (fun p => |p.1|) :=
        Finset.single_le_sum (f := fun p : GInt => |p.1|) (fun q _ => abs_nonneg q.1) hp
      have h2' : -|p.1| ≤ p.1 := neg_abs_le p.1
      linarith
    set B : ℤ := min N ((F2Word.sum (w1 ++ w2)).1 - FF (w1 ++ w2) (cntI (w1 ++ w2) - k - 1)) - 1 with hB_def
    have base : ((B, k) : GInt) ∈ T ↔
        RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) B k := by
      constructor
      · intro hm
        have hlt : N < B := hN _ hm
        omega
      · rintro ⟨-, -, hlo, -⟩
        omega
    have step : ∀ x : ℤ, (((x - 1, k) : GInt) ∈ T ↔
        RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) (x - 1) k) →
        (((x, k) : GInt) ∈ T ↔
          RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k) := by
      intro x hP
      apply prop_step
      · exact (bdry_S_iff T x k).symm.trans (hSe x k)
      · exact (bdry_N_iff T x k).symm.trans (hNe x k)
      · exact hP
    have all : ∀ n : ℕ, ∀ x : ℤ, x = B + n → (((x, k) : GInt) ∈ T ↔
        RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k) := by
      intro n
      induction n with
      | zero =>
        intro x hx
        have hxB : x = B := by simpa using hx
        rw [hxB]
        exact base
      | succ m ih =>
        intro x hx
        exact step x (ih (x - 1) (by push_cast at hx; omega))
    intro x
    rcases le_or_gt B x with hx | hx
    · exact all (x - B).toNat x (by omega)
    · -- x < B: both sides are false
      have hF : ¬ ((x, k) : GInt) ∈ T := by
        intro hm
        have hlt : N < x := hN _ hm
        omega
      have hG : ¬ RowG (cntI (w1 ++ w2)) (F2Word.sum (w1 ++ w2)).1 (FF (w1 ++ w2)) x k := by
        rintro ⟨-, -, hlo, -⟩
        omega
      exact ⟨fun h => absurd h hF, fun h => absurd h hG⟩
  exact hrow k x

end FLatticePaper.Tiles.RowsOfBoundary
