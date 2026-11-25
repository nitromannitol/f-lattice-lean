import FLatticePaper.Tiles.SubWalkOddBlocks
import FLatticePaper.Tiles.SubWalkOddCrit

/-! Task Q25 (sub), the odd bottom walk: every edge of the walk is a boundary edge of the cell tile.

For a ceiling word `x` of slope `(2N, D + N)` with `1 ≤ N` and `N < D`, the walk `gH x` from `0` has all its edges in the boundary
of a cell tile `T` whose membership is the four-test bound `pB` (`walk_bd`). Each block `j` is classified by the regime:
`2N ≤ D − N` (regime A, `block_A`, the next letter decides) and `D − N < 2N` (regime B, `block_B`, `hasN_B` and the previous letter
decide). The final east step is `last_A`, `last_B`. -/

namespace FLatticePaper.Tiles.SubWalkOddBound

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SubCeilOdd FLatticePaper.Tiles.SubBlockOdd FLatticePaper.Tiles.SubWalkOdd
  FLatticePaper.Tiles.SubWalkOddBlocks FLatticePaper.Tiles.CeilWords

theorem mkSub_gI (a b : ℤ) : ((a, b) : GInt) - gI = (a, b - 1) :=
  Prod.ext (by simp [gI]) (by simp [gI])

theorem mkAdd_gOne (a b : ℤ) : ((a, b) : GInt) + gOne = (a + 1, b) :=
  Prod.ext (by simp [gOne]) (by simp [gOne])

theorem mkAdd_gI (a b : ℤ) : ((a, b) : GInt) + gI = (a, b + 1) :=
  Prod.ext (by simp [gI]) (by simp [gI])

theorem mkSub_gOne (a b : ℤ) : ((a, b) : GInt) - gOne = (a - 1, b) :=
  Prod.ext (by simp [gOne]) (by simp [gOne])

/-- The block `[1,1]` at the corner `(a, b)`, in coordinates. -/
theorem EE_bd (T : CellTile) (a b : ℤ) (h1 : (a, b) ∈ T) (h2 : (a, b - 1) ∉ T) (h3 : (a + 1, b) ∈ T)
    (h4 : (a + 1, b - 1) ∉ T) : ∀ e ∈ edgesFrom (a, b) [Unit4.one, Unit4.one], e ∈ T.boundaryEdges := by
  refine SubWalkOddCrit.bd_EE T (a, b) h1 ?_ ?_ ?_
  · rw [mkSub_gI]; exact h2
  · rw [mkAdd_gOne]; exact h3
  · rw [mkAdd_gOne, mkSub_gI]; exact h4

/-- The block `[1,i]` at the corner `(a, b)`, in coordinates. -/
theorem EN_bd (T : CellTile) (a b : ℤ) (h1 : (a, b) ∈ T) (h2 : (a, b - 1) ∉ T) (h3 : (a + 1, b) ∉ T) :
    ∀ e ∈ edgesFrom (a, b) [Unit4.one, Unit4.i], e ∈ T.boundaryEdges := by
  refine SubWalkOddCrit.bd_EN T (a, b) h1 ?_ ?_
  · rw [mkSub_gI]; exact h2
  · rw [mkAdd_gOne]; exact h3

/-- The block `[i,1]` at the corner `(a, b)`, in coordinates. -/
theorem NE_bd (T : CellTile) (a b : ℤ) (h1 : (a - 1, b) ∈ T) (h2 : (a, b) ∉ T) (h3 : (a, b + 1) ∈ T) :
    ∀ e ∈ edgesFrom (a, b) [Unit4.i, Unit4.one], e ∈ T.boundaryEdges := by
  refine SubWalkOddCrit.bd_NE T (a, b) ?_ h2 ?_
  · rw [mkSub_gOne]; exact h1
  · rw [mkAdd_gI]; exact h3

/-- The final east step from the corner `(a, b)`. -/
theorem Last_bd (T : CellTile) (a b : ℤ) (h1 : (a, b) ∈ T) (h2 : (a, b - 1) ∉ T) :
    ∀ e ∈ edgesFrom (a, b) [Unit4.one], e ∈ T.boundaryEdges := by
  intro e he
  simp only [edgesFrom, vecOne_eq, List.mem_cons, List.mem_nil_iff, or_false] at he
  rw [he]
  exact (SubCriteria.east_mem_boundaryEdges_iff T (a, b)).2 ⟨h1, by rw [mkSub_gI]; exact h2⟩

theorem Yc_zero (ε : ℕ → ℤ) : Yc ε 0 = 0 := by simp [Yc]

theorem ec_eq (N D : ℤ) (x : BinaryWord) (hLD : (x.length : ℤ) = D + N) (k : ℕ) :
    ec N x.length (epsOf x) k = 2 * N * (k : ℤ) - (D + N) * Yc (epsOf x) k := by
  unfold ec
  rw [hLD]

/-- Regime A: the block `j` has no `q` pair before it, so it is never of type NE. -/
theorem noNE_A (N C : ℤ) (hA : 2 * N ≤ C) (x : BinaryWord)
    (hP : CeilPack N C x.length (epsOf x) (gVal N x)) (j : ℕ) (hj : j + 2 ≤ x.length) :
    ¬ (epsOf x j = 1 ∧ tY (epsOf x) j = 1) := by
  rintro ⟨h1, h2⟩
  cases j with
  | zero => simp [tY] at h2
  | succ m =>
    rw [tY_succ] at h2
    exact noqq_A N C hA x.length (epsOf x) (gVal N x) hP m (by omega) ⟨h2, h1⟩

/-- Regime A, a block `j` with `ε (j+1) = 1` is of type EN, the criteria of `EN_block` at its cursor. -/
theorem block_A (N D : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hA : 2 * N ≤ D - N) (x : BinaryWord)
    (hx : CeilWord x (2 * N) (D + N)) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pB N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) (j : ℕ)
    (hj : j + 2 ≤ x.length) :
    ∀ e ∈ edgesFrom (2 * (j : ℤ) - Yc (epsOf x) j, Yc (epsOf x) j) (blockWord x j), e ∈ T.boundaryEdges := by
  have hLD : (x.length : ℤ) = D + N := hx.1
  have hx' : CeilWord x (2 * N) (2 * N + (D - N)) := by
    rw [show 2 * N + (D - N) = D + N by ring]
    exact hx
  have hP := ceilPack_of N (D - N) hN hC x hx'
  have hK : max (D - 2 * N) N = D - 2 * N := max_eq_left (by omega)
  rw [hK] at hT
  have hYb := Yc_bounds (epsOf x) j
  have hjD : (j : ℤ) + 2 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hwin := winA N (D - N) hN hC hA x.length (epsOf x) (gVal N x) hP j (by omega)
  rw [ec_eq N D x hLD j] at hwin
  have hND : N + 1 ≤ D := by omega
  have hK1D : D - 2 * N ≤ D := by omega
  have hLam : min (D - N) (3 * N - D) ≤ D - N := min_le_left _ _
  intro e he
  by_cases hE : epsOf x (j + 1) = 1
  · have hε0 : epsOf x j = 0 := by
      rcases hP.hε j with h | h
      · exact h
      · exact absurd (And.intro h hE) (noqq_A N (D - N) hA x.length (epsOf x) (gVal N x) hP j hj)
    have hthr := thrA_EN N (D - N) hN hC hA x.length (epsOf x) (gVal N x) hP j hj hE
    rw [ec_eq N D x hLD j] at hthr
    rw [blockWord_eq x j (by omega), if_pos (And.intro hε0 hE)] at he
    have key := EN_block N D (D - 2 * N) (min (D - N) (3 * N - D)) (j : ℤ) (Yc (epsOf x) j) hN hND hK1D
      le_rfl hk0 hYb.2 hjD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hthr.1])
      (by linarith [hthr.2])
    exact EN_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      (fun hm => key.2.2 ((hT _ _).1 hm)) e he
  · have hε1 : epsOf x (j + 1) = 0 := by
      rcases hP.hε (j + 1) with h | h
      · exact h
      · exact absurd h hE
    have hnNE := noNE_A N (D - N) hA x hP j hj
    have hthr := thrA_EE N (D - N) hN hC hA x.length (epsOf x) (gVal N x) hP j hj hε1
    rw [ec_eq N D x hLD j] at hthr
    rw [blockWord_eq x j (by omega), if_neg (show ¬(epsOf x j = 0 ∧ epsOf x (j + 1) = 1) from fun h => hE h.2),
      if_neg hnNE] at he
    have key := EE_block N D (D - 2 * N) (min (D - N) (3 * N - D)) (j : ℤ) (Yc (epsOf x) j) hN hND hK1D
      le_rfl hLam hk0 hYb.2 hjD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hthr])
    exact EE_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      ((hT _ _).2 key.2.2.1) (fun hm => key.2.2.2 ((hT _ _).1 hm)) e he

/-- Regime B, the block `j` (the cursor of block `j` is at `j`). -/
theorem block_B (N D : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hB : D - N < 2 * N) (x : BinaryWord)
    (hx : CeilWord x (2 * N) (D + N)) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pB N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) (j : ℕ)
    (hj : j + 2 ≤ x.length) :
    ∀ e ∈ edgesFrom (2 * (j : ℤ) - Yc (epsOf x) j, Yc (epsOf x) j) (blockWord x j), e ∈ T.boundaryEdges := by
  have hLD : (x.length : ℤ) = D + N := hx.1
  have hx' : CeilWord x (2 * N) (2 * N + (D - N)) := by
    rw [show 2 * N + (D - N) = D + N by ring]
    exact hx
  have hP := ceilPack_of N (D - N) hN hC x hx'
  have hK : max (D - 2 * N) N = N := max_eq_right (by omega)
  rw [hK] at hT
  have e0 := eps_zero N (D - N) hN hC x.length (epsOf x) (gVal N x) hP
  have hND : N + 1 ≤ D := by omega
  have hK1D : N ≤ D := by omega
  have hK1lo : D - 2 * N ≤ N := by omega
  have hLam : min (D - N) (3 * N - D) ≤ D - N := min_le_left _ _
  intro e he
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hY : Yc (epsOf x) 0 = 0 := Yc_zero _
    rw [hY, blockWord_eq x 0 (by omega),
      if_neg (show ¬(epsOf x 0 = 0 ∧ epsOf x (0 + 1) = 1) from fun h => by
        have := h.1
        rw [e0] at this
        norm_num at this),
      if_neg (show ¬(epsOf x 0 = 1 ∧ tY (epsOf x) 0 = 1) from fun h => by
        have := h.2
        rw [tY_zero] at this
        norm_num at this)] at he
    have key := EE_block N D N (min (D - N) (3 * N - D)) ((0 : ℕ) : ℤ) 0 hN hND hK1D hK1lo hLam
      (by norm_num) (by norm_num) (by omega) (by norm_num; omega) (by norm_num; omega)
      (by norm_num)
    exact EE_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      ((hT _ _).2 key.2.2.1) (fun hm => key.2.2.2 ((hT _ _).1 hm)) e he
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hH := hasN_B N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP m (by omega)
    have hYk := Yc_bounds (epsOf x) (m + 1)
    have hk0 : (0 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by positivity
    have hkL : ((m + 1 : ℕ) : ℤ) + 2 ≤ D + N := by omega
    rcases hP.hε m with hm0 | hm1
    · -- type EE: the north indicator of block `m + 1` is `ε m = 0`
      have n1 : ¬(epsOf x (m + 1) = 0 ∧ epsOf x (m + 1 + 1) = 1) := fun h => by
        have h' := hasNI_EN x (m + 1) h
        omega
      have n2 : ¬(epsOf x (m + 1) = 1 ∧ tY (epsOf x) (m + 1) = 1) := fun h => by
        have h' := hasNI_NE x (m + 1) h
        omega
      rw [blockWord_eq x (m + 1) (by omega), if_neg n1, if_neg n2] at he
      have hwin := winB N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega)
      rw [ec_eq N D x hLD (m + 1)] at hwin
      have hthr := thrB_EE N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega) hm0
      rw [ec_eq N D x hLD (m + 1)] at hthr
      have key := EE_block N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
        hK1D hK1lo hLam hk0 hYk.2 hkL (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hthr])
      exact EE_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
        ((hT _ _).2 key.2.2.1) (fun hm => key.2.2.2 ((hT _ _).1 hm)) e he
    · rcases hP.hε (m + 1) with hn0 | hn1
      · -- type EN: `ε (m + 1) = 0` and then `ε (m + 2) = 1`
        have h2 : epsOf x (m + 1 + 1) = 1 := by
          rcases hP.hε (m + 1 + 1) with h | h
          · exfalso
            have hz : hasNI (epsOf x) (m + 1) = 0 :=
              hasNI_EE x (m + 1) (fun hc => by omega) (fun hc => by omega)
            omega
          · exact h
        have hc1 : epsOf x (m + 1) = 0 ∧ epsOf x (m + 1 + 1) = 1 := And.intro hn0 h2
        rw [blockWord_eq x (m + 1) (by omega), if_pos hc1] at he
        have hwin := winB N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega)
        rw [ec_eq N D x hLD (m + 1)] at hwin
        have hthr := thrB_EN N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega) hm1 hn0
        rw [ec_eq N D x hLD (m + 1)] at hthr
        have key := EN_block N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
          hK1D hK1lo hk0 hYk.2 hkL (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hthr.1])
          (by linarith [hthr.2])
        exact EN_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
          (fun hm => key.2.2 ((hT _ _).1 hm)) e he
      · -- type NE: `ε (m + 1) = 1` and `tY (m + 1) = ε m = 1`
        have htY : tY (epsOf x) (m + 1) = 1 := by
          rw [tY_succ]
          exact hm1
        have hc1 : ¬(epsOf x (m + 1) = 0 ∧ epsOf x (m + 1 + 1) = 1) := fun hc => by omega
        have hc2 : epsOf x (m + 1) = 1 ∧ tY (epsOf x) (m + 1) = 1 := And.intro hn1 htY
        rw [blockWord_eq x (m + 1) (by omega), if_neg hc1, if_pos hc2] at he
        have hwin := winB N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega)
        rw [ec_eq N D x hLD (m + 1)] at hwin
        have hthr := thrB_NE N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 m (by omega) hm1 hn1
        rw [ec_eq N D x hLD (m + 1)] at hthr
        have hk1 : (1 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by omega
        have key := NE_block N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
          hK1D le_rfl hLam hk0 hk1 (Yc_bounds (epsOf x) (m + 1)).1 hYk.2 hkL
          (by linarith [hwin.2]) (by linarith [hthr])
        exact NE_bd T _ _ ((hT _ _).2 key.2.1) (fun hm => key.1 ((hT _ _).1 hm))
          ((hT _ _).2 key.2.2) e he

/-- Regime A, the last east step (block `L − 1`). -/
theorem last_A (N D : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hA : 2 * N ≤ D - N) (x : BinaryWord)
    (hx : CeilWord x (2 * N) (D + N)) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pB N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom (2 * ((x.length - 1 : ℕ) : ℤ) - Yc (epsOf x) (x.length - 1), Yc (epsOf x) (x.length - 1))
      [Unit4.one], e ∈ T.boundaryEdges := by
  have hLD : (x.length : ℤ) = D + N := hx.1
  have hx' : CeilWord x (2 * N) (2 * N + (D - N)) := by
    rw [show 2 * N + (D - N) = D + N by ring]
    exact hx
  have hP := ceilPack_of N (D - N) hN hC x hx'
  have hK : max (D - 2 * N) N = D - 2 * N := max_eq_left (by omega)
  rw [hK] at hT
  have hL1 : 1 ≤ x.length := by omega
  have hwin := winA N (D - N) hN hC hA x.length (epsOf x) (gVal N x) hP (x.length - 1) (by omega)
  have hlast := lastA N (D - N) hN hC hA x.length (epsOf x) (gVal N x) hP hL1
  rw [ec_eq N D x hLD (x.length - 1)] at hwin hlast
  have hYb := Yc_bounds (epsOf x) (x.length - 1)
  have hkL : ((x.length - 1 : ℕ) : ℤ) + 1 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ ((x.length - 1 : ℕ) : ℤ) := by positivity
  have hK1D : D - 2 * N ≤ D := by omega
  have key := Last_block N D (D - 2 * N) (min (D - N) (3 * N - D)) ((x.length - 1 : ℕ) : ℤ)
    (Yc (epsOf x) (x.length - 1)) hN (by omega) hK1D le_rfl hk0 hYb.2 hkL
    (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hlast])
  exact Last_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2 ((hT _ _).1 hm))

/-- Regime B, the last east step (block `L − 1`). -/
theorem last_B (N D : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hB : D - N < 2 * N) (x : BinaryWord)
    (hx : CeilWord x (2 * N) (D + N)) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pB N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom (2 * ((x.length - 1 : ℕ) : ℤ) - Yc (epsOf x) (x.length - 1), Yc (epsOf x) (x.length - 1))
      [Unit4.one], e ∈ T.boundaryEdges := by
  have hLD : (x.length : ℤ) = D + N := hx.1
  have hx' : CeilWord x (2 * N) (2 * N + (D - N)) := by
    rw [show 2 * N + (D - N) = D + N by ring]
    exact hx
  have hP := ceilPack_of N (D - N) hN hC x hx'
  have hK : max (D - 2 * N) N = N := max_eq_right (by omega)
  rw [hK] at hT
  have e0 := eps_zero N (D - N) hN hC x.length (epsOf x) (gVal N x) hP
  have hL2 : 2 ≤ x.length := by omega
  have e2 : x.length - 2 + 1 = x.length - 1 := by omega
  have hwin := winB N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 (x.length - 2) (by omega)
  have hlast := lastB N (D - N) hN hC hB x.length (epsOf x) (gVal N x) hP e0 hL2
  rw [e2, ec_eq N D x hLD (x.length - 1)] at hwin hlast
  have hYb := Yc_bounds (epsOf x) (x.length - 1)
  have hkL : ((x.length - 1 : ℕ) : ℤ) + 1 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ ((x.length - 1 : ℕ) : ℤ) := by positivity
  have hK1lo : D - 2 * N ≤ N := by omega
  have key := Last_block N D N (min (D - N) (3 * N - D)) ((x.length - 1 : ℕ) : ℤ)
    (Yc (epsOf x) (x.length - 1)) hN (by omega) (by omega) hK1lo hk0 hYb.2 hkL
    (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hlast])
  exact Last_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2 ((hT _ _).1 hm))

/-- The whole odd bottom walk `gH x` from `0` lies in the boundary of the cell tile `T`. -/
theorem walk_bd (N D : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (x : BinaryWord)
    (hx : CeilWord x (2 * N) (D + N)) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pB N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom 0 (gH x), e ∈ T.boundaryEdges := by
  have hLD : (x.length : ℤ) = D + N := hx.1
  have hL1 : 1 ≤ x.length := by omega
  have hbl : ∀ k : ℕ, k + 1 ≤ x.length →
      ∀ e ∈ edgesFrom 0 ((List.range k).flatMap (blockWord x)), e ∈ T.boundaryEdges := by
    intro k
    induction k with
    | zero =>
      intro _ e he
      simp [edgesFrom] at he
    | succ k ih =>
      intro hk e he
      rw [flatMap_range_succ, edgesFrom_append, zero_add] at he
      rcases List.mem_append.1 he with h | h
      · exact ih (by omega) e h
      · rw [sum_prefix x k (by omega)] at h
        by_cases hA : 2 * N ≤ D - N
        · exact block_A N D hN hC hA x hx T hT k (by omega) e h
        · exact block_B N D hN hC (by omega) x hx T hT k (by omega) e h
  intro e he
  rw [gH_walk x hL1, edgesFrom_append, zero_add] at he
  rcases List.mem_append.1 he with h | h
  · exact hbl (x.length - 1) (by omega) e h
  · rw [sum_prefix x (x.length - 1) (by omega)] at h
    by_cases hA : 2 * N ≤ D - N
    · exact last_A N D hN hC hA x hx T hT e h
    · exact last_B N D hN hC (by omega) x hx T hT e h

end FLatticePaper.Tiles.SubWalkOddBound
