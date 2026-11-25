import FLatticePaper.Tiles.SubBlockEven
import FLatticePaper.Tiles.SubCeilEven
import FLatticePaper.Tiles.SubWalkOddBound

/-! Task Q25 (sub), the even bottom walk: every edge of `gH x` from `0` lies in the boundary of the even cell tile.

For the even child word `x` (`CeilWord x N M`, `D + N = 2M`), the walk `gH x` has the blocks of `SubWalkOddBlocks`. The block `j` lies
in regime A (`2N ≤ M`, `K1 = D − 2N`, the next letter decides the type) or regime B (`M < 2N`, `K1 = N`, `hasN_B_E` and the previous
letter decide). The cursor bound is `2j + 4 ≤ D + N`, since the blocks are indexed by `j < M`. -/

namespace FLatticePaper.Tiles.SubWalkEven

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SubCeilOdd FLatticePaper.Tiles.SubCeilEven FLatticePaper.Tiles.SubBlockEven
  FLatticePaper.Tiles.SubWalkOdd FLatticePaper.Tiles.SubWalkOddBlocks FLatticePaper.Tiles.SubWalkOddBound
  FLatticePaper.Tiles.CeilWords

/-- The ceiling values of the even child: `g j = M q_j − N j`. -/
def gValE (N M : ℤ) (x : BinaryWord) (j : ℕ) : ℤ := M * CeilWords.qPrefix x j - N * j

theorem ceilPackE_of (N M : ℤ) (x : BinaryWord) (hx : CeilWords.CeilWord x N M) (hM1 : 1 ≤ M) :
    CeilPackE N M x.length (epsOf x) (gValE N M x) := by
  have hL : (x.length : ℤ) = M := hx.1
  refine ⟨?_, ?_, ?_, ?_, ?_, hL⟩
  · intro j
    unfold epsOf
    split_ifs <;> simp
  · unfold gValE CeilWords.qPrefix
    simp
  · intro j hj
    unfold gValE
    rw [qPrefix_succ x j hj]
    push_cast
    ring
  · intro j hj
    have hj' : (j : ℤ) ≤ x.length := by exact_mod_cast hj
    have hb := hx.2 j (by linarith)
    unfold gValE
    constructor <;> linarith [hb.1, hb.2]
  · unfold gValE
    rw [CeilWords.ceil_total x N M hx hM1, hx.1]
    ring

/-- Regime A: no two consecutive `q` letters, so no block of type NE. -/
theorem noNE_E (N M : ℤ) (hA : 2 * N ≤ M) (x : BinaryWord)
    (hP : CeilPackE N M x.length (epsOf x) (gValE N M x)) (j : ℕ) (hj : j + 2 ≤ x.length) :
    ¬ (epsOf x j = 1 ∧ tY (epsOf x) j = 1) := by
  rintro ⟨h1, h2⟩
  cases j with
  | zero => simp [tY] at h2
  | succ m =>
    rw [tY_succ] at h2
    exact noqq_E N M hA x.length (epsOf x) (gValE N M x) hP m (by omega) ⟨h2, h1⟩

/-- Regime A, block `j`: its criteria at the cursor are the boundary of the even tile `T`. -/
theorem block_AE (N D M : ℤ) (hN : 1 ≤ N) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (x : BinaryWord)
    (hx : CeilWords.CeilWord x N M) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pBE N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) (j : ℕ)
    (hj : j + 2 ≤ x.length) :
    ∀ e ∈ edgesFrom (2 * (j : ℤ) - Yc (epsOf x) j, Yc (epsOf x) j) (blockWord x j), e ∈ T.boundaryEdges := by
  have hL : (x.length : ℤ) = M := hx.1
  have hM1 : 1 ≤ M := by omega
  have hP := ceilPackE_of N M x hx hM1
  have hNM : N < M := by omega
  have e0 := eps_zero_E N M hN hNM x.length (by omega) (epsOf x) (gValE N M x) hP
  have hK : max (D - 2 * N) N = D - 2 * N := max_eq_left (by omega)
  rw [hK] at hT
  have hYb := Yc_bounds (epsOf x) j
  have hkD : 2 * (j : ℤ) + 4 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hND : N + 1 ≤ D := by omega
  have hK1D : D - 2 * N ≤ D := by omega
  have hLam : min (D - N) (3 * N - D) ≤ D - N := min_le_left _ _
  have hwin := winA_E N M D hM hA x.length (epsOf x) (gValE N M x) hP e0 j (by omega)
  unfold ecE at hwin
  intro e he
  by_cases hE : epsOf x (j + 1) = 1
  · have hε0 : epsOf x j = 0 := by
      rcases hP.hε j with h | h
      · exact h
      · exact absurd (And.intro h hE) (noqq_E N M hA x.length (epsOf x) (gValE N M x) hP j hj)
    have thr := thrA_EN_E N M D hM hA x.length (epsOf x) (gValE N M x) hP e0 j hj hE
    unfold ecE at thr
    rw [blockWord_eq x j (by omega), if_pos (And.intro hε0 hE)] at he
    have key := EN_blockE N D (D - 2 * N) (min (D - N) (3 * N - D)) (j : ℤ) (Yc (epsOf x) j) hN hND hK1D
      le_rfl hk0 hYb.2 hkD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [thr.1])
      (by linarith [thr.2])
    exact EN_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      (fun hm => key.2.2 ((hT _ _).1 hm)) e he
  · have hε1 : epsOf x (j + 1) = 0 := by
      rcases hP.hε (j + 1) with h | h
      · exact h
      · exact absurd h hE
    have hnNE := noNE_E N M hA x hP j hj
    have thr := thrA_EE_E N M D hM hA x.length (epsOf x) (gValE N M x) hP e0 j hj hε1
    unfold ecE at thr
    rw [blockWord_eq x j (by omega), if_neg (show ¬(epsOf x j = 0 ∧ epsOf x (j + 1) = 1) from fun h => hE h.2),
      if_neg hnNE] at he
    have key := EE_blockE N D (D - 2 * N) (min (D - N) (3 * N - D)) (j : ℤ) (Yc (epsOf x) j) hN hND hK1D
      le_rfl hLam hk0 hYb.2 hkD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [thr])
    exact EE_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      ((hT _ _).2 key.2.2.1) (fun hm => key.2.2.2 ((hT _ _).1 hm)) e he

/-- Regime B, block `j`: its criteria at the cursor are the boundary of the even tile `T`. -/
theorem block_BE (N D M : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hM : D + N = 2 * M) (hB : M < 2 * N)
    (x : BinaryWord) (hx : CeilWords.CeilWord x N M) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pBE N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) (j : ℕ)
    (hj : j + 2 ≤ x.length) :
    ∀ e ∈ edgesFrom (2 * (j : ℤ) - Yc (epsOf x) j, Yc (epsOf x) j) (blockWord x j), e ∈ T.boundaryEdges := by
  have hL : (x.length : ℤ) = M := hx.1
  have hM1 : 1 ≤ M := by omega
  have hP := ceilPackE_of N M x hx hM1
  have hNM : N < M := by omega
  have e0 := eps_zero_E N M hN hNM x.length (by omega) (epsOf x) (gValE N M x) hP
  have hK : max (D - 2 * N) N = N := max_eq_right (by omega)
  rw [hK] at hT
  have hND : N + 1 ≤ D := by omega
  have hK1D : N ≤ D := by omega
  have hK1lo : D - 2 * N ≤ N := by omega
  have hLam : min (D - N) (3 * N - D) ≤ D - N := min_le_left _ _
  intro e he
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hY : Yc (epsOf x) 0 = 0 := SubWalkOddBound.Yc_zero _
    rw [hY, blockWord_eq x 0 (by omega),
      if_neg (show ¬(epsOf x 0 = 0 ∧ epsOf x (0 + 1) = 1) from fun h => by
        have := h.1
        rw [e0] at this
        norm_num at this),
      if_neg (show ¬(epsOf x 0 = 1 ∧ tY (epsOf x) 0 = 1) from fun h => by
        have := h.2
        rw [tY_zero] at this
        norm_num at this)] at he
    have key := EE_blockE N D N (min (D - N) (3 * N - D)) ((0 : ℕ) : ℤ) 0 hN hND hK1D hK1lo hLam
      (by norm_num) (by norm_num) (by omega) (by norm_num; omega) (by norm_num; omega) (by norm_num)
    exact EE_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
      ((hT _ _).2 key.2.2.1) (fun hm => key.2.2.2 ((hT _ _).1 hm)) e he
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hH := hasN_B_E N M hB x.length (epsOf x) (gValE N M x) hP m (by omega)
    have hYk := Yc_bounds (epsOf x) (m + 1)
    have hk0 : (0 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by positivity
    have hkD : 2 * ((m + 1 : ℕ) : ℤ) + 4 ≤ D + N := by omega
    rcases hP.hε m with hm0 | hm1
    · -- type EE: the north indicator of block `m + 1` is `ε m = 0`
      have n1 : ¬(epsOf x (m + 1) = 0 ∧ epsOf x (m + 1 + 1) = 1) := fun h => by
        have h' := hasNI_EN x (m + 1) h
        omega
      have n2 : ¬(epsOf x (m + 1) = 1 ∧ tY (epsOf x) (m + 1) = 1) := fun h => by
        have h' := hasNI_NE x (m + 1) h
        omega
      rw [blockWord_eq x (m + 1) (by omega), if_neg n1, if_neg n2] at he
      have hwin := winB_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega)
      unfold ecE at hwin
      have thr := thrB_EE_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega) hm0
      unfold ecE at thr
      have key := EE_blockE N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
        hK1D hK1lo hLam hk0 hYk.2 hkD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [thr])
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
        have hwin := winB_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega)
        unfold ecE at hwin
        have thr := thrB_EN_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega) hm1 hn0
        unfold ecE at thr
        have key := EN_blockE N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
          hK1D hK1lo hk0 hYk.2 hkD (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [thr.1])
          (by linarith [thr.2])
        exact EN_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2.1 ((hT _ _).1 hm))
          (fun hm => key.2.2 ((hT _ _).1 hm)) e he
      · -- type NE: `ε (m + 1) = 1` and `tY (m + 1) = ε m = 1`
        have htY : tY (epsOf x) (m + 1) = 1 := by
          rw [tY_succ]
          exact hm1
        have hc1 : ¬(epsOf x (m + 1) = 0 ∧ epsOf x (m + 1 + 1) = 1) := fun hc => by omega
        have hc2 : epsOf x (m + 1) = 1 ∧ tY (epsOf x) (m + 1) = 1 := And.intro hn1 htY
        rw [blockWord_eq x (m + 1) (by omega), if_neg hc1, if_pos hc2] at he
        have hwin := winB_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega)
        unfold ecE at hwin
        have thr := thrB_NE_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 m (by omega) hm1 hn1
        unfold ecE at thr
        have hk1 : (1 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) := by omega
        have key := NE_blockE N D N (min (D - N) (3 * N - D)) ((m + 1 : ℕ) : ℤ) (Yc (epsOf x) (m + 1)) hN hND
          hK1D le_rfl hLam hk0 hk1 hYk.1 hYk.2 hkD (by linarith [hwin.2]) (by linarith [thr])
        exact NE_bd T _ _ ((hT _ _).2 key.2.1) (fun hm => key.1 ((hT _ _).1 hm))
          ((hT _ _).2 key.2.2) e he

/-- Regime A, the last east step (block `L − 1`) of the even walk. -/
theorem last_AE (N D M : ℤ) (hN : 1 ≤ N) (hM : D + N = 2 * M) (hA : 2 * N ≤ M) (x : BinaryWord)
    (hx : CeilWords.CeilWord x N M) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pBE N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom (2 * ((x.length - 1 : ℕ) : ℤ) - Yc (epsOf x) (x.length - 1), Yc (epsOf x) (x.length - 1))
      [Unit4.one], e ∈ T.boundaryEdges := by
  have hL : (x.length : ℤ) = M := hx.1
  have hM1 : 1 ≤ M := by omega
  have hP := ceilPackE_of N M x hx hM1
  have hNM : N < M := by omega
  have hL1 : 1 ≤ x.length := by omega
  have e0 := eps_zero_E N M hN hNM x.length hL1 (epsOf x) (gValE N M x) hP
  have hK : max (D - 2 * N) N = D - 2 * N := max_eq_left (by omega)
  rw [hK] at hT
  have hwin := winA_E N M D hM hA x.length (epsOf x) (gValE N M x) hP e0 (x.length - 1) (by omega)
  have hlast := lastA_E N M D hM hA x.length (epsOf x) (gValE N M x) hP e0 hL1
  unfold ecE at hwin hlast
  have hYb := Yc_bounds (epsOf x) (x.length - 1)
  have hkL : 2 * ((x.length - 1 : ℕ) : ℤ) + 2 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ ((x.length - 1 : ℕ) : ℤ) := by positivity
  have hK1D : D - 2 * N ≤ D := by omega
  have key := Last_blockE N D (D - 2 * N) (min (D - N) (3 * N - D)) ((x.length - 1 : ℕ) : ℤ)
    (Yc (epsOf x) (x.length - 1)) hN (by omega) hK1D le_rfl hk0 hYb.2 hkL
    (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hlast])
  exact Last_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2 ((hT _ _).1 hm))

/-- Regime B, the last east step (block `L − 1`) of the even walk. -/
theorem last_BE (N D M : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hM : D + N = 2 * M) (hB : M < 2 * N)
    (x : BinaryWord) (hx : CeilWords.CeilWord x N M) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pBE N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom (2 * ((x.length - 1 : ℕ) : ℤ) - Yc (epsOf x) (x.length - 1), Yc (epsOf x) (x.length - 1))
      [Unit4.one], e ∈ T.boundaryEdges := by
  have hL : (x.length : ℤ) = M := hx.1
  have hM1 : 1 ≤ M := by omega
  have hP := ceilPackE_of N M x hx hM1
  have hNM : N < M := by omega
  have hL2 : 2 ≤ x.length := by omega
  have e0 := eps_zero_E N M hN hNM x.length (by omega) (epsOf x) (gValE N M x) hP
  have hK : max (D - 2 * N) N = N := max_eq_right (by omega)
  rw [hK] at hT
  obtain ⟨k, hk⟩ : ∃ k, x.length = k + 2 := ⟨x.length - 2, by omega⟩
  have e2 : x.length - 1 = k + 1 := by omega
  rw [e2]
  have hwin := winB_E N M D hM hB x.length (epsOf x) (gValE N M x) hP e0 k (by omega)
  have hlast := lastB_E N M D hM hN hNM hB x.length (epsOf x) (gValE N M x) hP e0 hL2
  rw [e2] at hlast
  unfold ecE at hwin hlast
  have hYb := Yc_bounds (epsOf x) (k + 1)
  have hkL : 2 * ((k + 1 : ℕ) : ℤ) + 2 ≤ D + N := by omega
  have hk0 : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by positivity
  have hK1D : N ≤ D := by omega
  have hK1lo : D - 2 * N ≤ N := by omega
  have key := Last_blockE N D N (min (D - N) (3 * N - D)) ((k + 1 : ℕ) : ℤ) (Yc (epsOf x) (k + 1)) hN
    (by omega) hK1D hK1lo hk0 hYb.2 hkL (by linarith [hwin.1]) (by linarith [hwin.2]) (by linarith [hlast])
  exact Last_bd T _ _ ((hT _ _).2 key.1) (fun hm => key.2 ((hT _ _).1 hm))

/-- The whole even bottom walk `gH x` from `0` lies in the boundary of the even cell tile `T`. -/
theorem walk_bdE (N D M : ℤ) (hN : 1 ≤ N) (hC : 1 ≤ D - N) (hM : D + N = 2 * M) (x : BinaryWord)
    (hx : CeilWords.CeilWord x N M) (T : CellTile)
    (hT : ∀ a b : ℤ, (a, b) ∈ T ↔ pBE N D (max (D - 2 * N) N) (min (D - N) (3 * N - D)) a b) :
    ∀ e ∈ edgesFrom 0 (gH x), e ∈ T.boundaryEdges := by
  have hL : (x.length : ℤ) = M := hx.1
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
        by_cases hA : 2 * N ≤ M
        · exact block_AE N D M hN hM hA x hx T hT k (by omega) e h
        · exact block_BE N D M hN hC hM (by omega) x hx T hT k (by omega) e h
  intro e he
  rw [gH_walk x hL1, edgesFrom_append, zero_add] at he
  rcases List.mem_append.1 he with h | h
  · exact hbl (x.length - 1) (by omega) e h
  · rw [sum_prefix x (x.length - 1) (by omega)] at h
    by_cases hA : 2 * N ≤ M
    · exact last_AE N D M hN hM hA x hx T hT e h
    · exact last_BE N D M hN hC hM (by omega) x hx T hT e h

end FLatticePaper.Tiles.SubWalkEven
