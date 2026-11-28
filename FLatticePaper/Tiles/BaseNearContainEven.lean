import FLatticePaper.Tiles.BaseNearContain
import FLatticePaper.Tiles.BaseHpNearEven
import FLatticePaper.Tiles.BaseTwoEven

/-! # Containment of the near-one placements of the base word `2^k`, even

The four placed strings of `RespectsAnchored` for the even word `2^k` (`k ≥ 1`; horizontal `q^{2k+1} p`, vertical
`p q^k p q^{k+1}`) lie in the near-one ladder tile `paperNearLadderTile (2k+2)` after the shift `(0,1)` of `nladderN`.
The horizontal strings use the index forms; the vertical strings use the index forms `vRevStringAt_eq_map` and
`vStringAt_eq_map`, proved as `hRevStringAt_eq_map` is. -/

namespace FLatticePaper.Tiles.BaseNearContainEven

open FLatticePaper.Tiles FLatticePaper.Construction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.BaseNearContain FLatticePaper.Farey FLatticePaper.Tiles.BaseHpNearEven FLatticePaper.Tiles.BaseTwoEven
  FLatticePaper.Tiles.BaseHmAnchor

/-! ### Index forms of the vertical strings -/

theorem vRevStringAt_eq_map (u : BinaryWord) (c : GInt) (P : ℕ → GInt) (hu : 0 < u.length) (hP0 : P 0 = c)
    (hstep : ∀ j, j + 1 < u.length →
      P (j + 1) = P j + vRevOffset (u.getD j Letter.p) (u.getD (j + 1) Letter.p)) :
    vRevStringAt u c = (List.range u.length).map fun j => (letterZTile (u.getD j Letter.p), P j) := by
  have hscan : ∀ j, j < u.length →
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD j 0 = P j := by
    intro j
    induction j with
    | zero => intro _; simp [hP0]
    | succ j ih =>
      intro hj
      have hL : j < ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2).length := by
        simp only [List.length_map, List.length_zip, List.length_tail]
        omega
      rw [scanl_getD_succ _ _ _ hL, ih (by omega), hstep j hj]
      congr 1
      have hz : ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2).getD j 0 =
          vRevOffset (u.getD j Letter.p) (u.getD (j + 1) Letter.p) := by
        have ha : j < u.length := by omega
        rw [List.getD_eq_getElem _ _ hL, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hj]
        simp [List.getElem_map, List.getElem_zip]
      exact hz
  unfold vRevStringAt
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_zip, List.length_map, List.length_scanl, List.length_range, List.length_tail]
    omega
  · intro j h1 h2
    have hj : j < u.length := by simpa using h2
    have e2 := hscan j hj
    have hlenS : j < (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).length := by
      simp only [List.length_scanl, List.length_map, List.length_zip, List.length_tail]
      omega
    rw [List.getD_eq_getElem _ _ hlenS] at e2
    have e1 : u.getD j Letter.p = u[j] := List.getD_eq_getElem _ _ hj
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    rw [e1]
    exact Prod.ext rfl e2

theorem vStringAt_eq_map (w : BinaryWord) (c : GInt) (P : ℕ → GInt) (hw : 0 < w.length) (hP0 : P 0 = c)
    (hstep : ∀ j, j + 1 < w.length → P (j + 1) = P j + vOffset (w.getD (j + 1) Letter.p)) :
    vStringAt w c = (List.range w.length).map fun j => (letterZTile (w.getD j Letter.p), P j) := by
  have hscan : ∀ j, j < w.length →
      (List.scanl (· + ·) c (w.tail.map vOffset)).getD j 0 = P j := by
    intro j
    induction j with
    | zero => intro _; simp [hP0]
    | succ j ih =>
      intro hj
      have hL : j < (w.tail.map vOffset).length := by
        simp only [List.length_map, List.length_tail]
        omega
      rw [scanl_getD_succ _ _ _ hL, ih (by omega), hstep j hj]
      congr 1
      have hz : (w.tail.map vOffset).getD j 0 = vOffset (w.getD (j + 1) Letter.p) := by
        rw [List.getD_eq_getElem _ _ hL, List.getD_eq_getElem _ _ (show j + 1 < w.length from hj)]
        simp [List.getElem_map, List.getElem_tail]
      exact hz
  unfold vStringAt
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_zip, List.length_map, List.length_scanl, List.length_range, List.length_tail]
    omega
  · intro j h1 h2
    have hj : j < w.length := by simpa using h2
    have e2 := hscan j hj
    have hlenS : j < (List.scanl (· + ·) c (w.tail.map vOffset)).length := by
      simp only [List.length_scanl, List.length_map, List.length_tail]
      omega
    rw [List.getD_eq_getElem _ _ hlenS] at e2
    have e1 : w.getD j Letter.p = w[j] := List.getD_eq_getElem _ _ hj
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    rw [e1]
    exact Prod.ext rfl e2

/-! ### Closed forms of the letters, the tile types and the positions -/

theorem lettersOf_E (k j : ℕ) :
    lettersOf (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) false j =
      if j < 2 * k + 1 then Letter.q else Letter.p := by
  show (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]).getD j Letter.p = _
  rw [getD_rep_append]
  split_ifs <;> rfl

theorem hTile_E (k j : ℕ) :
    hTileAt (lettersOf (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) false) j =
      if j = 0 then ZTile.one else if j < 2 * k + 1 then ZTile.oneD else ZTile.zero := by
  unfold hTileAt hPrev
  simp only [lettersOf_E]
  split_ifs <;> first | (exfalso; omega) | simp [hTt, letterZTile]

theorem posF_E_le (k : ℕ) : ∀ j, j ≤ 2 * k →
    posF Orientation.horizontal false (lettersOf (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) false) j =
      ((j : ℤ), (j : ℤ))
  | 0, _ => rfl
  | j + 1, h => by
      rw [posF, posF_E_le k j (by omega), stepOf_hor, lettersOf_E, if_pos (show j + 1 < 2 * k + 1 by omega)]
      simp only [hOffset]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        omega
      · simp only [Prod.snd_add]
        omega

theorem posF_E_last (k : ℕ) :
    posF Orientation.horizontal false (lettersOf (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) false)
      (2 * k + 1) = ((2 * (k : ℤ) + 2), (2 * (k : ℤ))) := by
  rw [posF, posF_E_le k (2 * k) le_rfl, stepOf_hor, lettersOf_E, if_neg (lt_irrefl _)]
  simp only [hOffset]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    omega
  · simp only [Prod.snd_add]
    omega

theorem lastPos_range_map (f : ℕ → ZTile × GInt) (n : ℕ) (hn : 0 < n) :
    lastPosOf ((List.range n).map f) = (f (n - 1)).2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [lastPosOf, List.range_succ]

/-- The forward string `q^{2k+1} p` (`k ≥ 1`): its placed sites lie in the near-one ladder tile, after the shift `(0,1)`. -/
theorem piece_hF_even (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]) (0, 0))) :
    (x.1, x.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 2) := by
  have hlen : (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]).length = 2 * k + 2 := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
  have e := zoForwardE_eq_hStringAt (List.replicate (2 * k + 1) Letter.q ++ [Letter.p])
  rw [hlen] at e
  rw [← e, zoForwardE, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [hTile_E k j] at hxj
  by_cases hjk : j ≤ 2 * k
  · rw [posF_E_le k j hjk] at hxj
    split_ifs at hxj with h0 h1 <;>
    first
      | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
      | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
      | rw [mem_oneD_c] at hxj
    all_goals
      unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Prod.ext_iff]
      omega
  · have hj2 : j = 2 * k + 1 := by omega
    subst hj2
    rw [posF_E_last, if_neg (show ¬ (2 * k + 1 = 0) by omega),
      if_neg (show ¬ (2 * k + 1 < 2 * k + 1) by omega), mem_shape_zero] at hxj
    simp only [zeroAt] at hxj
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff]
    omega

/-! ### The reversed string `p q^{2k+1}`, from `(-1, 4k+2)` -/

theorem lettersOf_R (k j : ℕ) :
    lettersOf (Letter.p :: List.replicate (2 * k + 1) Letter.q) false j =
      if j = 0 then Letter.p else if j ≤ 2 * k + 1 then Letter.q else Letter.p := by
  show (Letter.p :: List.replicate (2 * k + 1) Letter.q).getD j Letter.p = _
  rw [getD_cons_rep]

theorem hTile_R (k j : ℕ) (hj : j < 2 * k + 2) :
    hTileAt (lettersOf (Letter.p :: List.replicate (2 * k + 1) Letter.q) false) j =
      if j = 0 then ZTile.zero else if j = 1 then ZTile.one else ZTile.oneD := by
  unfold hTileAt hPrev
  simp only [lettersOf_R]
  split_ifs <;> first | (exfalso; omega) | simp [hTt, letterZTile]

/-- The positions of the reversed horizontal string `p q^{2k+1}` from `(-1, 4k+2)`. -/
def PhR (k j : ℕ) : GInt :=
  if j = 0 then ((-1 : ℤ), 4 * (k : ℤ) + 2) else ((j : ℤ), 4 * (k : ℤ) + 2 + (j : ℤ))

theorem hstep_hR (k : ℕ) :
    ∀ j, j + 1 < (Letter.p :: List.replicate (2 * k + 1) Letter.q).length →
      PhR k (j + 1) = PhR k j +
        zeroOneHorizontalReversedStep ((Letter.p :: List.replicate (2 * k + 1) Letter.q).getD j Letter.p)
          ((Letter.p :: List.replicate (2 * k + 1) Letter.q).getD (j + 1) Letter.p) := by
  intro j hj
  have hj' : j + 1 < 2 * k + 2 := by
    simp only [List.length_cons, List.length_replicate] at hj
    omega
  rw [← hRevOffset_eq_step, getD_cons_rep, getD_cons_rep]
  unfold PhR
  by_cases h0 : j = 0
  · subst h0
    refine Prod.ext ?_ ?_ <;> simp [hRevOffset]
  · have h5 : j ≤ 2 * k + 1 := by omega
    have h6 : j + 1 ≤ 2 * k + 1 := by omega
    refine Prod.ext ?_ ?_
    · simp [h0, h5, h6, hRevOffset]
    · simp [h0, h5, h6, hRevOffset]
      omega

theorem piece_hR_even (k : ℕ) (hk : 1 ≤ k) (s : GInt) (hs : s = (-1, 4 * (k : ℤ) + 2)) (x : GInt)
    (hx : x ∈ placedSites (hRevStringAt (Letter.p :: List.replicate (2 * k + 1) Letter.q) s)) :
    (x.1, x.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 2) := by
  subst hs
  have hlen : (Letter.p :: List.replicate (2 * k + 1) Letter.q).length = 2 * k + 2 := by
    simp only [List.length_cons, List.length_replicate]
  have key := hRevStringAt_eq_map (Letter.p :: List.replicate (2 * k + 1) Letter.q) (-1, 4 * (k : ℤ) + 2)
    (PhR k) (by simp [PhR]) (hstep_hR k)
  rw [key, hlen, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [hTile_R k j hj] at hxj
  unfold PhR at hxj
  split_ifs at hxj with h0 h1 <;>
  first
    | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
    | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
    | rw [mem_oneD_c] at hxj
  all_goals
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff]
    omega

/-! ### The reversed vertical string `q^{k+1} p q^k p`, from `(0,0)` -/

theorem getD_uR (k j : ℕ) :
    (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).getD j Letter.p =
      if j ≤ k then Letter.q else if j = k + 1 then Letter.p else if j ≤ 2 * k + 1 then Letter.q else Letter.p := by
  rcases Nat.lt_or_ge j (k + 1) with hA | hA
  · rw [List.getD_append _ _ _ _ (by simp only [List.length_replicate]; omega), getD_replicate']
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate]
    rcases Nat.eq_zero_or_pos (j - (k + 1)) with h0 | hpos
    · rw [h0, List.getD_cons_zero]
      split_ifs <;> first | rfl | (exfalso; omega)
    · obtain ⟨i, hi⟩ : ∃ i, j - (k + 1) = i + 1 := ⟨j - (k + 1) - 1, by omega⟩
      rw [hi, List.getD_cons_succ, getD_rep_append]
      split_ifs <;> first | rfl | (exfalso; omega)

/-- The positions of the reversed vertical string `q^{k+1} p q^k p` from `(0,0)`. -/
def PvR (k j : ℕ) : GInt :=
  if j ≤ k then (0, 2 * (j : ℤ)) else if j = k + 1 then (0, 2 * (k : ℤ) + 1)
    else if j ≤ 2 * k + 1 then (-1, 2 * (k : ℤ) + 3 + 2 * ((j : ℤ) - k - 2)) else (-1, 4 * (k : ℤ) + 2)

theorem hstep_vR (k : ℕ) :
    ∀ j, j + 1 < (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).length →
      PvR k (j + 1) = PvR k j +
        vRevOffset ((List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).getD j
            Letter.p)
          ((List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).getD (j + 1)
            Letter.p) := by
  intro j hj
  have hj' : j + 1 < 2 * k + 3 := by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hj
    omega
  rw [getD_uR, getD_uR]
  unfold PvR
  split_ifs <;> first | (exfalso; omega) | (simp [Prod.ext_iff, vRevOffset]; omega)

theorem piece_vR_even (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ placedSites (vRevStringAt
      (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])) (0, 0))) :
    (x.1, x.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 2) := by
  have hlen : (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).length =
      2 * k + 3 := by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have key := vRevStringAt_eq_map (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p]))
    (0, 0) (PvR k) (by rw [hlen]; omega) (by simp [PvR]) (hstep_vR k)
  rw [key, hlen, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [getD_uR] at hxj
  unfold PvR at hxj
  split_ifs at hxj <;> simp only [lzq, lzp] at hxj
  all_goals first
    | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
    | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
  all_goals
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff]
    omega

/-! ### The forward vertical string `p q^k p q^{k+1}`, from `(2k+2, 2k)` -/

theorem getD_vF (k j : ℕ) (hj : j < 2 * k + 3) :
    (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)).getD j Letter.p =
      if j = 0 then Letter.p else if j ≤ k then Letter.q else if j = k + 1 then Letter.p else Letter.q := by
  cases j with
  | zero => simp
  | succ j =>
    rw [List.getD_cons_succ]
    rcases Nat.lt_or_ge j k with hA | hA
    · rw [List.getD_append _ _ _ _ (by simp only [List.length_replicate]; omega), getD_replicate']
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
      simp only [List.length_replicate]
      rcases Nat.eq_zero_or_pos (j - k) with h0 | hpos
      · rw [h0, List.getD_cons_zero]
        split_ifs <;> first | rfl | (exfalso; omega)
      · obtain ⟨i, hi⟩ : ∃ i, j - k = i + 1 := ⟨j - k - 1, by omega⟩
        rw [hi, List.getD_cons_succ, getD_replicate']
        split_ifs <;> first | rfl | (exfalso; omega)

/-- The positions of the forward vertical string `p q^k p q^{k+1}` from `(2k+2, 2k)`. -/
def PvF (k j : ℕ) : GInt :=
  if j ≤ k then (2 * (k : ℤ) + 2, 2 * (k : ℤ) + 2 * (j : ℤ))
    else (2 * (k : ℤ) + 1, 4 * (k : ℤ) + 1 + 2 * ((j : ℤ) - k - 1))

theorem hstep_vF (k : ℕ) :
    ∀ j, j + 1 < (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)).length →
      PvF k (j + 1) = PvF k j +
        vOffset ((Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)).getD (j + 1)
          Letter.p) := by
  intro j hj
  have hj' : j + 1 < 2 * k + 3 := by
    simp only [List.length_cons, List.length_append, List.length_replicate] at hj
    omega
  rw [getD_vF k (j + 1) hj']
  unfold PvF
  split_ifs <;> first | (exfalso; omega) | (refine Prod.ext ?_ ?_ <;> simp [vOffset] <;> omega)

theorem piece_vF_even (k : ℕ) (hk : 1 ≤ k) (x : GInt)
    (hx : x ∈ placedSites (vStringAt (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q))
      (2 * (k : ℤ) + 2, 2 * (k : ℤ)))) :
    (x.1, x.2 + 1) ∈ paperNearLadderTile (2 * (k : ℤ) + 2) := by
  have hlen : (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)).length =
      2 * k + 3 := by
    simp only [List.length_cons, List.length_append, List.length_replicate]
    omega
  have key := vStringAt_eq_map (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q))
    (2 * (k : ℤ) + 2, 2 * (k : ℤ)) (PvF k) (by rw [hlen]; omega) (by simp [PvF]) (hstep_vF k)
  rw [key, hlen, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [getD_vF k j hj] at hxj
  unfold PvF at hxj
  split_ifs at hxj <;> simp only [lzq, lzp] at hxj
  all_goals first
    | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
    | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
  all_goals
    unfold paperNearLadderTile paperNearLadderA paperNearLadderB paperNearLadderC paperNearLadderD
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.ext_iff]
    omega

/-! ### InsideTile for the even word `2^k` -/

theorem insideTile_two_even (k : ℕ) (hk : 1 ≤ k) :
    InsideTile ((nladderN (2 * (k : ℤ) + 2) : Finset GInt) : Set GInt)
      (hStringAt (hWordOf (List.replicate k Digit.two) true) (0, 0) ++
        hRevStringAt (hWordOf (List.replicate k Digit.two) true).reverse
          (lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.two) true).reverse (0, 0))) ++
        vRevStringAt (vWordOf (List.replicate k Digit.two) true).reverse (0, 0) ++
        vStringAt (vWordOf (List.replicate k Digit.two) true)
          (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) true) (0, 0)))) := by
  intro x hx
  rw [Finset.mem_coe, mem_nladderN_iff_paper (d := 2 * (k : ℤ) + 2) (by omega)]
  have a1 := anchor_even2 k
  have hW : hWordOf (List.replicate k Digit.two) true = List.replicate (2 * k + 1) Letter.q ++ [Letter.p] := by
    rw [hWordOf_two_true]
    rfl
  have hV : vWordOf (List.replicate k Digit.two) true =
      Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q) := wv_even2 k
  rw [a1, hW, hV] at hx
  have hrH : (List.replicate (2 * k + 1) Letter.q ++ [Letter.p]).reverse =
      Letter.p :: List.replicate (2 * k + 1) Letter.q := by
    simp
  have hrV : (Letter.p :: (List.replicate k Letter.q ++ Letter.p :: List.replicate (k + 1) Letter.q)).reverse =
      List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p]) := by
    simp [List.append_assoc]
  rw [hrH, hrV] at hx
  have hu0 : 0 < (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).length := by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hL : lastPosOf (vRevStringAt (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p]))
      (0, 0)) = (-1, 4 * (k : ℤ) + 2) := by
    rw [vRevStringAt_eq_map _ (0, 0) (PvR k) hu0 (by simp [PvR]) (hstep_vR k), lastPos_range_map _ _ hu0]
    have hlen : (List.replicate (k + 1) Letter.q ++ Letter.p :: (List.replicate k Letter.q ++ [Letter.p])).length =
        2 * k + 3 := by
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      omega
    rw [hlen]
    have e : 2 * k + 3 - 1 = 2 * k + 2 := by omega
    rw [e]
    dsimp only
    unfold PvR
    rw [if_neg (show ¬ (2 * k + 2 ≤ k) by omega), if_neg (show ¬ (2 * k + 2 = k + 1) by omega),
      if_neg (show ¬ (2 * k + 2 ≤ 2 * k + 1) by omega)]
  rw [hL] at hx
  simp only [placedSites_append, List.mem_append] at hx
  rcases hx with ((hA | hB) | hC) | hD
  · exact piece_hF_even k hk x hA
  · exact piece_hR_even k hk (-1, 4 * (k : ℤ) + 2) rfl x hB
  · exact piece_vR_even k hk x hC
  · exact piece_vF_even k hk x hD

end FLatticePaper.Tiles.BaseNearContainEven
