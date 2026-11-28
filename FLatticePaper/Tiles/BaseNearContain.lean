import FLatticePaper.Tiles.RevStringList
import FLatticePaper.Tiles.TileListBridge
import FLatticePaper.Tiles.StackedMoreover
import FLatticePaper.Tiles.BaseCasePseudoSquares
import FLatticePaper.Tiles.BaseHpNear
import FLatticePaper.Tiles.BaseTwoOdd
import FLatticePaper.Tiles.BaseHmAnchor
import FLatticePaper.Tiles.StandardBaseBridge
import FLatticePaper.Tiles.PartialBoundary

/-! # Containment of the near-one placements of the base word `2^k`, odd

The four placed strings of `RespectsAnchored` for the odd word `2^k` (horizontal `q^{2k+2} p`, vertical `p q^{k+1}`) lie in the
near-one stair tile `paperNearStairTile (2k+3)` after the shift `(0,1)` of `nstairN`. The forward and reversed horizontal strings
are handled by their index forms (`zoForwardE_eq_hStringAt`, `hRevStringAt_eq_map`); the vertical strings by induction on the run. -/

namespace FLatticePaper.Tiles.BaseNearContain

open FLatticePaper.Tiles FLatticePaper.Construction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Farey
  FLatticePaper.Tiles.BaseHpNear FLatticePaper.Tiles.BaseTwoOdd FLatticePaper.Tiles.BaseHmAnchor

theorem lzq : letterZTile Letter.q = ZTile.one := rfl
theorem lzp : letterZTile Letter.p = ZTile.zero := rfl

/-! ### Shapes and lists -/

theorem mem_oneD_c (c x : GInt) : x ∈ (tileShape ZTile.oneD).map (· + c) ↔
    ((x.1 - c.1 = 0 ∧ x.2 - c.2 = 0) ∨ (x.1 - c.1 = 0 ∧ x.2 - c.2 = 1) ∨ (x.1 - c.1 = 1 ∧ x.2 - c.2 = 0) ∨
      (x.1 - c.1 = 1 ∧ x.2 - c.2 = 1) ∨ (x.1 - c.1 = -1 ∧ x.2 - c.2 = 1) ∨ (x.1 - c.1 = 1 ∧ x.2 - c.2 = -1)) := by
  simp only [tileShape, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add]
  constructor <;> intro h <;> omega

theorem mem_placed_range (L : ℕ) (f : ℕ → ZTile × GInt) (x : GInt) :
    x ∈ placedSites ((List.range L).map f) ↔ ∃ j, j < L ∧ x ∈ (tileShape (f j).1).map (· + (f j).2) := by
  simp [placedSites, List.flatMap_map, List.mem_flatMap, List.mem_range]

theorem getD_replicate' (b d : Letter) (n j : ℕ) : (List.replicate n b).getD j d = if j < n then b else d := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.replicate_succ, List.getD_cons_succ, ih]
      by_cases h : j < n
      · rw [if_pos h, if_pos (show j + 1 < n + 1 by omega)]
      · rw [if_neg h, if_neg (show ¬ (j + 1 < n + 1) by omega)]

theorem getD_cons_rep (a b d : Letter) (n j : ℕ) :
    (a :: List.replicate n b).getD j d = if j = 0 then a else if j ≤ n then b else d := by
  cases j with
  | zero => simp
  | succ j =>
    rw [List.getD_cons_succ, getD_replicate', if_neg (Nat.succ_ne_zero j)]
    by_cases h : j < n
    · rw [if_pos h, if_pos (show j + 1 ≤ n by omega)]
    · rw [if_neg h, if_neg (show ¬ (j + 1 ≤ n) by omega)]

theorem getD_rep_append (n : ℕ) (a b d : Letter) (j : ℕ) :
    (List.replicate n a ++ [b]).getD j d = if j < n then a else if j = n then b else d := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ j => simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih]
      split_ifs <;> first | rfl | (exfalso; omega)

/-! ### The forward string `q^{2k+2} p` -/

theorem lettersOf_W (k j : ℕ) :
    lettersOf (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) false j =
      if j < 2 * k + 2 then Letter.q else Letter.p := by
  show (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]).getD j Letter.p = _
  rw [getD_rep_append]
  by_cases h : j < 2 * k + 2
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    by_cases h' : j = 2 * k + 2
    · rw [if_pos h']
    · rw [if_neg h']

theorem hTile_W (k j : ℕ) :
    hTileAt (lettersOf (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) false) j =
      if j = 0 then ZTile.one else if j < 2 * k + 2 then ZTile.oneD else ZTile.zero := by
  unfold hTileAt hPrev
  simp only [lettersOf_W]
  split_ifs <;> first | (exfalso; omega) | simp [hTt, letterZTile]

theorem posF_W_le (k : ℕ) : ∀ j, j ≤ 2 * k + 1 →
    posF Orientation.horizontal false (lettersOf (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) false) j =
      ((j : ℤ), (j : ℤ))
  | 0, _ => rfl
  | j + 1, h => by
      rw [posF, posF_W_le k j (by omega), stepOf_hor, lettersOf_W, if_pos (show j + 1 < 2 * k + 2 by omega)]
      simp only [hOffset]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]
        omega
      · simp only [Prod.snd_add]
        omega

theorem posF_W_last (k : ℕ) :
    posF Orientation.horizontal false (lettersOf (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) false)
      (2 * k + 2) = ((2 * (k : ℤ) + 3), (2 * (k : ℤ) + 1)) := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, posF, posF_W_le k (2 * k + 1) le_rfl, stepOf_hor,
    lettersOf_W, if_neg (show ¬ (2 * k + 1 + 1 < 2 * k + 2) by omega)]
  simp only [hOffset]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    omega
  · simp only [Prod.snd_add]
    omega

theorem piece_hF_odd (k : ℕ) (x : GInt)
    (hx : x ∈ placedSites (hStringAt (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]) (0, 0))) :
    (x.1, x.2 + 1) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
  have hlen : (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]).length = 2 * k + 3 := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
  have e := zoForwardE_eq_hStringAt (List.replicate (2 * k + 2) Letter.q ++ [Letter.p])
  rw [hlen] at e
  rw [← e, zoForwardE, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [hTile_W k j] at hxj
  by_cases hjk : j ≤ 2 * k + 1
  · rw [posF_W_le k j hjk] at hxj
    split_ifs at hxj with h0 h1 <;>
    first
      | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
      | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
      | rw [mem_oneD_c] at hxj
    all_goals
      unfold paperNearStairTile
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
      omega
  · have hj2 : j = 2 * k + 2 := by omega
    subst hj2
    rw [posF_W_last, if_neg (show ¬ (2 * k + 2 = 0) by omega), if_neg (show ¬ (2 * k + 2 < 2 * k + 2) by omega),
      mem_shape_zero] at hxj
    simp only [zeroAt] at hxj
    unfold paperNearStairTile
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega

/-! ### The reversed string `p q^{2k+2}` (the reversed horizontal word), from `(0, 2k+1)` -/

theorem lettersOf_U (k j : ℕ) :
    lettersOf (Letter.p :: List.replicate (2 * k + 2) Letter.q) false j =
      if j = 0 then Letter.p else if j ≤ 2 * k + 2 then Letter.q else Letter.p := by
  show (Letter.p :: List.replicate (2 * k + 2) Letter.q).getD j Letter.p = _
  rw [getD_cons_rep]

theorem hTile_U (k j : ℕ) (hj : j < 2 * k + 3) :
    hTileAt (lettersOf (Letter.p :: List.replicate (2 * k + 2) Letter.q) false) j =
      if j = 0 then ZTile.zero else if j = 1 then ZTile.one else ZTile.oneD := by
  unfold hTileAt hPrev
  simp only [lettersOf_U]
  split_ifs <;> first | (exfalso; omega) | simp [hTt, letterZTile]

theorem hstep_U (k : ℕ) :
    ∀ j, j + 1 < (Letter.p :: List.replicate (2 * k + 2) Letter.q).length →
      (fun j : ℕ => if j = 0 then ((0 : ℤ), 2 * (k : ℤ) + 1) else (((j : ℤ) + 1), 2 * (k : ℤ) + 1 + (j : ℤ))) (j + 1) =
        (fun j : ℕ => if j = 0 then ((0 : ℤ), 2 * (k : ℤ) + 1) else (((j : ℤ) + 1), 2 * (k : ℤ) + 1 + (j : ℤ))) j +
          zeroOneHorizontalReversedStep ((Letter.p :: List.replicate (2 * k + 2) Letter.q).getD j Letter.p)
            ((Letter.p :: List.replicate (2 * k + 2) Letter.q).getD (j + 1) Letter.p) := by
  intro j hj
  have hj' : j + 1 < 2 * k + 3 := by
    simp only [List.length_cons, List.length_replicate] at hj
    omega
  rw [← hRevOffset_eq_step, getD_cons_rep, getD_cons_rep]
  by_cases h0 : j = 0
  · subst h0
    refine Prod.ext ?_ ?_ <;> simp [hRevOffset]
  · have h5 : j ≤ 2 * k + 2 := by omega
    have h6 : j + 1 ≤ 2 * k + 2 := by omega
    refine Prod.ext ?_ ?_
    · simp [h0, h5, h6, hRevOffset]
    · simp [h0, h5, h6, hRevOffset]
      omega

theorem piece_hR_odd (k : ℕ) (s : GInt) (hs : s = (0, 2 * (k : ℤ) + 1)) (x : GInt)
    (hx : x ∈ placedSites (hRevStringAt (Letter.p :: List.replicate (2 * k + 2) Letter.q) s)) :
    (x.1, x.2 + 1) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
  subst hs
  have hlen : (Letter.p :: List.replicate (2 * k + 2) Letter.q).length = 2 * k + 3 := by
    simp only [List.length_cons, List.length_replicate]
  have key := hRevStringAt_eq_map (Letter.p :: List.replicate (2 * k + 2) Letter.q) (0, 2 * (k : ℤ) + 1)
    (fun j : ℕ => if j = 0 then ((0 : ℤ), 2 * (k : ℤ) + 1) else (((j : ℤ) + 1), 2 * (k : ℤ) + 1 + (j : ℤ)))
    (by simp) (hstep_U k)
  rw [key, hlen, mem_placed_range] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  dsimp only at hxj
  rw [hTile_U k j (by omega)] at hxj
  split_ifs at hxj with h0 h1 <;>
  first
    | (rw [mem_shape_zero] at hxj; simp only [zeroAt] at hxj)
    | (rw [mem_shape_one] at hxj; simp only [oneAt] at hxj)
    | rw [mem_oneD_c] at hxj
  all_goals
    unfold paperNearStairTile
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    omega

/-! ### The reversed vertical string `q^{k+1} p` and the forward vertical string `p q^{k+1}` -/

theorem vRev_qrun_mem (k : ℕ) : ∀ (c x : GInt),
    x ∈ placedSites (vRevStringAt (List.replicate (k + 1) Letter.q ++ [Letter.p]) c) ↔
      (∃ j : ℕ, j ≤ k ∧ oneAt (c.1, c.2 + 2 * (j : ℤ)) x) ∨ zeroAt (c.1, c.2 + 2 * (k : ℤ) + 1) x := by
  induction k with
  | zero =>
    intro c x
    have e : List.replicate (0 + 1) Letter.q ++ [Letter.p] = [Letter.q, Letter.p] := rfl
    rw [e, vRevStringAt_cons, vRevStringAt_single_p, lzq, placedSites_cons_one, placedSites_cons_zero,
      placedSites_nil, List.append_nil, List.mem_append, mem_shape_one, mem_shape_zero]
    simp only [oneAt, zeroAt, vRevOffset, Prod.fst_add, Prod.snd_add]
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨0, Nat.le_refl 0, by omega⟩
      · exact Or.inr (by omega)
    · rintro (⟨j, hj, h⟩ | h)
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  | succ k ih =>
    intro c x
    have e : List.replicate (k + 1 + 1) Letter.q ++ [Letter.p] =
        Letter.q :: Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) := by
      simp [List.replicate_succ]
    have e2 : Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) = List.replicate (k + 1) Letter.q ++ [Letter.p] := by
      simp [List.replicate_succ]
    rw [e, vRevStringAt_cons, lzq, placedSites_cons_one, List.mem_append, mem_shape_one, e2, ih]
    simp only [oneAt, zeroAt, vRevOffset, Prod.fst_add, Prod.snd_add]
    constructor
    · rintro (h | ⟨j, hj, h⟩ | h)
      · exact Or.inl ⟨0, Nat.zero_le _, by omega⟩
      · exact Or.inl ⟨j + 1, by omega, by omega⟩
      · exact Or.inr (by omega)
    · rintro (⟨j, hj, h⟩ | h)
      · cases j with
        | zero => exact Or.inl (by omega)
        | succ j => exact Or.inr (Or.inl ⟨j, by omega, by omega⟩)
      · exact Or.inr (Or.inr (by omega))

theorem lastPos_vRev_qp (k : ℕ) : ∀ c : GInt,
    lastPosOf (vRevStringAt (List.replicate (k + 1) Letter.q ++ [Letter.p]) c) = (c.1, c.2 + 2 * (k : ℤ) + 1) := by
  induction k with
  | zero =>
    intro c
    have e : List.replicate (0 + 1) Letter.q ++ [Letter.p] = [Letter.q, Letter.p] := rfl
    rw [e, vRevStringAt_cons, vRevStringAt_single_p]
    simp [lastPosOf, vRevOffset]
    exact Prod.ext (by simp) (by simp)
  | succ k ih =>
    intro c
    have e : List.replicate (k + 1 + 1) Letter.q ++ [Letter.p] =
        Letter.q :: Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) := by
      simp [List.replicate_succ]
    have e2 : Letter.q :: (List.replicate k Letter.q ++ [Letter.p]) = List.replicate (k + 1) Letter.q ++ [Letter.p] := by
      simp [List.replicate_succ]
    rw [e, vRevStringAt_cons, lastPosOf_cons_of_ne _ _ (by simp [vRevStringAt]), e2, ih]
    simp only [vRevOffset, Prod.mk.injEq, Prod.fst_add, Prod.snd_add]
    push_cast
    exact ⟨by ring, by ring⟩

theorem piece_vR_odd (k : ℕ) (x : GInt)
    (hx : x ∈ placedSites (vRevStringAt (List.replicate (k + 1) Letter.q ++ [Letter.p]) (0, 0))) :
    (x.1, x.2 + 1) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
  rw [vRev_qrun_mem k (0, 0) x] at hx
  unfold paperNearStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
  rcases hx with ⟨j, hj, h⟩ | h
  · simp only [oneAt] at h
    omega
  · simp only [zeroAt] at h
    omega

theorem oneRun_mem (n : ℕ) : ∀ (t x : GInt),
    x ∈ placedSites (vStringAt (List.replicate (n + 1) Letter.q) t) ↔
      ∃ j : ℕ, j ≤ n ∧ oneAt (t.1, t.2 + 2 * (j : ℤ)) x := by
  induction n with
  | zero =>
    intro t x
    have e : vStringAt (List.replicate (0 + 1) Letter.q) t = [(ZTile.one, t)] := by
      simp [vStringAt, lzq]
    rw [e, placedSites_cons_one, placedSites_nil, List.append_nil, mem_shape_one]
    simp only [oneAt]
    constructor
    · intro h
      exact ⟨0, Nat.le_refl 0, by omega⟩
    · rintro ⟨j, hj, h⟩
      omega
  | succ n ih =>
    intro t x
    have e : List.replicate (n + 1 + 1) Letter.q = Letter.q :: Letter.q :: List.replicate n Letter.q := by
      simp [List.replicate_succ]
    have e2 : Letter.q :: List.replicate n Letter.q = List.replicate (n + 1) Letter.q := by
      simp [List.replicate_succ]
    rw [e, vStringAt_cons, lzq, placedSites_cons_one, List.mem_append, mem_shape_one, e2, ih]
    simp only [oneAt, vOffset, Prod.fst_add, Prod.snd_add]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, Nat.zero_le _, by omega⟩
      · exact ⟨j + 1, by omega, by omega⟩
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero => exact Or.inl (by omega)
      | succ j => exact Or.inr ⟨j, by omega, by omega⟩

theorem vF_run_mem (k : ℕ) (t x : GInt) :
    x ∈ placedSites (vStringAt (Letter.p :: List.replicate (k + 1) Letter.q) t) ↔
      zeroAt t x ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ k + 1 ∧ oneAt (t.1, t.2 + 2 * (j : ℤ)) x := by
  have e : Letter.p :: List.replicate (k + 1) Letter.q = Letter.p :: Letter.q :: List.replicate k Letter.q := by
    simp [List.replicate_succ]
  have e2 : Letter.q :: List.replicate k Letter.q = List.replicate (k + 1) Letter.q := by
    simp [List.replicate_succ]
  rw [e, vStringAt_cons, lzp, placedSites_cons_zero, List.mem_append, mem_shape_zero, e2, oneRun_mem]
  simp only [zeroAt, oneAt, vOffset, Prod.fst_add, Prod.snd_add]
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j + 1, by omega, by omega, by omega⟩
  · rintro (h | ⟨j, hj1, hj2, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j - 1, by omega, by omega⟩

theorem piece_vF_odd (k : ℕ) (x : GInt)
    (hx : x ∈ placedSites (vStringAt (Letter.p :: List.replicate (k + 1) Letter.q) (2 * (k : ℤ) + 3, 2 * (k : ℤ) + 1))) :
    (x.1, x.2 + 1) ∈ paperNearStairTile (2 * (k : ℤ) + 3) := by
  rw [vF_run_mem] at hx
  unfold paperNearStairTile
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
  rcases hx with h | ⟨j, hj1, hj2, h⟩
  · simp only [zeroAt] at h
    omega
  · simp only [oneAt] at h
    omega

/-! ### InsideTile for the odd word `2^k` -/

theorem insideTile_two_odd (k : ℕ) :
    InsideTile ((nstairN (2 * (k : ℤ) + 3) : Finset GInt) : Set GInt)
      (hStringAt (hWordOf (List.replicate k Digit.two) false) (0, 0) ++
        hRevStringAt (hWordOf (List.replicate k Digit.two) false).reverse
          (lastPosOf (vRevStringAt (vWordOf (List.replicate k Digit.two) false).reverse (0, 0))) ++
        vRevStringAt (vWordOf (List.replicate k Digit.two) false).reverse (0, 0) ++
        vStringAt (vWordOf (List.replicate k Digit.two) false)
          (lastPosOf (hStringAt (hWordOf (List.replicate k Digit.two) false) (0, 0)))) := by
  intro x hx
  rw [Finset.mem_coe, mem_nstairN_iff_paper (d := 2 * (k : ℤ) + 3) (by omega)]
  have a1 := anchor_two k
  have hW : hWordOf (List.replicate k Digit.two) false = List.replicate (2 * k + 2) Letter.q ++ [Letter.p] := by
    rw [hWordOf_two_false]
    rfl
  have hV : vWordOf (List.replicate k Digit.two) false = Letter.p :: List.replicate (k + 1) Letter.q := wv_two k
  rw [a1, hW, hV] at hx
  have hrH : (List.replicate (2 * k + 2) Letter.q ++ [Letter.p]).reverse =
      Letter.p :: List.replicate (2 * k + 2) Letter.q := by
    simp
  have hrV : (Letter.p :: List.replicate (k + 1) Letter.q).reverse =
      List.replicate (k + 1) Letter.q ++ [Letter.p] := by
    simp
  rw [hrH, hrV] at hx
  have hL : lastPosOf (vRevStringAt (List.replicate (k + 1) Letter.q ++ [Letter.p]) (0, 0)) =
      (0, 2 * (k : ℤ) + 1) := by
    have := lastPos_vRev_qp k (0, 0)
    simpa using this
  rw [hL] at hx
  simp only [placedSites_append, List.mem_append] at hx
  rcases hx with ((hA | hB) | hC) | hD
  · exact piece_hF_odd k x hA
  · exact piece_hR_odd k (0, 2 * (k : ℤ) + 1) rfl x hB
  · exact piece_vR_odd k x hC
  · exact piece_vF_odd k x hD

end FLatticePaper.Tiles.BaseNearContain
