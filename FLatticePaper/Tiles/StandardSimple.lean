import FLatticePaper.Tiles.ArcInequality
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.CheckerFree

/-! Task 53: the standard tiles are simple. The row inequalities of `cellRowChain_of_arc_inequalities` need
(a) the letter classes of the boundary words (`admissible_oddStandard`, `admissible_evenStandard`),
(b) the two sum inequalities, from the Farey data of the parents (`bottomEdges_odd_sum`, `bottomEdges_even_sum`,
`parentsAt_swap_eq`, and the unit interval bounds of the parents), and
(c) the corner condition, from the boundary-word hypothesis (a reversal at the corner would put a boundary edge and its
reverse into the boundary). Then the row chain gives edge-connectivity and no checkerboard vertex, and simplicity follows. -/

namespace FLatticePaper.Tiles.StandardSimple

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary
open FLatticePaper.Tiles.StandardClause

/-! ### (a) letter classes -/

theorem oddBottom_letters (w : Word) : ∀ x ∈ oddBottom w, x = .one ∨ x = .i :=
  (admissible_oddStandard w).1.1

theorem oddRight_letters (w : Word) : ∀ x ∈ oddRight w, x = .i ∨ x = .negOne := by
  intro x hx
  have hm := (admissible_oddStandard w).2.1 (Unit4.mulNegI x) (List.mem_map_of_mem hx)
  clear hx
  revert hm
  cases x <;> decide

theorem evenBottom_letters (w : Word) : ∀ x ∈ evenBottom w, x = .one ∨ x = .i :=
  (admissible_evenStandard w).1.1

theorem evenRight_letters (w : Word) : ∀ x ∈ evenRight w, x = .i ∨ x = .negOne := by
  intro x hx
  have hm := (admissible_evenStandard w).2.1 (Unit4.mulNegI x) (List.mem_map_of_mem hx)
  clear hx
  revert hm
  cases x <;> decide

/-! ### (b) the sums of the boundary words, through the Farey data -/

theorem sum_oddBottom (w : Word) :
    F2Word.sum (oddBottom w) = texV1Odd ((parentsAt w).current .odd) - gI :=
  eq_sub_of_add_eq (bottomEdges_odd_sum w)

theorem sum_oddRight (w : Word) :
    F2Word.sum (oddRight w) =
      rotI (texV1Even ((parentsAt (w.map Digit.swapTwoThree)).current .even) - gI) := by
  unfold oddRight
  rw [F2Word_sum_map_mulI]
  congr 1
  exact eq_sub_of_add_eq (bottomEdges_even_sum (w.map Digit.swapTwoThree))

theorem sum_evenBottom (w : Word) :
    F2Word.sum (evenBottom w) = texV1Even ((parentsAt w).current .even) - gI :=
  eq_sub_of_add_eq (bottomEdges_even_sum w)

theorem sum_evenRight (w : Word) :
    F2Word.sum (evenRight w) =
      rotI (texV1Odd ((parentsAt (w.map Digit.swapTwoThree)).current .odd) - gI) := by
  unfold evenRight
  rw [F2Word_sum_map_mulI]
  congr 1
  exact eq_sub_of_add_eq (bottomEdges_odd_sum (w.map Digit.swapTwoThree))

/-- The arithmetic core of the odd sum inequalities, for the unit interval parents `p`, `q` (`0 ≤ num ≤ den`), with the
even parent `q` of even sum. -/
theorem odd_sum_core (pn pd qn qd : ℤ) (hp1 : 0 ≤ pn) (hp2 : pn ≤ pd)
    (hq1 : 0 ≤ qn) (hq2 : qn ≤ qd) (hqe : (qn + qd) % 2 = 0) :
    2 * (pn + qn) - 1 < 2 * ((qd + qn) / 2) + (pd + pn) ∧
      0 < 2 * (pd + qd) + (1 - (2 * ((qd - qn) / 2) + (pd - pn))) := by
  constructor <;> omega

/-- The arithmetic core of the even sum inequalities. -/
theorem even_sum_core (pn pd qn qd : ℤ) (hp1 : 0 ≤ pn) (hp2 : pn ≤ pd)
    (hq1 : 0 ≤ qn) (hq2 : qn ≤ qd) (hqe : (qn + qd) % 2 = 0) :
    2 * pn + qn - 1 < 2 * ((qd + qn) / 2 + (pd + pn)) ∧
      0 < 2 * pd + qd + (1 - 2 * ((qd - qn) / 2 + (pd - pn))) := by
  constructor <;> omega

/-- The two sum inequalities of the odd tile: `S1.y < S2.y` and `0 < S1.x + S2.x`. -/
theorem standard_sums_odd (w : Word) :
    (F2Word.sum (oddBottom w)).2 < (F2Word.sum (oddRight w)).2 ∧
      0 < (F2Word.sum (oddBottom w)).1 + (F2Word.sum (oddRight w)).1 := by
  have hV := parentsAt_valid w
  have hsw := parentsAt_swap_eq w
  have hp := hV.odd_bounds
  have hq := hV.even_bounds
  have hqe : (parentsAt w).even.Even := hV.even_parity
  have hpo : (parentsAt w).odd.Odd := hV.odd_parity
  rw [sum_oddBottom, sum_oddRight, hsw]
  have hrq := Fraction.rotate_of_even hqe
  have hrp := Fraction.rotate_of_odd hpo
  simp only [Parents.current, Parents.combine, texV1Odd, texV1Even, rotI, gI, Prod.fst_sub, Prod.snd_sub,
    hrq, hrp]
  obtain ⟨hA, hB⟩ := odd_sum_core (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den hp.2.1 hp.2.2 hq.2.1 hq.2.2 hqe
  constructor <;> omega

/-- The two sum inequalities of the even tile. -/
theorem standard_sums_even (w : Word) :
    (F2Word.sum (evenBottom w)).2 < (F2Word.sum (evenRight w)).2 ∧
      0 < (F2Word.sum (evenBottom w)).1 + (F2Word.sum (evenRight w)).1 := by
  have hV := parentsAt_valid w
  have hsw := parentsAt_swap_eq w
  have hp := hV.odd_bounds
  have hq := hV.even_bounds
  have hqe : (parentsAt w).even.Even := hV.even_parity
  have hpo : (parentsAt w).odd.Odd := hV.odd_parity
  rw [sum_evenBottom, sum_evenRight, hsw]
  have hrq := Fraction.rotate_of_even hqe
  have hrp := Fraction.rotate_of_odd hpo
  simp only [Parents.current, Parents.combine, texV1Odd, texV1Even, rotI, gI, Prod.fst_sub, Prod.snd_sub,
    hrq, hrp]
  obtain ⟨hA, hB⟩ := even_sum_core (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den hp.2.1 hp.2.2 hq.2.1 hq.2.2 hqe
  constructor <;> omega

/-! ### (c) the corner condition, from the boundary-word hypothesis -/

/-- A north boundary edge `(v, v + i)` leaves `v` outside the tile. -/
theorem north_edge_not_mem (T : CellTile) (v : GInt) (h : (v, v + gI) ∈ T.boundaryEdges) : v ∉ T := by
  rcases boundary_out T v (v + gI) h with ⟨hb, -, -⟩ | ⟨-, -, hv⟩ | ⟨hb, -, -⟩ | ⟨hb, -, -⟩
  · exfalso
    simp [Prod.ext_iff, gI, gOne] at hb
  · exact hv
  · exfalso
    simp [Prod.ext_iff, gI, gOne] at hb
  · exfalso
    simp [Prod.ext_iff, gI] at hb
    omega

/-- A south boundary edge `(v, v - i)` has its target `v - i` in the tile. -/
theorem south_edge_mem (T : CellTile) (v : GInt) (h : (v, v - gI) ∈ T.boundaryEdges) : v - gI ∈ T := by
  rcases boundary_out T v (v - gI) h with ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨hb, -, -⟩ | ⟨-, h4, -⟩
  · exfalso
    simp [Prod.ext_iff, gI, gOne] at hb
  · exfalso
    simp [Prod.ext_iff, gI] at hb
    omega
  · exfalso
    simp [Prod.ext_iff, gI, gOne] at hb
  · exact h4

theorem edgesFrom_last (c : GInt) (X : F2Word) (x : Unit4) :
    (c + F2Word.sum X, c + F2Word.sum X + x.vec) ∈ edgesFrom c (X ++ [x]) := by
  rw [edgesFrom_append]
  simp [edgesFrom]

theorem edgesFrom_head (c : GInt) (x : Unit4) (R : F2Word) : (c, c + x.vec) ∈ edgesFrom c (x :: R) := by
  simp [edgesFrom]

/-- The corner condition: the boundary word of a tile does not start with `i` and end with `i` at the same corner
(the two edges of the reversal would both be boundary edges). -/
theorem corner_not_both (T : CellTile) (w1 w2 : F2Word) (hT : IsBoundaryWordAt T (0, 0) (boundaryWordOf w1 w2)) :
    ¬ (w1.head? = some .i ∧ w2.getLast? = some .i) := by
  rintro ⟨hh, hl⟩
  have hE : (edgesFrom (0, 0) (boundaryWordOf w1 w2)).toFinset = T.boundaryEdges := by
    have h := hT.2.2.2
    rwa [zip_walk_eq] at h
  rcases w1 with _ | ⟨x, w1'⟩
  · simp at hh
  have hx : x = .i := by simpa using hh
  subst hx
  rcases List.eq_nil_or_concat w2 with h | ⟨u, y, rfl⟩
  · subst h
    simp at hl
  rw [List.concat_eq_append] at hE hl
  have hy : y = .i := by simpa using hl
  subst hy
  have hW : boundaryWordOf (Unit4.i :: w1') (u ++ [Unit4.i]) =
      ((Unit4.i :: w1') ++ u ++ [Unit4.i]) ++
        (Unit4.negI :: (w1'.map Unit4.neg ++ (u ++ [Unit4.i]).map Unit4.neg)) := by
    simp [boundaryWordOf, hat_rev, Unit4.neg]
  rw [hW] at hE
  -- the north edge after the letters `(i :: w1') ++ u`
  have m1 : (F2Word.sum ((Unit4.i :: w1') ++ u), F2Word.sum ((Unit4.i :: w1') ++ u) + gI) ∈
      edgesFrom (0, 0) (((Unit4.i :: w1') ++ u ++ [Unit4.i]) ++
        (Unit4.negI :: (w1'.map Unit4.neg ++ (u ++ [Unit4.i]).map Unit4.neg))) := by
    rw [edgesFrom_append]
    apply List.mem_append_left
    have h := edgesFrom_last ((0 : ℤ), (0 : ℤ)) ((Unit4.i :: w1') ++ u) Unit4.i
    rw [arc_zero_add] at h
    exact h
  have f1 : (F2Word.sum ((Unit4.i :: w1') ++ u), F2Word.sum ((Unit4.i :: w1') ++ u) + gI) ∈
      T.boundaryEdges := by
    rw [← hE]
    exact List.mem_toFinset.mpr m1
  -- the south edge after the whole prefix `(i :: w1') ++ u ++ [i]`
  have m2 : (((0 : ℤ), (0 : ℤ)) + F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]),
      ((0 : ℤ), (0 : ℤ)) + F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) + Unit4.vec Unit4.negI) ∈
      edgesFrom (0, 0) (((Unit4.i :: w1') ++ u ++ [Unit4.i]) ++
        (Unit4.negI :: (w1'.map Unit4.neg ++ (u ++ [Unit4.i]).map Unit4.neg))) := by
    rw [edgesFrom_append]
    apply List.mem_append_right
    exact edgesFrom_head _ Unit4.negI _
  rw [arc_zero_add] at m2
  have f2 : (F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]),
      F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) + Unit4.vec Unit4.negI) ∈ T.boundaryEdges := by
    rw [← hE]
    exact List.mem_toFinset.mpr m2
  have hsA : F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) =
      F2Word.sum ((Unit4.i :: w1') ++ u) + gI := by
    rw [arc_sum_append]
    simp [F2Word.sum, Unit4.vec, gI]
  have e1 : F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) + Unit4.vec Unit4.negI =
      F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) - gI := by
    ext <;> simp [Unit4.vec, gI, sub_eq_add_neg]
  rw [e1] at f2
  have hX := south_edge_mem T _ f2
  have e3 : F2Word.sum (((Unit4.i :: w1') ++ u) ++ [Unit4.i]) - gI = F2Word.sum ((Unit4.i :: w1') ++ u) := by
    rw [hsA]
    abel
  rw [e3] at hX
  exact north_edge_not_mem T _ f1 hX

/-! ### The row chain and simplicity of the standard tiles -/

theorem cellRowChain_odd (w : Word) (hB : StandardBoundaryOdd w) :
    CellRowChain (cellTileOf (oddTile w)) :=
  cellRowChain_of_arc_inequalities (cellTileOf (oddTile w)) (oddBottom w) (oddRight w) hB
    (oddBottom_letters w) (oddRight_letters w) (standard_sums_odd w).1 (standard_sums_odd w).2
    (corner_not_both _ _ _ hB)

theorem cellRowChain_even (w : Word) (hB : StandardBoundaryEven w) :
    CellRowChain (cellTileOf (evenTile w)) :=
  cellRowChain_of_arc_inequalities (cellTileOf (evenTile w)) (evenBottom w) (evenRight w) hB
    (evenBottom_letters w) (evenRight_letters w) (standard_sums_even w).1 (standard_sums_even w).2
    (corner_not_both _ _ _ hB)

/-- The odd standard tile is simple, from its boundary-word statement alone. -/
theorem simpleOdd_of_standardBoundary (w : Word) (hB : StandardBoundaryOdd w) :
    IsSimpleTile (cellTileOf (oddTile w)) := by
  have hC := cellRowChain_odd w hB
  exact ⟨⟨(0, 0), boundaryWordOf (oddBottom w) (oddRight w), hB,
      walk_dropLast_nodup _ _ _ hB (fun v => cellRowChain_no_checker hC v)⟩,
    (edgeConnected_iff _).mpr (cellRowChain_edgeConnected hC)⟩

/-- The even standard tile is simple, from its boundary-word statement alone. -/
theorem simpleEven_of_standardBoundary (w : Word) (hB : StandardBoundaryEven w) :
    IsSimpleTile (cellTileOf (evenTile w)) := by
  have hC := cellRowChain_even w hB
  exact ⟨⟨(0, 0), boundaryWordOf (evenBottom w) (evenRight w), hB,
      walk_dropLast_nodup _ _ _ hB (fun v => cellRowChain_no_checker hC v)⟩,
    (edgeConnected_iff _).mpr (cellRowChain_edgeConnected hC)⟩

/-- The standard tiles are simple, the only input being the boundary-word statement `StandardBoundaryWord`. -/
theorem simpleOdd_of_standardBoundaryWord (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    IsSimpleTile (cellTileOf (oddTile w)) :=
  simpleOdd_of_standardBoundary w (bd w).1

theorem simpleEven_of_standardBoundaryWord (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    IsSimpleTile (cellTileOf (evenTile w)) :=
  simpleEven_of_standardBoundary w (bd w).2

end FLatticePaper.Tiles.StandardSimple
