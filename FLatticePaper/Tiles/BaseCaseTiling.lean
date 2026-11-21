import FLatticePaper.Tiles.RowScan
import FLatticePaper.Tiles.WalkRows
import FLatticePaper.Tiles.BaseCasePseudoSquares

/-! The cell tiles of the reciprocal base tiles of `prop:base_cases` (d), and their boundary words.

A cell tile is a finite set of lower-left corners (`CellTile`). The reciprocal staircase `paperStairTile (2k+3)` and the
doubled staircase `paperLadderTile (2k+2)` (`k ≥ 1`) are the vertex sets of explicit cell sets (`stairCells`, `ladderCells`); the
pseudo-boundary word `pseudoBoundaryWord (gPseudo w_h w_v)` traces their boundary. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperStairTile)
open FLatticePaper.Construction (paperLadderTile paperLadderA paperLadderB paperLadderC paperLadderD)

/-- The bottom edge of the cell `(a, b)`: its lower side, with the cell `(a, b-1)` on the other side. -/
theorem bottom_mem (T : CellTile) (a b : ℤ) :
    ((a, b), (a + 1, b)) ∈ T.boundaryEdges ↔ ((a, b) : GInt) ∈ T ∧ ((a, b - 1) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · have hc' : c = (a, b) := by
        simp [gOne, Prod.ext_iff] at hfe
        exact Prod.ext (by omega) (by omega)
      subst hc'
      refine ⟨hc, ?_⟩
      have h1 : ((a, b) : GInt) - gI = (a, b - 1) := by simp [gI]
      rw [h1] at hnot
      exact hnot
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gI, Prod.ext_iff] at hfe
      omega
  · rintro ⟨hc, hnot⟩
    refine ⟨(a, b), hc, ((a, b), (a, b) + gOne, (a, b) - gI), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · have h1 : ((a, b - 1) : GInt) = (a, b) - gI := by simp [gI]
      rw [h1] at hnot
      exact hnot
    · simp [gOne]

/-- The top edge of the cell `(a, b)`: its upper side from `(a+1, b+1)` to `(a, b+1)`, with the cell `(a, b+1)` on the
other side. -/
theorem top_mem (T : CellTile) (a b : ℤ) :
    ((a + 1, b + 1), (a, b + 1)) ∈ T.boundaryEdges ↔ ((a, b) : GInt) ∈ T ∧ ((a, b + 1) : GInt) ∉ T := by
  rw [mem_boundaryEdges_iff]
  constructor
  · rintro ⟨c, hc, f, hf, hnot, hfe⟩
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exfalso
      simp [gOne, Prod.ext_iff] at hfe
      omega
    · exfalso
      simp [gOne, gI, Prod.ext_iff] at hfe
      omega
    · have hc' : c = (a, b) := by
        simp [gOne, gI, Prod.ext_iff] at hfe
        exact Prod.ext (by omega) (by omega)
      subst hc'
      refine ⟨hc, ?_⟩
      have h1 : ((a, b) : GInt) + gI = (a, b + 1) := by simp [gI]
      rw [h1] at hnot
      exact hnot
    · exfalso
      simp [gI, Prod.ext_iff] at hfe
      omega
  · rintro ⟨hc, hnot⟩
    refine ⟨(a, b), hc, ((a, b) + gOne + gI, (a, b) + gI, (a, b) + gI), ?_, ?_, ?_⟩
    · simp [cellEdgesWithOther]
    · have h1 : ((a, b + 1) : GInt) = (a, b) + gI := by simp [gI]
      rw [h1] at hnot
      exact hnot
    · simp [gOne, gI]

/-! ### The reciprocal staircase -/

/-- The cells of the reciprocal staircase `paperStairTile d`, as lower-left corners (`d` odd, `d = 2k+3`). -/
def stairInT (d a b : ℤ) : Prop :=
  (2 - d ≤ a ∧ a ≤ d - 1 ∧ 0 ≤ b ∧ b ≤ d ∧ 1 ≤ a + b ∧ a + b ≤ d) ∨ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = d)

instance (d a b : ℤ) : Decidable (stairInT d a b) := by
  unfold stairInT
  infer_instance

/-- The cell tile of the reciprocal staircase of denominator `d`. -/
def stairCells (d : ℤ) : CellTile :=
  ((Finset.Icc (2 - d) d) ×ˢ (Finset.Icc 0 (d + 1))).filter fun x => stairInT d x.1 x.2

theorem mem_stairCells (d : ℤ) (hd : 3 ≤ d) (x : GInt) : x ∈ stairCells d ↔ stairInT d x.1 x.2 := by
  unfold stairCells
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> unfold stairInT at h <;> omega

/-- The membership of a corner of a cell, in coordinates. -/
theorem mem_cellCorners_iff (c x : GInt) :
    x ∈ cellCorners c ↔ (x.1 = c.1 ∧ x.2 = c.2) ∨ (x.1 = c.1 + 1 ∧ x.2 = c.2) ∨ (x.1 = c.1 ∧ x.2 = c.2 + 1) ∨
      (x.1 = c.1 + 1 ∧ x.2 = c.2 + 1) := by
  simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, gOne, gI, Prod.fst_add,
    Prod.snd_add]
  constructor <;> intro h <;> omega

/-- Every site of the staircase is a corner of a cell of the staircase cell set. -/
theorem stair_cell_choice (d : ℤ) (hd : 3 ≤ d) (x : GInt)
    (hx : (2 - d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d + 1 ∧ 1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2) ∨
      (x.1 = 0 ∧ x.2 = 0) ∨ (x.1 = 2 ∧ x.2 = d + 1)) :
    stairInT d x.1 x.2 ∨ stairInT d (x.1 - 1) x.2 ∨ stairInT d x.1 (x.2 - 1) ∨
      stairInT d (x.1 - 1) (x.2 - 1) := by
  rcases hx with ⟨ha1, ha2, hb1, hb2, hs1, hs2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hA : x.1 ≤ d - 1 ∧ x.2 ≤ d ∧ x.1 + x.2 ≤ d
    · exact Or.inl (by unfold stairInT; omega)
    · by_cases hB : x.1 ≤ d - 1 ∧ x.2 ≤ d
      · exact Or.inr (Or.inr (Or.inr (by unfold stairInT; omega)))
      · by_cases hC : x.1 = d ∧ x.2 ≤ 1
        · exact Or.inr (Or.inl (by unfold stairInT; omega))
        · by_cases hD : x.1 = d ∧ x.2 = 2
          · exact Or.inr (Or.inr (Or.inr (by unfold stairInT; omega)))
          · by_cases ha0 : x.1 ≤ 0
            · exact Or.inr (Or.inr (Or.inl (by unfold stairInT; omega)))
            · exact Or.inr (Or.inr (Or.inr (by unfold stairInT; omega)))
  · exact Or.inl (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

/-- The vertices of the cells of `stairCells d` are exactly the sites of `paperStairTile d`. -/
theorem mem_stairVertices (d : ℤ) (hd : 3 ≤ d) (x : GInt) :
    x ∈ (stairCells d).vertices ↔ x ∈ paperStairTile d := by
  rw [mem_stairT_disj]
  unfold CellTile.vertices
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    rw [mem_stairCells d (by omega) c] at hc
    rw [mem_cellCorners_iff] at hx
    unfold stairInT at hc
    omega
  · intro hx
    have key := stair_cell_choice d hd x hx
    rcases key with h | h | h | h
    · exact ⟨x, (mem_stairCells d (by omega) x).2 h, (mem_cellCorners_iff x x).2 (by omega)⟩
    · exact ⟨(x.1 - 1, x.2), (mem_stairCells d (by omega) _).2 h, (mem_cellCorners_iff _ x).2 (by omega)⟩
    · exact ⟨(x.1, x.2 - 1), (mem_stairCells d (by omega) _).2 h, (mem_cellCorners_iff _ x).2 (by omega)⟩
    · exact ⟨(x.1 - 1, x.2 - 1), (mem_stairCells d (by omega) _).2 h, (mem_cellCorners_iff _ x).2 (by omega)⟩

/-- The lower-left vertex of the reciprocal staircase cell tile is `(0,0)` (line 1100). -/
theorem stairCells_lowerLeft (d : ℤ) (hd : 3 ≤ d) : IsLowerLeft (stairCells d) (0, 0) := by
  unfold IsLowerLeft
  constructor
  · rw [mem_stairVertices d hd]
    exact (mem_stairT_disj d (0, 0)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro v hv
    rw [mem_stairVertices d hd, mem_stairT_disj] at hv
    omega

/-! ### The explicit G-words of the stair family -/

theorem flat_zero (m : ℕ) :
    (((List.replicate (m + 1) ZTile.zero).zip (List.replicate m ZTile.zero)).flatMap fun ab => gPair ab.1 ab.2) =
      (List.replicate m [Unit4.one, Unit4.one]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (List.replicate (m + 1 + 1) ZTile.zero).zip (List.replicate (m + 1) ZTile.zero) =
        (ZTile.zero, ZTile.zero) :: (List.replicate (m + 1) ZTile.zero).zip (List.replicate m ZTile.zero) := by
      simp [List.replicate_succ]
    rw [e, List.flatMap_cons, ih]
    simp [List.replicate_succ, gPair]

theorem flat_ones (k : ℕ) : (List.replicate k [Unit4.one, Unit4.one]).flatten = List.replicate (2 * k) Unit4.one := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      List.replicate_succ, List.replicate_succ]
    simp

theorem gH_stairH (k : ℕ) : gH (stairH k) = List.replicate (2 * k + 3) Unit4.one := by
  simp only [gH, stairH, tileSeq_q_rep_p, List.tail_cons]
  have e : (ZTile.one :: List.replicate (k + 1) ZTile.zero).zip (List.replicate (k + 1) ZTile.zero) =
      (ZTile.one, ZTile.zero) :: (List.replicate (k + 1) ZTile.zero).zip (List.replicate k ZTile.zero) := by
    simp [List.replicate_succ]
  rw [e, List.flatMap_cons, flat_zero, flat_ones]
  simp only [gPair, List.cons_append, List.nil_append]
  rw [← List.replicate_succ', List.replicate_succ, show 2 * k + 3 = 2 * k + 1 + 1 + 1 by ring,
    List.replicate_succ, List.replicate_succ]
  simp
  rfl

theorem flat_oneD (n : ℕ) :
    (((List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]).zip (List.replicate n ZTile.oneD ++ [ZTile.zero])).flatMap
      fun ab => gPair ab.1 ab.2) = (List.replicate (n + 1) [Unit4.i, Unit4.one]).flatten := by
  induction n with
  | zero => simp [gPair]
  | succ n ih =>
    have e1 : List.replicate (n + 1 + 1) ZTile.oneD ++ [ZTile.zero] =
        ZTile.oneD :: (List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero]) := by
      simp [List.replicate_succ]
    have e2 : List.replicate (n + 1) ZTile.oneD ++ [ZTile.zero] =
        ZTile.oneD :: (List.replicate n ZTile.oneD ++ [ZTile.zero]) := by
      simp [List.replicate_succ]
    rw [e1]
    rw [e2] at ih ⊢
    simp only [List.zip_cons_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    simp [gPair, List.replicate_succ]

theorem gH_stair_flip (k : ℕ) :
    gH (flipW (stairV k)) = [Unit4.one, Unit4.one] ++ (List.replicate (2 * k + 1) [Unit4.i, Unit4.one]).flatten ++
      [Unit4.one] := by
  have hf : flipW (stairV k) = List.replicate (2 * k + 1 + 1) Letter.q ++ [Letter.p] := by
    simp only [stairV, flipW, flipLetter, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
  rw [hf]
  simp only [gH, tileSeq_flip, List.tail_cons]
  have e : (ZTile.one :: (List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero])).zip
      (List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero]) =
      (ZTile.one, ZTile.oneD) :: ((List.replicate (2 * k + 1) ZTile.oneD ++ [ZTile.zero]).zip
        (List.replicate (2 * k) ZTile.oneD ++ [ZTile.zero])) := by
    simp [List.replicate_succ]
  rw [e, List.flatMap_cons, flat_oneD (2 * k)]
  simp [gPair]

theorem gV_stair (k : ℕ) :
    gV (stairV k) = [Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i] := by
  unfold gV
  rw [gH_stair_flip]
  simp [List.map_flatten, List.map_replicate, Unit4.mulI, List.map_append]

/-- The explicit boundary word `w1 * w2 * hat(rev w1) * hat(rev w2)` of the reciprocal staircase. -/
def stairWord (k : ℕ) : F2Word :=
  List.replicate (2 * k + 3) Unit4.one ++
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
    (List.replicate (2 * k + 3) Unit4.negOne ++
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]))

theorem pseudoBoundaryWord_stair (k : ℕ) :
    pseudoBoundaryWord (gPseudo (stairH k) (stairV k)).1 (gPseudo (stairH k) (stairV k)).2 = stairWord k := by
  simp [gPseudo, pseudoBoundaryWord, gH_stairH, gV_stair, stairWord, hat_rev_eq_map_neg, List.map_flatten,
    Unit4.neg, List.append_assoc]

/-! ### Edges of the walk segments -/

theorem mem_edgesFrom_one (c : GInt) (n : ℕ) (e : GInt × GInt) :
    e ∈ edgesFrom c (List.replicate n Unit4.one) ↔
      ∃ j : ℕ, j < n ∧ e = ((c.1 + (j : ℤ), c.2), (c.1 + (j : ℤ) + 1, c.2)) := by
  induction n generalizing c with
  | zero => simp [edgesFrom]
  | succ n ih =>
    rw [List.replicate_succ, edgesFrom, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]⟩
      · exact ⟨j + 1, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega⟩
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff])
      · exact Or.inr ⟨j, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega⟩

theorem mem_edgesFrom_negOne (c : GInt) (n : ℕ) (e : GInt × GInt) :
    e ∈ edgesFrom c (List.replicate n Unit4.negOne) ↔
      ∃ j : ℕ, j < n ∧ e = ((c.1 - (j : ℤ), c.2), (c.1 - (j : ℤ) - 1, c.2)) := by
  induction n generalizing c with
  | zero => simp [edgesFrom]
  | succ n ih =>
    rw [List.replicate_succ, edgesFrom, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega⟩
      · exact ⟨j + 1, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega⟩
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
      · exact Or.inr ⟨j, by omega, by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega⟩

theorem mem_edgesFrom_negOne_i (c : GInt) (n : ℕ) (e : GInt × GInt) :
    e ∈ edgesFrom c (List.replicate n [Unit4.negOne, Unit4.i]).flatten ↔
      ∃ j : ℕ, j < n ∧ (e = ((c.1 - (j : ℤ), c.2 + (j : ℤ)), (c.1 - (j : ℤ) - 1, c.2 + (j : ℤ))) ∨
        e = ((c.1 - (j : ℤ) - 1, c.2 + (j : ℤ)), (c.1 - (j : ℤ) - 1, c.2 + (j : ℤ) + 1))) := by
  induction n generalizing c with
  | zero => simp [edgesFrom]
  | succ n ih =>
    have hfl : (List.replicate (n + 1) [Unit4.negOne, Unit4.i]).flatten =
        Unit4.negOne :: Unit4.i :: (List.replicate n [Unit4.negOne, Unit4.i]).flatten := by
      simp [List.replicate_succ]
    rw [hfl, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, ih]
    constructor
    · rintro (h | h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)⟩
      · exact ⟨0, by omega, Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)⟩
      · refine ⟨j + 1, by omega, ?_⟩
        rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
        · exact Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
        · exact Or.inr (Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega))
      · refine Or.inr (Or.inr ⟨j, by omega, ?_⟩)
        rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
        · exact Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)

theorem mem_edgesFrom_one_negI (c : GInt) (n : ℕ) (e : GInt × GInt) :
    e ∈ edgesFrom c (List.replicate n [Unit4.one, Unit4.negI]).flatten ↔
      ∃ j : ℕ, j < n ∧ (e = ((c.1 + (j : ℤ), c.2 - (j : ℤ)), (c.1 + (j : ℤ) + 1, c.2 - (j : ℤ))) ∨
        e = ((c.1 + (j : ℤ) + 1, c.2 - (j : ℤ)), (c.1 + (j : ℤ) + 1, c.2 - (j : ℤ) - 1))) := by
  induction n generalizing c with
  | zero => simp [edgesFrom]
  | succ n ih =>
    have hfl : (List.replicate (n + 1) [Unit4.one, Unit4.negI]).flatten =
        Unit4.one :: Unit4.negI :: (List.replicate n [Unit4.one, Unit4.negI]).flatten := by
      simp [List.replicate_succ]
    rw [hfl, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, ih]
    constructor
    · rintro (h | h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff])⟩
      · exact ⟨0, by omega, Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)⟩
      · refine ⟨j + 1, by omega, ?_⟩
        rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
        · exact Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff])
        · exact Or.inr (Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega))
      · refine Or.inr (Or.inr ⟨j, by omega, ?_⟩)
        rcases h with h | h
        · exact Or.inl (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)
        · exact Or.inr (by rw [h]; simp [Unit4.vec, Prod.ext_iff]; omega)

/-! ### The four shapes of a boundary edge -/

/-- The boundary edges of a cell tile, by their four shapes: the north, south, bottom and top edges of the cells. -/
def BShape (T : CellTile) (e : GInt × GInt) : Prop :=
  ∃ a b : ℤ, (e = ((a, b), (a, b + 1)) ∧ ((a - 1, b) : GInt) ∈ T ∧ ((a, b) : GInt) ∉ T) ∨
    (e = ((a, b + 1), (a, b)) ∧ ((a, b) : GInt) ∈ T ∧ ((a - 1, b) : GInt) ∉ T) ∨
    (e = ((a, b), (a + 1, b)) ∧ ((a, b) : GInt) ∈ T ∧ ((a, b - 1) : GInt) ∉ T) ∨
    (e = ((a + 1, b + 1), (a, b + 1)) ∧ ((a, b) : GInt) ∈ T ∧ ((a, b + 1) : GInt) ∉ T)

theorem eq_add_one (c : GInt) : c + gOne = (c.1 + 1, c.2) := Prod.ext (by simp [gOne]) (by simp [gOne])

theorem eq_add_I (c : GInt) : c + gI = (c.1, c.2 + 1) := Prod.ext (by simp [gI]) (by simp [gI])

theorem eq_sub_I (c : GInt) : c - gI = (c.1, c.2 - 1) := Prod.ext (by simp [gI]) (by simp [gI])

theorem eq_sub_one (c : GInt) : c - gOne = (c.1 - 1, c.2) := Prod.ext (by simp [gOne]) (by simp [gOne])

theorem mem_boundaryEdges_iff_shape (T : CellTile) (e : GInt × GInt) :
    e ∈ T.boundaryEdges ↔ BShape T e := by
  constructor
  · intro he
    rw [mem_boundaryEdges_iff] at he
    obtain ⟨c, hc, f, hf, hnot, rfl⟩ := he
    simp only [cellEdgesWithOther, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · have h1 : ((c.1, c.2 - 1) : GInt) ∉ T := by rw [show ((c.1, c.2 - 1) : GInt) = c - gI from (eq_sub_I c).symm]; exact hnot
      exact ⟨c.1, c.2, Or.inr (Or.inr (Or.inl ⟨by rw [eq_add_one], hc, h1⟩))⟩
    · have h1 : ((c.1 + 1, c.2) : GInt) ∉ T := by rw [show ((c.1 + 1, c.2) : GInt) = c + gOne from (eq_add_one c).symm]; exact hnot
      have h2 : ((c.1, c.2) : GInt) ∈ T := hc
      exact ⟨c.1 + 1, c.2, Or.inl ⟨by rw [eq_add_one, eq_add_I], by simpa using h2, h1⟩⟩
    · have h1 : ((c.1, c.2 + 1) : GInt) ∉ T := by rw [show ((c.1, c.2 + 1) : GInt) = c + gI from (eq_add_I c).symm]; exact hnot
      exact ⟨c.1, c.2, Or.inr (Or.inr (Or.inr ⟨by rw [eq_add_one, eq_add_I, eq_add_I], hc, h1⟩))⟩
    · have h1 : ((c.1 - 1, c.2) : GInt) ∉ T := by rw [show ((c.1 - 1, c.2) : GInt) = c - gOne from (eq_sub_one c).symm]; exact hnot
      exact ⟨c.1, c.2, Or.inr (Or.inl ⟨by rw [eq_add_I], hc, h1⟩)⟩
  · rintro ⟨a, b, h⟩
    rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
    · exact (north_mem T a b).2 ⟨h1, h2⟩
    · exact (south_mem T a b).2 ⟨h1, h2⟩
    · exact (bottom_mem T a b).2 ⟨h1, h2⟩
    · exact (top_mem T a b).2 ⟨h1, h2⟩

/-! ### Sums of the walk segments -/

theorem sum_rep_one (n : ℕ) : F2Word.sum (List.replicate n Unit4.one) = ((n : ℤ), 0) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_rep_negOne (n : ℕ) : F2Word.sum (List.replicate n Unit4.negOne) = (-(n : ℤ), 0) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_flat_negOne_i (m : ℕ) :
    F2Word.sum (List.replicate m [Unit4.negOne, Unit4.i]).flatten = (-(m : ℤ), (m : ℤ)) := by
  induction m with
  | zero => simp [F2Word.sum, Prod.ext_iff]
  | succ m ih =>
    have hfl : (List.replicate (m + 1) [Unit4.negOne, Unit4.i]).flatten =
        Unit4.negOne :: Unit4.i :: (List.replicate m [Unit4.negOne, Unit4.i]).flatten := by
      simp [List.replicate_succ]
    have h1 : F2Word.sum (Unit4.negOne :: Unit4.i :: (List.replicate m [Unit4.negOne, Unit4.i]).flatten) =
        Unit4.vec Unit4.negOne + (Unit4.vec Unit4.i + F2Word.sum (List.replicate m [Unit4.negOne, Unit4.i]).flatten) := by
      simp [F2Word.sum]
    rw [hfl, h1, ih]
    simp only [Unit4.vec, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    push_cast
    omega

theorem sum_flat_one_negI (m : ℕ) :
    F2Word.sum (List.replicate m [Unit4.one, Unit4.negI]).flatten = ((m : ℤ), -(m : ℤ)) := by
  induction m with
  | zero => simp [F2Word.sum, Prod.ext_iff]
  | succ m ih =>
    have hfl : (List.replicate (m + 1) [Unit4.one, Unit4.negI]).flatten =
        Unit4.one :: Unit4.negI :: (List.replicate m [Unit4.one, Unit4.negI]).flatten := by
      simp [List.replicate_succ]
    have h1 : F2Word.sum (Unit4.one :: Unit4.negI :: (List.replicate m [Unit4.one, Unit4.negI]).flatten) =
        Unit4.vec Unit4.one + (Unit4.vec Unit4.negI + F2Word.sum (List.replicate m [Unit4.one, Unit4.negI]).flatten) := by
      simp [F2Word.sum]
    rw [hfl, h1, ih]
    simp only [Unit4.vec, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    push_cast
    omega

theorem sum_w2_stair (k : ℕ) :
    F2Word.sum ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) =
      (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) := by
  rw [f2sum_append, f2sum_append, sum_flat_negOne_i]
  simp only [F2Word.sum, Unit4.vec, Prod.ext_iff, Prod.fst_add, Prod.snd_add, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, Prod.fst_zero, Prod.snd_zero]
  push_cast
  omega

theorem sum_w4_stair (k : ℕ) :
    F2Word.sum ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI]) = (2 * (k : ℤ) + 1, -(2 * (k : ℤ) + 4)) := by
  rw [f2sum_append, f2sum_append, sum_flat_one_negI]
  simp only [F2Word.sum, Unit4.vec, Prod.ext_iff, Prod.fst_add, Prod.snd_add, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, Prod.fst_zero, Prod.snd_zero]
  push_cast
  omega

/-- The walk of the four blocks of a word `(A ++ W2) ++ (C ++ W4)` splits into the four walks, from the partial sums. -/
theorem mem_edgesFrom_four (c : GInt) (A W2 C W4 : F2Word) (e : GInt × GInt) :
    e ∈ edgesFrom c ((A ++ W2) ++ (C ++ W4)) ↔
      e ∈ edgesFrom c A ∨ e ∈ edgesFrom (c + F2Word.sum A) W2 ∨
        e ∈ edgesFrom (c + F2Word.sum A + F2Word.sum W2) C ∨
        e ∈ edgesFrom (c + F2Word.sum A + F2Word.sum W2 + F2Word.sum C) W4 := by
  simp only [edgesFrom_append, f2sum_append, List.mem_append, ← add_assoc]
  tauto

/-- The walk of the reciprocal staircase `stairWord k` from `(0,0)`, in its four blocks. -/
theorem mem_stairWord_four (k : ℕ) (e : GInt × GInt) :
    e ∈ edgesFrom (0, 0) (stairWord k) ↔
      e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one) ∨
      e ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
        ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ∨
      e ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne) ∨
      e ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
        ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
          [Unit4.negI]) := by
  rw [stairWord, mem_edgesFrom_four, sum_rep_one, sum_w2_stair, sum_rep_negOne]
  have p2 : ((0, 0) : GInt) + ((((2 * k + 3 : ℕ)) : ℤ), 0) = (2 * (k : ℤ) + 3, 0) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  have p3 : (2 * (k : ℤ) + 3, (0 : ℤ)) + (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) = (2, 2 * (k : ℤ) + 4) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  have p4 : (2, 2 * (k : ℤ) + 4) + (-(((2 * k + 3 : ℕ)) : ℤ), 0) = (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4) :=
    Prod.ext (by simp; try ring) (by simp; try ring)
  rw [p2, p3, p4]

theorem mem_sc (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) : ((a, b) : GInt) ∈ stairCells d ↔ stairInT d a b :=
  mem_stairCells d hd (a, b)

/-- The second block of the stair walk: two north steps, the staircase of pairs, and the last north step. -/
theorem seg2_cases (k : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i])) :
    e = ((2 * (k : ℤ) + 3, 0), (2 * (k : ℤ) + 3, 1)) ∨ e = ((2 * (k : ℤ) + 3, 1), (2 * (k : ℤ) + 3, 2)) ∨
      (∃ j : ℕ, j < 2 * k + 1 ∧
        (e = ((2 * (k : ℤ) + 3 - j, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ))) ∨
          e = ((2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ) + 1)))) ∨
      e = ((2, 2 * (k : ℤ) + 3), (2, 2 * (k : ℤ) + 3 + 1)) := by
  have hW : [Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] =
      Unit4.i :: Unit4.i :: ((List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_negOne_i] at h
  rcases h with h | h | h | h
  · left
    rw [h]
    simp [Unit4.vec, Prod.mk_add_mk]
  · right; left
    rw [h]
    simp [Unit4.vec, Prod.mk_add_mk]
  · right; right; left
    obtain ⟨j, hj, h'⟩ := h
    refine ⟨j, hj, ?_⟩
    rcases h' with h' | h'
    · left
      rw [h']
      simp [Unit4.vec, Prod.mk_add_mk]
    · right
      rw [h']
      simp [Unit4.vec, Prod.mk_add_mk]
  · right; right; right
    simp only [edgesFrom, List.mem_singleton] at h
    rw [h, sum_flat_negOne_i]
    simp [Unit4.vec, Prod.mk_add_mk]; omega

/-- The first block of the stair walk: the lower side. -/
theorem seg1_cases (k : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one)) :
    ∃ j : ℕ, j < 2 * k + 3 ∧ e = (((j : ℤ), 0), ((j : ℤ) + 1, 0)) := by
  rw [mem_edgesFrom_one] at h
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj, by rw [h]; simp⟩

/-- The third block of the stair walk: the upper side, from `(2, 2k+4)` to `(2-d, 2k+4)`. -/
theorem seg3_cases (k : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne)) :
    ∃ j : ℕ, j < 2 * k + 3 ∧ e = ((2 - (j : ℤ), 2 * (k : ℤ) + 4), (2 - (j : ℤ) - 1, 2 * (k : ℤ) + 4)) := by
  rw [mem_edgesFrom_negOne] at h
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj, h⟩

/-- The fourth block of the stair walk: the left side, from `(2-d, 2k+4)` down to `(0,0)`. -/
theorem seg4_cases (k : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e = ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4), (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3)) ∨
      e = ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3), (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 2)) ∨
      (∃ j : ℕ, j < 2 * k + 1 ∧
        (e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ), 2 * (k : ℤ) + 2 - (j : ℤ)),
            (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ))) ∨
          e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ)),
            (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ) - 1)))) ∨
      e = ((0, 1), (0, 0)) := by
  have hW : [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI] = Unit4.negI :: Unit4.negI :: ((List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
        [Unit4.negI]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_one_negI] at h
  rcases h with h | h | h | h
  · left
    rw [h]
    simp [Unit4.vec, Prod.mk_add_mk]; omega
  · right; left
    rw [h]
    simp [Unit4.vec, Prod.mk_add_mk]; omega
  · right; right; left
    obtain ⟨j, hj, h'⟩ := h
    refine ⟨j, hj, ?_⟩
    rcases h' with h' | h'
    · left
      rw [h']
      simp [Unit4.vec, Prod.mk_add_mk]; omega
    · right
      rw [h']
      simp [Unit4.vec, Prod.mk_add_mk]; omega
  · right; right; right
    simp only [edgesFrom, List.mem_singleton] at h
    rw [h, sum_flat_one_negI]
    simp [Unit4.vec, Prod.mk_add_mk]; omega

/-- Every edge of the stair walk is a boundary edge of the reciprocal staircase cell tile. -/
theorem stair_walk_sub (k : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (0, 0) (stairWord k)) :
    BShape (stairCells (2 * (k : ℤ) + 3)) e := by
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  rw [mem_stairWord_four] at h
  rcases h with h1 | h2 | h3 | h4
  · -- the lower side: bottom edges of the cells `(j, 0)`
    obtain ⟨j, hj, rfl⟩ := seg1_cases k e h1
    refine ⟨(j : ℤ), 0, Or.inr (Or.inr (Or.inl ⟨by simp, (mem_sc _ hd _ _).2 ?_, ?_⟩))⟩
    · unfold stairInT
      omega
    · intro hm
      have := (mem_sc _ hd _ _).1 hm
      unfold stairInT at this
      omega
  · rcases seg2_cases k e h2 with h | h | ⟨j, hj, h | h⟩ | h
    · -- north edge of the cell `(d-1, 0)`
      refine ⟨2 * (k : ℤ) + 3, 0, Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · refine ⟨2 * (k : ℤ) + 3, 1, Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- a top edge of the cell `(d-j-1, 1+j)`
      refine ⟨2 * (k : ℤ) + 3 - (j : ℤ) - 1, 1 + (j : ℤ), Or.inr (Or.inr (Or.inr ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩))⟩
      · subst h; simp [Prod.mk.injEq]; omega
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- a north edge of the cell `(d-j-1, 2+j)`
      refine ⟨2 * (k : ℤ) + 3 - (j : ℤ) - 1, 2 + (j : ℤ), Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- the last north edge of the cell `(1, d)`... of the cell `(2, d)`
      refine ⟨2, 2 * (k : ℤ) + 3, Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
  · obtain ⟨j, hj, h⟩ := seg3_cases k e h3
    refine ⟨1 - (j : ℤ), 2 * (k : ℤ) + 3, Or.inr (Or.inr (Or.inr ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩))⟩
    · subst h; simp [Prod.mk.injEq]; omega
    · unfold stairInT; omega
    · intro hm
      have := (mem_sc _ hd _ _).1 hm
      unfold stairInT at this
      omega
  · rcases seg4_cases k e h4 with h | h | ⟨j, hj, h | h⟩ | h
    · -- south edge of the cell `(2-d, d)`
      refine ⟨2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3, Or.inr (Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩)⟩
      · subst h; simp [Prod.mk.injEq]; omega
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · refine ⟨2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 2, Or.inr (Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩)⟩
      · subst h; simp [Prod.mk.injEq]; omega
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- bottom edge of the cell `(2-d+j, 2k+2-j)`
      refine ⟨2 - (2 * (k : ℤ) + 3) + (j : ℤ), 2 * (k : ℤ) + 2 - (j : ℤ), Or.inr (Or.inr (Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩))⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- south edge of the cell `(3-d+j, 2k+1-j)`
      refine ⟨2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 1 - (j : ℤ), Or.inr (Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩)⟩
      · subst h; simp [Prod.mk.injEq]; omega
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega
    · -- the last south edge, of the cell `(0,0)`
      refine ⟨0, 0, Or.inr (Or.inl ⟨?_, (mem_sc _ hd _ _).2 ?_, ?_⟩)⟩
      · subst h; simp
      · unfold stairInT; omega
      · intro hm
        have := (mem_sc _ hd _ _).1 hm
        unfold stairInT at this
        omega

/-- The explicit edges of the first block are edges of its walk. -/
theorem seg1_mem (k : ℕ) (e : GInt × GInt) (j : ℕ) (hj : j < 2 * k + 3) (h : e = (((j : ℤ), 0), ((j : ℤ) + 1, 0))) :
    e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one) :=
  (mem_edgesFrom_one _ _ _).2 ⟨j, hj, by subst h; simp⟩

/-- The explicit edges of the third block are edges of its walk. -/
theorem seg3_mem (k : ℕ) (e : GInt × GInt) (j : ℕ) (hj : j < 2 * k + 3)
    (h : e = ((2 - (j : ℤ), 2 * (k : ℤ) + 4), (2 - (j : ℤ) - 1, 2 * (k : ℤ) + 4))) :
    e ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne) :=
  (mem_edgesFrom_negOne _ _ _).2 ⟨j, hj, by subst h; simp⟩

/-- The explicit edges of the second block are edges of its walk. -/
theorem seg2_mem (k : ℕ) (e : GInt × GInt)
    (h : e = ((2 * (k : ℤ) + 3, 0), (2 * (k : ℤ) + 3, 1)) ∨ e = ((2 * (k : ℤ) + 3, 1), (2 * (k : ℤ) + 3, 2)) ∨
      (∃ j : ℕ, j < 2 * k + 1 ∧
        (e = ((2 * (k : ℤ) + 3 - j, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ))) ∨
          e = ((2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ) + 1)))) ∨
      e = ((2, 2 * (k : ℤ) + 3), (2, 2 * (k : ℤ) + 3 + 1))) :
    e ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
        ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
  have hW : [Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] =
      Unit4.i :: Unit4.i :: ((List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_negOne_i]
  rcases h with h | h | ⟨j, hj, h | h⟩ | h
  · left; subst h; simp [Unit4.vec, Prod.mk_add_mk]
  · right; left; subst h; simp [Unit4.vec, Prod.mk_add_mk]
  · right; right; left
    exact ⟨j, hj, Or.inl (by subst h; simp [Unit4.vec, Prod.mk_add_mk])⟩
  · right; right; left
    exact ⟨j, hj, Or.inr (by subst h; simp [Unit4.vec, Prod.mk_add_mk])⟩
  · right; right; right
    simp only [edgesFrom, List.mem_singleton]
    subst h
    rw [sum_flat_negOne_i]
    simp [Unit4.vec, Prod.mk_add_mk]; omega

/-- The explicit edges of the fourth block are edges of its walk. -/
theorem seg4_mem (k : ℕ) (e : GInt × GInt)
    (h : e = ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4), (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3)) ∨
      e = ((2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 3), (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 2)) ∨
      (∃ j : ℕ, j < 2 * k + 1 ∧
        (e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ), 2 * (k : ℤ) + 2 - (j : ℤ)),
            (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ))) ∨
          e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ)),
            (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ) - 1)))) ∨
      e = ((0, 1), (0, 0))) :
    e ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]) := by
  have hW : [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI] = Unit4.negI :: Unit4.negI :: ((List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
        [Unit4.negI]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_one_negI]
  rcases h with h | h | ⟨j, hj, h | h⟩ | h
  · left; subst h; simp [Unit4.vec, Prod.mk_add_mk]; omega
  · right; left; subst h; simp [Unit4.vec, Prod.mk_add_mk]; omega
  · right; right; left
    exact ⟨j, hj, Or.inl (by subst h; simp [Unit4.vec, Prod.mk_add_mk]; omega)⟩
  · right; right; left
    exact ⟨j, hj, Or.inr (by subst h; simp [Unit4.vec, Prod.mk_add_mk]; omega)⟩
  · right; right; right
    simp only [edgesFrom, List.mem_singleton]
    subst h
    rw [sum_flat_one_negI]
    simp [Unit4.vec, Prod.mk_add_mk]; omega

/-! ### Boundary shapes of the stair cell tile -/

theorem N_cases (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) (h : stairInT d (a - 1) b ∧ ¬stairInT d a b) :
    (b = 0 ∧ a = d) ∨ (1 ≤ b ∧ b ≤ d - 1 ∧ a = d - b + 1) ∨ (b = d ∧ a = 2) := by
  obtain ⟨h1, h2⟩ := h
  unfold stairInT at h1 h2
  omega

theorem S_cases (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) (h : stairInT d a b ∧ ¬stairInT d (a - 1) b) :
    (b = 0 ∧ a = 0) ∨ (1 ≤ b ∧ b ≤ d - 1 ∧ a = 1 - b) ∨ (b = d ∧ a = 2 - d) := by
  obtain ⟨h1, h2⟩ := h
  unfold stairInT at h1 h2
  omega

theorem Bo_cases (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) (h : stairInT d a b ∧ ¬stairInT d a (b - 1)) :
    (b = 0 ∧ 0 ≤ a ∧ a ≤ d - 1) ∨ (2 ≤ b ∧ b ≤ d - 1 ∧ a = 1 - b) := by
  obtain ⟨h1, h2⟩ := h
  unfold stairInT at h1 h2
  omega

theorem To_cases (d : ℤ) (hd : 3 ≤ d) (a b : ℤ) (h : stairInT d a b ∧ ¬stairInT d a (b + 1)) :
    (b = d ∧ 2 - d ≤ a ∧ a ≤ 1) ∨ (b = 1 ∧ a = d - 1) ∨ (2 ≤ b ∧ b ≤ d - 2 ∧ a = d - b) := by
  obtain ⟨h1, h2⟩ := h
  unfold stairInT at h1 h2
  omega

theorem walk_seg1 (k : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one)) :
    e ∈ edgesFrom (0, 0) (stairWord k) := by
  rw [mem_stairWord_four]
  exact Or.inl h

theorem walk_seg2 (k : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i])) :
    e ∈ edgesFrom (0, 0) (stairWord k) := by
  rw [mem_stairWord_four]
  exact Or.inr (Or.inl h)

theorem walk_seg3 (k : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne)) :
    e ∈ edgesFrom (0, 0) (stairWord k) := by
  rw [mem_stairWord_four]
  exact Or.inr (Or.inr (Or.inl h))

theorem walk_seg4 (k : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e ∈ edgesFrom (0, 0) (stairWord k) := by
  rw [mem_stairWord_four]
  exact Or.inr (Or.inr (Or.inr h))

/-- Every boundary edge of the reciprocal staircase cell tile is an edge of the stair walk. -/
theorem stair_bdry_sub (k : ℕ) (e : GInt × GInt) (h : BShape (stairCells (2 * (k : ℤ) + 3)) e) :
    e ∈ edgesFrom (0, 0) (stairWord k) := by
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  obtain ⟨a, b, hs⟩ := h
  rcases hs with ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩
  · -- north edges
    rw [mem_sc _ hd] at h1 h2
    rcases N_cases (2 * (k : ℤ) + 3) hd a b ⟨h1, h2⟩ with ⟨hb, ha⟩ | ⟨hb1, hb2, ha⟩ | ⟨hb, ha⟩
    · exact walk_seg2 k e (seg2_mem k e (Or.inl (by rw [he]; simp [Prod.mk.injEq]; omega)))
    · by_cases hb1' : b = 1
      · exact walk_seg2 k e (seg2_mem k e (Or.inr (Or.inl (by rw [he]; simp [Prod.mk.injEq]; omega))))
      · obtain ⟨j, hj⟩ := exists_nat_of_int (b - 2) (by omega)
        have hj' : j < 2 * k + 1 := by omega
        have hN : e = ((2 * (k : ℤ) + 3 - j, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ))) ∨
            e = ((2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ)), (2 * (k : ℤ) + 3 - j - 1, 2 + (j : ℤ) + 1)) :=
          Or.inr (by rw [he]; simp [Prod.mk.injEq]; omega)
        exact walk_seg2 k e (seg2_mem k e (Or.inr (Or.inr (Or.inl ⟨j, hj', hN⟩))))
    · exact walk_seg2 k e (seg2_mem k e (Or.inr (Or.inr (Or.inr (by rw [he]; simp [Prod.mk.injEq]; omega)))))
  · -- south edges
    rw [mem_sc _ hd] at h1 h2
    rcases S_cases (2 * (k : ℤ) + 3) hd a b ⟨h1, h2⟩ with ⟨hb, ha⟩ | ⟨hb1, hb2, ha⟩ | ⟨hb, ha⟩
    · exact walk_seg4 k e (seg4_mem k e (Or.inr (Or.inr (Or.inr (by rw [he]; simp [Prod.mk.injEq]; omega)))))
    · by_cases hb3 : b = 2 * (k : ℤ) + 2
      · exact walk_seg4 k e (seg4_mem k e (Or.inr (Or.inl (by rw [he]; simp [Prod.mk.injEq]; omega))))
      · obtain ⟨j, hj⟩ := exists_nat_of_int (2 * (k : ℤ) + 1 - b) (by omega)
        have hj' : j < 2 * k + 1 := by omega
        have hS : e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ)),
            (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ) - 1)) :=
          by rw [he]; simp [Prod.mk.injEq]; omega
        exact walk_seg4 k e (seg4_mem k e (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inr hS⟩))))
    · exact walk_seg4 k e (seg4_mem k e (Or.inl (by rw [he]; simp [Prod.mk.injEq]; omega)))
  · -- bottom edges
    rw [mem_sc _ hd] at h1 h2
    rcases Bo_cases (2 * (k : ℤ) + 3) hd a b ⟨h1, h2⟩ with ⟨hb, ha1, ha2⟩ | ⟨hb1, hb2, ha⟩
    · obtain ⟨j, hj⟩ := exists_nat_of_int a ha1
      have hj' : j < 2 * k + 3 := by omega
      exact walk_seg1 k e (seg1_mem k e j hj' (by rw [he]; simp [Prod.mk.injEq]; omega))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (2 * (k : ℤ) + 2 - b) (by omega)
      have hj' : j < 2 * k + 1 := by omega
      have hB : e = ((2 - (2 * (k : ℤ) + 3) + (j : ℤ), 2 * (k : ℤ) + 2 - (j : ℤ)),
          (2 - (2 * (k : ℤ) + 3) + (j : ℤ) + 1, 2 * (k : ℤ) + 2 - (j : ℤ))) :=
        by rw [he]; simp [Prod.mk.injEq]; omega
      exact walk_seg4 k e (seg4_mem k e (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inl hB⟩))))
  · -- top edges
    rw [mem_sc _ hd] at h1 h2
    rcases To_cases (2 * (k : ℤ) + 3) hd a b ⟨h1, h2⟩ with ⟨hb, ha1, ha2⟩ | ⟨hb, ha⟩ | ⟨hb1, hb2, ha⟩
    · obtain ⟨j, hj⟩ := exists_nat_of_int (1 - a) (by omega)
      have hj' : j < 2 * k + 3 := by omega
      exact walk_seg3 k e (seg3_mem k e j hj' (by rw [he]; simp [Prod.mk.injEq]; omega))
    · exact walk_seg2 k e (seg2_mem k e (Or.inr (Or.inr (Or.inl ⟨0, by omega, Or.inl
        (by rw [he]; simp [Prod.mk.injEq]; omega)⟩))))
    · obtain ⟨j, hj⟩ := exists_nat_of_int (b - 1) (by omega)
      have hj' : j < 2 * k + 1 := by omega
      exact walk_seg2 k e (seg2_mem k e (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inl
        (by rw [he]; simp [Prod.mk.injEq]; omega)⟩))))

/-! ### The walk of the stair tile is a simple closed walk -/

/-- The potential `y - x` of a lattice point. -/
def yMinusX (p : GInt) : ℤ := p.2 - p.1

theorem yMinusX_add_pos (c : GInt) (x : Unit4) (hx : x = Unit4.i ∨ x = Unit4.negOne) :
    yMinusX (c + x.vec) = yMinusX c + 1 := by
  rcases hx with rfl | rfl <;> simp [yMinusX, Unit4.vec, Prod.fst_add, Prod.snd_add] <;> omega

theorem yMinusX_add_neg (c : GInt) (x : Unit4) (hx : x = Unit4.one ∨ x = Unit4.negI) :
    yMinusX (c + x.vec) = yMinusX c - 1 := by
  rcases hx with rfl | rfl <;> simp [yMinusX, Unit4.vec, Prod.fst_add, Prod.snd_add] <;> omega

theorem yMinusX_ge_pos : ∀ (w : F2Word) (c : GInt) (e : GInt × GInt),
    (∀ x ∈ w, x = Unit4.i ∨ x = Unit4.negOne) → e ∈ edgesFrom c w → yMinusX c ≤ yMinusX e.1
  | [], _, _, _, he => by simp [edgesFrom] at he
  | x :: w, c, e, hw, he => by
    rw [edgesFrom, List.mem_cons] at he
    rcases he with rfl | he
    · exact le_refl _
    · have h1 := yMinusX_ge_pos w (c + x.vec) e (fun y hy => hw y (by simp [hy])) he
      rw [yMinusX_add_pos c x (hw x (by simp))] at h1
      omega

theorem yMinusX_le_neg : ∀ (w : F2Word) (c : GInt) (e : GInt × GInt),
    (∀ x ∈ w, x = Unit4.one ∨ x = Unit4.negI) → e ∈ edgesFrom c w → yMinusX e.1 ≤ yMinusX c
  | [], _, _, _, he => by simp [edgesFrom] at he
  | x :: w, c, e, hw, he => by
    rw [edgesFrom, List.mem_cons] at he
    rcases he with rfl | he
    · exact le_refl _
    · have h1 := yMinusX_le_neg w (c + x.vec) e (fun y hy => hw y (by simp [hy])) he
      rw [yMinusX_add_neg c x (hw x (by simp))] at h1
      omega

theorem yMinusX_pairwise_pos : ∀ (w : F2Word) (c : GInt),
    (∀ x ∈ w, x = Unit4.i ∨ x = Unit4.negOne) →
      ((edgesFrom c w).map (fun e => yMinusX e.1)).Pairwise (· < ·)
  | [], _, _ => by simp [edgesFrom]
  | x :: w, c, hw => by
    rw [edgesFrom, List.map_cons, List.pairwise_cons]
    refine ⟨?_, yMinusX_pairwise_pos w (c + x.vec) (fun y hy => hw y (by simp [hy]))⟩
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨e, he, rfl⟩ := hb
    have h1 := yMinusX_ge_pos w (c + x.vec) e (fun y hy => hw y (by simp [hy])) he
    rw [yMinusX_add_pos c x (hw x (by simp))] at h1
    show yMinusX c < yMinusX e.1
    omega

theorem yMinusX_pairwise_neg : ∀ (w : F2Word) (c : GInt),
    (∀ x ∈ w, x = Unit4.one ∨ x = Unit4.negI) →
      ((edgesFrom c w).map (fun e => yMinusX e.1)).Pairwise (· > ·)
  | [], _, _ => by simp [edgesFrom]
  | x :: w, c, hw => by
    rw [edgesFrom, List.map_cons, List.pairwise_cons]
    refine ⟨?_, yMinusX_pairwise_neg w (c + x.vec) (fun y hy => hw y (by simp [hy]))⟩
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨e, he, rfl⟩ := hb
    have h1 := yMinusX_le_neg w (c + x.vec) e (fun y hy => hw y (by simp [hy])) he
    rw [yMinusX_add_neg c x (hw x (by simp))] at h1
    show yMinusX c > yMinusX e.1
    omega

/-- A walk whose letters are all `i` or `-1` has no repeated edge. -/
theorem edgesFrom_nodup_pos (w : F2Word) (c : GInt) (hw : ∀ x ∈ w, x = Unit4.i ∨ x = Unit4.negOne) :
    (edgesFrom c w).Nodup :=
  List.Nodup.of_map (fun e : GInt × GInt => yMinusX e.1)
    (List.Pairwise.imp (fun h => ne_of_lt h) (yMinusX_pairwise_pos w c hw))

/-- A walk whose letters are all `1` or `-i` has no repeated edge. -/
theorem edgesFrom_nodup_neg (w : F2Word) (c : GInt) (hw : ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.negI) :
    (edgesFrom c w).Nodup :=
  List.Nodup.of_map (fun e : GInt × GInt => yMinusX e.1)
    (List.Pairwise.imp (fun h => ne_of_gt h) (yMinusX_pairwise_neg w c hw))

theorem mem_flat_pair (m : ℕ) (a b x : Unit4) (h : x ∈ (List.replicate m [a, b]).flatten) :
    x = a ∨ x = b := by
  induction m with
  | zero => simp at h
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · simpa using h
    · exact ih h

theorem letters_W2C (k : ℕ) : ∀ x ∈ ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i]) ++ List.replicate (2 * k + 3) Unit4.negOne, x = Unit4.i ∨ x = Unit4.negOne := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · simp at h; exact Or.inl h
      · rcases mem_flat_pair _ _ _ x h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
    · simp at h; exact Or.inl h
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem letters_W4 (k : ℕ) : ∀ x ∈ [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI], x = Unit4.one ∨ x = Unit4.negI := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · simp at h; exact Or.inr h
    · rcases mem_flat_pair _ _ _ x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  · simp at h; exact Or.inr h

theorem edgesFrom_four_list (c : GInt) (A W2 C W4 : F2Word) :
    edgesFrom c ((A ++ W2) ++ (C ++ W4)) =
      edgesFrom c A ++ edgesFrom (c + F2Word.sum A) W2 ++
        (edgesFrom (c + F2Word.sum A + F2Word.sum W2) C ++
          edgesFrom (c + F2Word.sum A + F2Word.sum W2 + F2Word.sum C) W4) := by
  simp only [edgesFrom_append, List.append_assoc]

theorem start_p2 (k : ℕ) : ((0, 0) : GInt) + ((((2 * k + 3 : ℕ)) : ℤ), 0) = (2 * (k : ℤ) + 3, 0) :=
  Prod.ext (by simp; try ring) (by simp; try ring)

theorem start_p3 (k : ℕ) :
    (2 * (k : ℤ) + 3, (0 : ℤ)) + (-(2 * (k : ℤ) + 1), 2 * (k : ℤ) + 4) = (2, 2 * (k : ℤ) + 4) :=
  Prod.ext (by simp; try ring) (by simp; try ring)

theorem start_p4 (k : ℕ) :
    (2, 2 * (k : ℤ) + 4) + (-(((2 * k + 3 : ℕ)) : ℤ), 0) = (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4) :=
  Prod.ext (by simp; try ring) (by simp; try ring)

/-- The walk of `stairWord k` splits into the bottom run, the upper arc and the left run. -/
theorem stairWord_edges (k : ℕ) :
    edgesFrom (0, 0) (stairWord k) =
      edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one) ++
        ((edgesFrom (2 * (k : ℤ) + 3, 0)
            ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
          edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne)) ++
          edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
            ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
              [Unit4.negI])) := by
  rw [stairWord, edgesFrom_four_list, sum_rep_one, sum_w2_stair, sum_rep_negOne, start_p2, start_p3, start_p4]
  simp only [List.append_assoc]

theorem disj_P_Q (k : ℕ) (a b : GInt × GInt)
    (ha : a ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one))
    (hb : b ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
        ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
      edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne)) : a ≠ b := by
  obtain ⟨j, hj, rfl⟩ := seg1_cases k a ha
  intro heq
  rcases List.mem_append.1 hb with hb | hb
  · rcases seg2_cases k b hb with h | h | ⟨m, hm, h | h⟩ | h <;>
      (rw [h] at heq; simp only [Prod.mk.injEq] at heq; omega)
  · obtain ⟨m, hm, h⟩ := seg3_cases k b hb
    rw [h] at heq; simp only [Prod.mk.injEq] at heq; omega

theorem disj_P_R (k : ℕ) (a b : GInt × GInt)
    (ha : a ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one))
    (hb : b ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
        ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
          [Unit4.negI])) : a ≠ b := by
  obtain ⟨j, hj, rfl⟩ := seg1_cases k a ha
  intro heq
  rcases seg4_cases k b hb with h | h | ⟨m, hm, h | h⟩ | h <;>
    (rw [h] at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem disj_Q_R (k : ℕ) (a b : GInt × GInt)
    (ha : a ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
        ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
      edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne))
    (hb : b ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
        ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++
          [Unit4.negI])) : a ≠ b := by
  intro heq
  rcases List.mem_append.1 ha with ha | ha
  · rcases seg2_cases k a ha with h | h | ⟨m, hm, h | h⟩ | h <;>
      rcases seg4_cases k b hb with h' | h' | ⟨n, hn, h' | h'⟩ | h' <;>
      (rw [h, h'] at heq; simp only [Prod.mk.injEq] at heq; omega)
  · obtain ⟨m, hm, h⟩ := seg3_cases k a ha
    rcases seg4_cases k b hb with h' | h' | ⟨n, hn, h' | h'⟩ | h' <;>
      (rw [h, h'] at heq; simp only [Prod.mk.injEq] at heq; omega)

/-- The arcs `X, Y, Z` of a walk, pairwise disjoint and each without repetitions, give a walk without repetitions. -/
theorem nodup_arcs {α : Type} {X Y Z : List α} (hX : X.Nodup) (hY : Y.Nodup) (hZ : Z.Nodup)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a ≠ b) (hXZ : ∀ a ∈ X, ∀ b ∈ Z, a ≠ b) (hYZ : ∀ a ∈ Y, ∀ b ∈ Z, a ≠ b) :
    (X ++ (Y ++ Z)).Nodup := by
  rw [List.nodup_append]
  refine ⟨hX, List.nodup_append.2 ⟨hY, hZ, hYZ⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hXY a ha b hb
  · exact hXZ a ha b hb

theorem stairWord_nodup (k : ℕ) : (edgesFrom (0, 0) (stairWord k)).Nodup := by
  rw [stairWord_edges k]
  refine nodup_arcs ?_ ?_ ?_ ?_ ?_ ?_
  · exact edgesFrom_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  · have h := edgesFrom_nodup_pos _ (2 * (k : ℤ) + 3, 0) (letters_W2C k)
    rw [edgesFrom_append, sum_w2_stair, start_p3] at h
    exact h
  · exact edgesFrom_nodup_neg _ _ (letters_W4 k)
  · intro a ha b hb
    exact disj_P_Q k a b ha hb
  · intro a ha b hb
    exact disj_P_R k a b ha hb
  · intro a ha b hb
    exact disj_Q_R k a b ha hb

theorem stairWord_sum (k : ℕ) : F2Word.sum (stairWord k) = 0 := by
  simp only [stairWord, f2sum_append, sum_rep_one, sum_rep_negOne, sum_flat_negOne_i, sum_flat_one_negI]
  apply Prod.ext <;> simp [F2Word.sum, Unit4.vec] <;> ring

/-- The reciprocal staircase tile: `stairWord k` is a boundary word of its cell set, at `(0,0)`. -/
theorem stairWord_boundary (k : ℕ) :
    IsBoundaryWordAt (stairCells (2 * (k : ℤ) + 3)) (0, 0) (stairWord k) := by
  have hd : (3 : ℤ) ≤ 2 * (k : ℤ) + 3 := by omega
  refine ⟨stairCells_lowerLeft _ hd, stairWord_sum k, ?_, ?_⟩
  · rw [zip_walk_eq]
    exact stairWord_nodup k
  · rw [zip_walk_eq]
    ext e
    rw [List.mem_toFinset, mem_boundaryEdges_iff_shape]
    exact ⟨fun h => stair_walk_sub k e h, fun h => stair_bdry_sub k e h⟩

/-! ### Admissibility of the base words -/

theorem flat_shift (m : ℕ) :
    (List.replicate m [Unit4.one, Unit4.i]).flatten ++ [Unit4.one] =
      Unit4.one :: (List.replicate m [Unit4.i, Unit4.one]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]
    simp [List.replicate_succ, List.flatten_cons]

theorem flat_reverse (m : ℕ) :
    ((List.replicate m [Unit4.i, Unit4.one]).flatten).reverse = (List.replicate m [Unit4.one, Unit4.i]).flatten := by
  simp [List.reverse_flatten, List.map_replicate, List.reverse_replicate]

theorem admissible_pal (m : ℕ) :
    Admissible ([Unit4.one, Unit4.one] ++ (List.replicate m [Unit4.i, Unit4.one]).flatten ++ [Unit4.one]) := by
  unfold Admissible
  refine ⟨?_, ?_, ?_, Or.inl ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · rcases List.mem_append.1 h with h | h
      · simp at h; exact Or.inl h
      · rcases mem_flat_pair _ _ _ x h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
    · simp at h; exact Or.inl h
  · simp
  · rw [List.getLast?_append]
    simp
  · have hs := flat_shift m
    have hr := flat_reverse m
    have h2 : (List.replicate m [Unit4.one, Unit4.i]).flatten ++ [Unit4.one, Unit4.one] =
        Unit4.one :: ((List.replicate m [Unit4.i, Unit4.one]).flatten ++ [Unit4.one]) := by
      rw [show [Unit4.one, Unit4.one] = [Unit4.one] ++ [Unit4.one] from rfl, ← List.append_assoc, hs]
      simp
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, hr,
      List.append_assoc, List.cons_append]
    rw [h2]

theorem admissible_rep_one (n : ℕ) (hn : 0 < n) : Admissible (List.replicate n Unit4.one) := by
  unfold Admissible
  refine ⟨?_, ?_, ?_, Or.inl ?_⟩
  · intro x hx
    exact Or.inl (List.eq_of_mem_replicate hx)
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [List.replicate_succ]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [List.replicate_succ']
  · simp [List.reverse_replicate]

/-- The lattice `L'(n/d)` of the paper: `L(n,d)` when `n + d` is even, and `2ℤ v₁ + ℤ v₂` when `n + d` is odd, for
`v₁ = (d, n)` and `v₂ = (n - d, n + d)`. -/
def paperLattice (n d : ℤ) : Set GInt :=
  if (n + d) % 2 = 0 then latticeOf (d, n) (n - d, n + d) else latticeOf (2 * d, 2 * n) (n - d, n + d)

theorem map_mulNegI_flat (m : ℕ) :
    ((List.replicate m [Unit4.negOne, Unit4.i]).flatten).map Unit4.mulNegI =
      (List.replicate m [Unit4.i, Unit4.one]).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.map_append, ih]
    simp [Unit4.mulNegI, Unit4.mulI]

theorem stair_W2_mulNegI (k : ℕ) :
    ((gV (stairV k))).map Unit4.mulNegI =
      [Unit4.one, Unit4.one] ++ (List.replicate (2 * k + 1) [Unit4.i, Unit4.one]).flatten ++ [Unit4.one] := by
  rw [gV_stair]
  simp only [List.map_append, List.map_cons, List.map_nil, map_mulNegI_flat]
  simp [Unit4.mulNegI, Unit4.mulI]

theorem stair_admissible (k : ℕ) :
    Admissible (gH (stairH k)) ∧ Admissible ((gV (stairV k)).map Unit4.mulNegI) := by
  rw [gH_stairH, stair_W2_mulNegI]
  exact ⟨admissible_rep_one _ (by omega), admissible_pal _⟩

/-! ### The lattice of the stair base tile -/

theorem almostV1_stair (k : ℕ) : almostV₁ (gH (stairH k)) = ((2 * (k : ℤ) + 3), 1) := by
  rw [almostV₁, gH_stairH, sum_rep_one, gI]
  simp

theorem almostV2_stair (k : ℕ) :
    almostV₂ (gV (stairV k)) = (1 - (2 * (k : ℤ) + 3), 1 + (2 * (k : ℤ) + 3)) := by
  rw [almostV₂, gV_stair, sum_w2_stair, gOne]
  simp [Prod.ext_iff]
  constructor <;> ring

theorem stair_lattice (k : ℕ) :
    latticeOf (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) = paperLattice 1 (2 * (k : ℤ) + 3) := by
  rw [almostV1_stair, almostV2_stair, paperLattice, if_pos (by omega)]

/-! ### The explicit G-words of the ladder family: `ladderH (m+1)` and `ladderV (m+1)`, so `d = 2m + 4` -/

theorem flat_key (m : ℕ) (t : ZTile) (T : List ZTile) :
    (((List.replicate (m + 1) ZTile.zero ++ t :: T).zip (List.replicate m ZTile.zero ++ t :: T)).flatMap
      fun ab => gPair ab.1 ab.2) =
      (List.replicate m [Unit4.one, Unit4.one]).flatten ++ gPair ZTile.zero t ++
        (((t :: T).zip T).flatMap fun ab => gPair ab.1 ab.2) := by
  induction m with
  | zero => simp [List.replicate_succ]
  | succ m ih =>
    have e : (List.replicate (m + 1 + 1) ZTile.zero ++ t :: T).zip (List.replicate (m + 1) ZTile.zero ++ t :: T) =
        (ZTile.zero, ZTile.zero) :: (List.replicate (m + 1) ZTile.zero ++ t :: T).zip
          (List.replicate m ZTile.zero ++ t :: T) := by
      simp [List.replicate_succ]
    rw [e, List.flatMap_cons, ih]
    simp [gPair, List.replicate_succ, List.append_assoc]

theorem gH_ladderH_computed (m : ℕ) :
    gH (ladderH (m + 1)) = [Unit4.one, Unit4.one] ++ (List.replicate (2 * m) Unit4.one ++
      ([Unit4.one, Unit4.i] ++ ([Unit4.one, Unit4.one] ++ (List.replicate (2 * (m + 1)) Unit4.one ++ [Unit4.one])))) := by
  simp only [gH, tileSeq_ladderH, List.tail_cons]
  have e : (ZTile.one :: (List.replicate (m + 1) ZTile.zero ++ ZTile.one :: List.replicate (m + 2) ZTile.zero)).zip
      (List.replicate (m + 1) ZTile.zero ++ ZTile.one :: List.replicate (m + 2) ZTile.zero) =
      (ZTile.one, ZTile.zero) :: (List.replicate (m + 1) ZTile.zero ++ ZTile.one :: List.replicate (m + 2) ZTile.zero).zip
        (List.replicate m ZTile.zero ++ ZTile.one :: List.replicate (m + 2) ZTile.zero) := by
    simp [List.replicate_succ]
  have e2 : (ZTile.one :: List.replicate (m + 2) ZTile.zero).zip (List.replicate (m + 2) ZTile.zero) =
      (ZTile.one, ZTile.zero) :: (List.replicate (m + 1 + 1) ZTile.zero).zip (List.replicate (m + 1) ZTile.zero) := by
    simp [List.replicate_succ]
  rw [e, List.flatMap_cons, flat_key m ZTile.one (List.replicate (m + 2) ZTile.zero), e2, List.flatMap_cons,
    flat_zero (m + 1), flat_ones m, flat_ones (m + 1)]
  simp only [gPair, List.append_assoc, List.cons_append, List.nil_append]

/-- A list of `1`s is a replicate of its length. -/
theorem ones_eq_rep (L : F2Word) (n : ℕ) (hn : L.length = n) (hL : ∀ x ∈ L, x = Unit4.one) :
    L = List.replicate n Unit4.one :=
  List.eq_replicate_iff.2 ⟨hn, hL⟩

theorem gH_ladderH (m : ℕ) :
    gH (ladderH (m + 1)) = List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one := by
  have h1 : ([Unit4.one, Unit4.one] ++ (List.replicate (2 * m) Unit4.one ++ [Unit4.one])) =
      List.replicate (2 * m + 3) Unit4.one := by
    apply ones_eq_rep
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
      omega
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · simp at h; exact h
      · rcases List.mem_append.1 h with h | h
        · exact List.eq_of_mem_replicate h
        · simp at h; exact h
  have h2 : ([Unit4.one, Unit4.one] ++ (List.replicate (2 * (m + 1)) Unit4.one ++ [Unit4.one])) =
      List.replicate (2 * m + 5) Unit4.one := by
    apply ones_eq_rep
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
      omega
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · simp at h; exact h
      · rcases List.mem_append.1 h with h | h
        · exact List.eq_of_mem_replicate h
        · simp at h; exact h
  rw [gH_ladderH_computed, ← h1, ← h2]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem gH_ladder_flip (m : ℕ) :
    gH (flipW (ladderV (m + 1))) =
      [Unit4.one, Unit4.one] ++ (List.replicate (2 * m + 1 + 1) [Unit4.i, Unit4.one]).flatten ++ [Unit4.one] := by
  have hf : flipW (ladderV (m + 1)) = List.replicate (2 * m + 1 + 1 + 1) Letter.q ++ [Letter.p] := by
    simp only [ladderV, flipW, flipLetter, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
    congr 2
  rw [hf]
  simp only [gH, tileSeq_flip, List.tail_cons]
  have e : (ZTile.one :: (List.replicate (2 * m + 1 + 1) ZTile.oneD ++ [ZTile.zero])).zip
      (List.replicate (2 * m + 1 + 1) ZTile.oneD ++ [ZTile.zero]) =
      (ZTile.one, ZTile.oneD) :: ((List.replicate (2 * m + 1 + 1) ZTile.oneD ++ [ZTile.zero]).zip
        (List.replicate (2 * m + 1) ZTile.oneD ++ [ZTile.zero])) := by
    simp [List.replicate_succ]
  rw [e, List.flatMap_cons, flat_oneD (2 * m + 1)]
  simp [gPair]

theorem gV_ladder (m : ℕ) :
    gV (ladderV (m + 1)) = [Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i] := by
  unfold gV
  rw [gH_ladder_flip]
  simp [List.map_flatten, List.map_replicate, Unit4.mulI, List.map_append]

/-- The boundary word of the ladder base tile, written out: `w₁ w₂ \widehat{rev w₁} \widehat{rev w₂}`. -/
def ladderWord (m : ℕ) : F2Word :=
  List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one ++
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) ++
    (List.replicate (2 * m + 3) Unit4.negOne ++ [Unit4.negI] ++ List.replicate (2 * m + 5) Unit4.negOne) ++
    ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])

theorem pseudoBoundaryWord_ladder (m : ℕ) :
    pseudoBoundaryWord (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).1
      (gPseudo (ladderH (m + 1)) (ladderV (m + 1))).2 = ladderWord m := by
  simp [gPseudo, pseudoBoundaryWord, gH_ladderH, gV_ladder, ladderWord, hat_rev_eq_map_neg, List.map_flatten,
    List.map_replicate, List.map_append, Unit4.neg, List.append_assoc]

/-! ### The cell set of the ladder base tile `paperLadderTile d`, `d = 2m + 4` -/

/-- The lower-left corners of the cells of the ladder tile: the C-strip cells whose four corners avoid the removed
rows, and the two corner cells `(0,0)` and `(d+1,d+1)`. -/
def ladderInT (d a b : ℤ) : Prop :=
  ((-d + 2 ≤ a ∧ a ≤ 2 * d - 1 ∧ 0 ≤ b ∧ b ≤ d + 1 ∧ 1 ≤ a + b ∧ a + b ≤ 2 * d + 1) ∧
      (b ≠ 0 ∨ a ≤ d - 2) ∧ (b ≠ d + 1 ∨ 3 ≤ a)) ∨
    (a = 0 ∧ b = 0) ∨ (a = d + 1 ∧ b = d + 1)

instance (d a b : ℤ) : Decidable (ladderInT d a b) := by
  unfold ladderInT
  infer_instance

def ladderCells (d : ℤ) : CellTile :=
  ((Finset.Icc (-d + 2) (2 * d)) ×ˢ (Finset.Icc 0 (d + 1))).filter fun x => ladderInT d x.1 x.2

theorem mem_ladderCells (d : ℤ) (hd : 4 ≤ d) (x : GInt) : x ∈ ladderCells d ↔ ladderInT d x.1 x.2 := by
  unfold ladderCells
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> (unfold ladderInT at h; omega)

/-- A cell `(a,b)` with `x` among its corners. -/
theorem cell_of (d : ℤ) (x : GInt) (a b : ℤ) (hcell : ladderInT d a b)
    (hx : (x.1 = a ∧ x.2 = b) ∨ (x.1 = a + 1 ∧ x.2 = b) ∨ (x.1 = a ∧ x.2 = b + 1) ∨ (x.1 = a + 1 ∧ x.2 = b + 1)) :
    ∃ c : GInt, ladderInT d c.1 c.2 ∧ x ∈ cellCorners c :=
  ⟨(a, b), hcell, (mem_cellCorners_iff _ _).2 hx⟩

/-- Every point of the ladder tile is a corner of a cell of the ladder cell set, by an explicit choice of the cell. -/
theorem ladderTile_cover (d : ℤ) (hd : 4 ≤ d) (x : GInt) (hx : x ∈ paperLadderTile d) :
    ∃ c : GInt, ladderInT d c.1 c.2 ∧ x ∈ cellCorners c := by
  have hx' := hx
  simp only [paperLadderTile, paperLadderA, paperLadderB, paperLadderC, paperLadderD, Set.mem_sdiff,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hx'
  obtain ⟨hU, hD⟩ := hx'
  rcases hU with ((hA | hA) | hB) | hC
  · exact cell_of d x 0 0 (by unfold ladderInT; omega) (by omega)
  · exact cell_of d x (d + 1) (d + 1) (by unfold ladderInT; omega) (by omega)
  · exact cell_of d x x.1 x.2 (by unfold ladderInT; omega) (by omega)
  by_cases hq0 : x.2 = 0
  · by_cases hp : x.1 ≤ d - 2
    · exact cell_of d x x.1 x.2 (by unfold ladderInT; omega) (by omega)
    · exact cell_of d x (x.1 - 1) x.2 (by unfold ladderInT; omega) (by omega)
  by_cases hq2 : x.2 = d + 2
  · by_cases hp : x.1 ≤ d
    · exact cell_of d x x.1 (x.2 - 1) (by unfold ladderInT; omega) (by omega)
    · exact cell_of d x (x.1 - 1) (x.2 - 1) (by unfold ladderInT; omega) (by omega)
  by_cases hs : 2 * d + 2 ≤ x.1 + x.2
  · exact cell_of d x (x.1 - 1) (x.2 - 1) (by unfold ladderInT; omega) (by omega)
  by_cases hp : x.1 ≤ 2 * d - 1
  · by_cases hq : x.2 = d + 1
    · by_cases hp3 : 3 ≤ x.1
      · exact cell_of d x x.1 x.2 (by unfold ladderInT; omega) (by omega)
      · exact cell_of d x x.1 (x.2 - 1) (by unfold ladderInT; omega) (by omega)
    · exact cell_of d x x.1 x.2 (by unfold ladderInT; omega) (by omega)
  · exact cell_of d x (x.1 - 1) x.2 (by unfold ladderInT; omega) (by omega)

theorem mem_ladderVertices (d : ℤ) (hd : 4 ≤ d) (x : GInt) :
    x ∈ (ladderCells d).vertices ↔ x ∈ paperLadderTile d := by
  constructor
  · intro hx
    simp only [CellTile.vertices, Finset.mem_biUnion] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    rw [mem_ladderCells d hd] at hc
    rw [mem_cellCorners_iff] at hxc
    simp only [paperLadderTile, paperLadderA, paperLadderB, paperLadderC, paperLadderD, Set.mem_sdiff,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff]
    unfold ladderInT at hc
    omega
  · intro hx
    obtain ⟨c, hc, hxc⟩ := ladderTile_cover d hd x hx
    simp only [CellTile.vertices, Finset.mem_biUnion]
    exact ⟨c, (mem_ladderCells d hd c).2 hc, hxc⟩

theorem ladderCells_lowerLeft (d : ℤ) (hd : 4 ≤ d) : IsLowerLeft (ladderCells d) (0, 0) := by
  refine ⟨(mem_ladderVertices d hd _).2 ?_, ?_⟩
  · refine (Set.mem_sdiff _).2 ⟨Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_insert _ _)), ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> dsimp only at h1 h2 <;> omega
  · intro v hv
    rw [mem_ladderVertices d hd] at hv
    simp only [paperLadderTile, paperLadderA, paperLadderB, paperLadderC, paperLadderD, Set.mem_sdiff,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, Prod.ext_iff] at hv
    constructor
    · omega
    · intro h
      omega

/-! ### The walk of the ladder boundary word, in blocks -/

theorem edgesFrom_append' (c d : GInt) (u v : F2Word) (h : d = c + F2Word.sum u) :
    edgesFrom c (u ++ v) = edgesFrom c u ++ edgesFrom d v := by
  subst h
  exact edgesFrom_append c u v

theorem sum_single_i : F2Word.sum [Unit4.i] = (0, 1) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_single_negI : F2Word.sum [Unit4.negI] = (0, -1) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_ii : F2Word.sum [Unit4.i, Unit4.i] = (0, 2) := by
  simp [F2Word.sum, Unit4.vec]

theorem sum_negI_negI : F2Word.sum [Unit4.negI, Unit4.negI] = (0, -2) := by
  simp [F2Word.sum, Unit4.vec]

/-- The ladder boundary word split as `A i B Q (A' (-i) B') S`, with the walk blocks in the order of the walk. -/
theorem ladderWord_hw (m : ℕ) :
    ladderWord m = List.replicate (2 * m + 3) Unit4.one ++
      ([Unit4.i] ++ (List.replicate (2 * m + 5) Unit4.one ++
        (([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] ++
            List.replicate (2 * m + 3) Unit4.negOne) ++
          ([Unit4.negI] ++ (List.replicate (2 * m + 5) Unit4.negOne ++
            ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
              [Unit4.negI])))))) := by
  simp only [ladderWord, List.append_assoc, List.cons_append, List.nil_append]

theorem ladderWord_edges (m : ℕ) :
    edgesFrom (0, 0) (ladderWord m) =
      edgesFrom (0, 0) (List.replicate (2 * m + 3) Unit4.one) ++
      (edgesFrom (2 * (m : ℤ) + 3, 0) [Unit4.i] ++
      (edgesFrom (2 * (m : ℤ) + 3, 1) (List.replicate (2 * m + 5) Unit4.one) ++
      (edgesFrom (4 * (m : ℤ) + 8, 1)
          ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] ++
            List.replicate (2 * m + 3) Unit4.negOne) ++
      (edgesFrom (3, 2 * (m : ℤ) + 6) [Unit4.negI] ++
      (edgesFrom (3, 2 * (m : ℤ) + 5) (List.replicate (2 * m + 5) Unit4.negOne) ++
      edgesFrom (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5)
          ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
            [Unit4.negI])))))) := by
  rw [ladderWord_hw]
  rw [edgesFrom_append' _ (2 * (m : ℤ) + 3, 0) _ _
    (by simp only [sum_rep_one]; ext <;> simp)]
  rw [edgesFrom_append' _ (2 * (m : ℤ) + 3, 1) _ _
    (by simp only [sum_single_i]; ext <;> simp)]
  rw [edgesFrom_append' (2 * (m : ℤ) + 3, 1) (4 * (m : ℤ) + 8, 1) (List.replicate (2 * m + 5) Unit4.one) _
    (by simp only [sum_rep_one]; ext <;> simp; ring)]
  rw [edgesFrom_append' (4 * (m : ℤ) + 8, 1) (3, 2 * (m : ℤ) + 6)
    ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] ++
      List.replicate (2 * m + 3) Unit4.negOne) _
    (by
      simp only [f2sum_append, sum_ii, sum_flat_negOne_i, sum_single_i, sum_rep_negOne]
      ext <;> simp <;> ring)]
  rw [edgesFrom_append' (3, 2 * (m : ℤ) + 6) (3, 2 * (m : ℤ) + 5) [Unit4.negI] _
    (by simp only [sum_single_negI]; ext <;> simp; ring)]
  rw [edgesFrom_append' (3, 2 * (m : ℤ) + 5) (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5)
    (List.replicate (2 * m + 5) Unit4.negOne) _
    (by simp only [sum_rep_negOne]; ext <;> simp; ring)]

/-! ### Boundary shapes of the ladder cell tile -/

theorem mem_ladderCells' (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) : ((a, b) : GInt) ∈ ladderCells d ↔ ladderInT d a b :=
  mem_ladderCells d hd (a, b)

theorem ladder_N_cases (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) (h : ladderInT d (a - 1) b ∧ ¬ladderInT d a b) :
    (b = 0 ∧ a = d - 1) ∨ (b = 1 ∧ a = 2 * d) ∨ (2 ≤ b ∧ b ≤ d ∧ a = 2 * d + 2 - b) ∨ (b = d + 1 ∧ a = d + 2) := by
  obtain ⟨h1, h2⟩ := h
  unfold ladderInT at h1 h2
  omega

theorem ladder_S_cases (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) (h : ladderInT d a b ∧ ¬ladderInT d (a - 1) b) :
    (b = 0 ∧ a = 0) ∨ (1 ≤ b ∧ b ≤ d - 1 ∧ a = 1 - b) ∨ (b = d ∧ a = 2 - d) ∨ (b = d + 1 ∧ a = 3) := by
  obtain ⟨h1, h2⟩ := h
  unfold ladderInT at h1 h2
  omega

theorem ladder_E_cases (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) (h : ladderInT d a b ∧ ¬ladderInT d a (b - 1)) :
    (b = 0 ∧ 0 ≤ a ∧ a ≤ d - 2) ∨ (b = 1 ∧ d - 1 ≤ a ∧ a ≤ 2 * d - 1) ∨ (2 ≤ b ∧ b ≤ d - 1 ∧ a = 1 - b) := by
  obtain ⟨h1, h2⟩ := h
  unfold ladderInT at h1 h2
  omega

theorem ladder_W_cases (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) (h : ladderInT d a b ∧ ¬ladderInT d a (b + 1)) :
    (2 ≤ b ∧ b ≤ d - 1 ∧ a = 2 * d + 1 - b) ∨ (b = d ∧ 2 - d ≤ a ∧ a ≤ 2) ∨ (b = d + 1 ∧ 3 ≤ a ∧ a ≤ d + 1) := by
  obtain ⟨h1, h2⟩ := h
  unfold ladderInT at h1 h2
  omega

/-! ### The edges of the upper block `Q` of the ladder walk, from `(4m+8, 1)` -/

theorem ladderQ_cases (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (4 * (m : ℤ) + 8, 1)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i])) :
    e = ((4 * (m : ℤ) + 8, 1), (4 * (m : ℤ) + 8, 2)) ∨ e = ((4 * (m : ℤ) + 8, 2), (4 * (m : ℤ) + 8, 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (e = ((4 * (m : ℤ) + 8 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ))) ∨
          e = ((4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 4 + (j : ℤ))))) ∨
      e = ((2 * (m : ℤ) + 6, 2 * (m : ℤ) + 5), (2 * (m : ℤ) + 6, 2 * (m : ℤ) + 6)) := by
  have hW : [Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] =
      Unit4.i :: Unit4.i :: ((List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_negOne_i] at h
  rcases h with h | h | ⟨j, hj, h⟩ | h
  · left
    rw [h]
    simp [Unit4.vec]
  · right; left
    rw [h]
    simp [Unit4.vec]
  · right; right; left
    refine ⟨j, hj, ?_⟩
    rcases h with h | h
    · left
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
    · right
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; right
    simp only [edgesFrom, List.mem_singleton] at h
    rw [h, sum_flat_negOne_i]
    simp [Unit4.vec, Prod.ext_iff]; omega


theorem mem_single_i (c : GInt) (e : GInt × GInt) : e ∈ edgesFrom c [Unit4.i] ↔ e = (c, c + Unit4.vec Unit4.i) := by
  simp [edgesFrom]

theorem mem_single_negI (c : GInt) (e : GInt × GInt) :
    e ∈ edgesFrom c [Unit4.negI] ↔ e = (c, c + Unit4.vec Unit4.negI) := by
  simp [edgesFrom]

theorem start_A' (m : ℕ) :
    ((4 * (m : ℤ) + 8, 1) : GInt) + F2Word.sum ([Unit4.i, Unit4.i] ++
      (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) =
      (2 * (m : ℤ) + 6, 2 * (m : ℤ) + 6) := by
  simp only [f2sum_append, sum_ii, sum_flat_negOne_i, sum_single_i]
  ext <;> simp <;> ring

/-- The edges of the lower-left block `S` of the ladder walk, from `(-2m-2, 2m+5)`. -/
theorem ladderS_cases (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4)) ∨
      e = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (e = ((-2 * (m : ℤ) - 2 + (j : ℤ), 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ))) ∨
          e = ((-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 2 - (j : ℤ))))) ∨
      e = ((0, 1), (0, 0)) := by
  have hW : [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI] = Unit4.negI :: Unit4.negI :: ((List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
        [Unit4.negI]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_one_negI] at h
  rcases h with h | h | ⟨j, hj, h⟩ | h
  · left
    rw [h]
    simp [Unit4.vec, Prod.ext_iff]; omega
  · right; left
    rw [h]
    simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; left
    refine ⟨j, hj, ?_⟩
    rcases h with h | h
    · left
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
    · right
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; right
    simp only [edgesFrom, List.mem_singleton] at h
    rw [h, sum_flat_one_negI]
    simp [Unit4.vec, Prod.ext_iff]; omega

/-- The upper block `Q` and the top-left block `A'`, backwards: the forms of the upper block are edges of the walk. -/
theorem ladderQ_mem (m : ℕ) (e : GInt × GInt)
    (h : e = ((4 * (m : ℤ) + 8, 1), (4 * (m : ℤ) + 8, 2)) ∨ e = ((4 * (m : ℤ) + 8, 2), (4 * (m : ℤ) + 8, 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (e = ((4 * (m : ℤ) + 8 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ))) ∨
          e = ((4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 4 + (j : ℤ))))) ∨
      e = ((2 * (m : ℤ) + 6, 2 * (m : ℤ) + 5), (2 * (m : ℤ) + 6, 2 * (m : ℤ) + 6))) :
    e ∈ edgesFrom (4 * (m : ℤ) + 8, 1)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
  have hW : [Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] =
      Unit4.i :: Unit4.i :: ((List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_negOne_i]
  rcases h with h | h | ⟨j, hj, h⟩ | h
  · left
    rw [h]
    simp [Unit4.vec]
  · right; left
    rw [h]
    simp [Unit4.vec]
  · right; right; left
    refine ⟨j, hj, ?_⟩
    rcases h with h | h
    · left
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
    · right
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; right
    rw [mem_single_i, sum_flat_negOne_i, h]
    simp [Unit4.vec, Prod.ext_iff]; omega

theorem ladderS_mem (m : ℕ) (e : GInt × GInt)
    (h : e = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4)) ∨
      e = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (e = ((-2 * (m : ℤ) - 2 + (j : ℤ), 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ))) ∨
          e = ((-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 2 - (j : ℤ))))) ∨
      e = ((0, 1), (0, 0))) :
    e ∈ edgesFrom (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI]) := by
  have hW : [Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
      [Unit4.negI] = Unit4.negI :: Unit4.negI :: ((List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++
        [Unit4.negI]) := by
    simp
  rw [hW, edgesFrom, edgesFrom, List.mem_cons, List.mem_cons, edgesFrom_append, List.mem_append,
    mem_edgesFrom_one_negI]
  rcases h with h | h | ⟨j, hj, h⟩ | h
  · left
    rw [h]
    simp [Unit4.vec, Prod.ext_iff]; omega
  · right; left
    rw [h]
    simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; left
    refine ⟨j, hj, ?_⟩
    rcases h with h | h
    · left
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
    · right
      rw [h]
      simp [Unit4.vec, Prod.ext_iff]; omega
  · right; right; right
    rw [mem_single_negI, sum_flat_one_negI, h]
    simp [Unit4.vec, Prod.ext_iff]; omega

/-! ### Boundary shapes from explicit edges of the ladder -/

theorem bshape_N (d : ℤ) (hd : 4 ≤ d) (e : GInt × GInt) (a b : ℤ) (he : e = ((a, b), (a, b + 1)))
    (h1 : ladderInT d (a - 1) b) (h2 : ¬ ladderInT d a b) : BShape (ladderCells d) e :=
  ⟨a, b, Or.inl ⟨he, (mem_ladderCells' d hd (a - 1) b).2 h1, fun h => h2 ((mem_ladderCells' d hd a b).1 h)⟩⟩

theorem bshape_S (d : ℤ) (hd : 4 ≤ d) (e : GInt × GInt) (a b : ℤ) (he : e = ((a, b + 1), (a, b)))
    (h1 : ladderInT d a b) (h2 : ¬ ladderInT d (a - 1) b) : BShape (ladderCells d) e :=
  ⟨a, b, Or.inr (Or.inl ⟨he, (mem_ladderCells' d hd a b).2 h1, fun h => h2 ((mem_ladderCells' d hd (a - 1) b).1 h)⟩)⟩

theorem bshape_E (d : ℤ) (hd : 4 ≤ d) (e : GInt × GInt) (a b : ℤ) (he : e = ((a, b), (a + 1, b)))
    (h1 : ladderInT d a b) (h2 : ¬ ladderInT d a (b - 1)) : BShape (ladderCells d) e :=
  ⟨a, b, Or.inr (Or.inr (Or.inl ⟨he, (mem_ladderCells' d hd a b).2 h1,
    fun h => h2 ((mem_ladderCells' d hd a (b - 1)).1 h)⟩))⟩

theorem bshape_W (d : ℤ) (hd : 4 ≤ d) (e : GInt × GInt) (a b : ℤ) (he : e = ((a + 1, b + 1), (a, b + 1)))
    (h1 : ladderInT d a b) (h2 : ¬ ladderInT d a (b + 1)) : BShape (ladderCells d) e :=
  ⟨a, b, Or.inr (Or.inr (Or.inr ⟨he, (mem_ladderCells' d hd a b).2 h1,
    fun h => h2 ((mem_ladderCells' d hd a (b + 1)).1 h)⟩))⟩

/-! ### The blocks of the ladder walk, inside the walk -/

theorem walk_X1 (m : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (0, 0) (List.replicate (2 * m + 3) Unit4.one)) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inl h

theorem walk_X2 (m : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (2 * (m : ℤ) + 3, 0) [Unit4.i]) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inl h)

theorem walk_X3 (m : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (2 * (m : ℤ) + 3, 1) (List.replicate (2 * m + 5) Unit4.one)) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inl h))

theorem mem_X4_of_Q (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (4 * (m : ℤ) + 8, 1)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i])) :
    e ∈ edgesFrom (4 * (m : ℤ) + 8, 1) ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i] ++ List.replicate (2 * m + 3) Unit4.negOne) := by
  rw [edgesFrom_append]
  exact List.mem_append_left _ h

theorem mem_X4_of_A (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (2 * (m : ℤ) + 6, 2 * (m : ℤ) + 6) (List.replicate (2 * m + 3) Unit4.negOne)) :
    e ∈ edgesFrom (4 * (m : ℤ) + 8, 1) ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i] ++ List.replicate (2 * m + 3) Unit4.negOne) := by
  rw [edgesFrom_append]
  refine List.mem_append_right _ ?_
  rw [start_A']
  exact h

theorem walk_X4 (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (4 * (m : ℤ) + 8, 1) ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++
      [Unit4.i] ++ List.replicate (2 * m + 3) Unit4.negOne)) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem walk_X5 (m : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (3, 2 * (m : ℤ) + 6) [Unit4.negI]) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem walk_X6 (m : ℕ) (e : GInt × GInt) (h : e ∈ edgesFrom (3, 2 * (m : ℤ) + 5) (List.replicate (2 * m + 5) Unit4.negOne)) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem walk_X7 (m : ℕ) (e : GInt × GInt)
    (h : e ∈ edgesFrom (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  rw [ladderWord_edges]
  simp only [List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-! ### The walk of the ladder tile lies on its boundary -/

theorem ladder_walk_sub (m : ℕ) (e : GInt × GInt) (he : e ∈ edgesFrom (0, 0) (ladderWord m)) :
    BShape (ladderCells (2 * (m : ℤ) + 4)) e := by
  have hd : (4 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  rw [ladderWord_edges] at he
  simp only [List.mem_append] at he
  rcases he with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · obtain ⟨j, hj, h⟩ := (mem_edgesFrom_one _ _ _).1 h1
    exact bshape_E _ hd e j 0 (by rw [h]; simp) (by unfold ladderInT; omega) (by unfold ladderInT; omega)
  · rw [mem_single_i] at h2
    exact bshape_N _ hd e (2 * (m : ℤ) + 3) 0 (by rw [h2]; simp [Unit4.vec])
      (by unfold ladderInT; omega) (by unfold ladderInT; omega)
  · obtain ⟨j, hj, h⟩ := (mem_edgesFrom_one _ _ _).1 h3
    exact bshape_E _ hd e (2 * (m : ℤ) + 3 + (j : ℤ)) 1 (by rw [h]) (by unfold ladderInT; omega)
      (by unfold ladderInT; omega)
  · rw [edgesFrom_append] at h4
    rcases List.mem_append.1 h4 with hQ | hA
    · rcases ladderQ_cases m e hQ with h | h | ⟨j, hj, h | h⟩ | h
      · exact bshape_N _ hd e (4 * (m : ℤ) + 8) 1 (by rw [h]; simp)
          (by unfold ladderInT; omega) (by unfold ladderInT; omega)
      · exact bshape_N _ hd e (4 * (m : ℤ) + 8) 2 (by rw [h]; simp)
          (by unfold ladderInT; omega) (by unfold ladderInT; omega)
      · exact bshape_W _ hd e (4 * (m : ℤ) + 7 - (j : ℤ)) (2 + (j : ℤ)) (by rw [h]; simp; omega)
          (by unfold ladderInT; omega) (by unfold ladderInT; omega)
      · exact bshape_N _ hd e (4 * (m : ℤ) + 7 - (j : ℤ)) (3 + (j : ℤ)) (by rw [h]; simp; omega)
          (by unfold ladderInT; omega) (by unfold ladderInT; omega)
      · exact bshape_N _ hd e (2 * (m : ℤ) + 6) (2 * (m : ℤ) + 5) (by rw [h]; simp; omega)
          (by unfold ladderInT; omega) (by unfold ladderInT; omega)
    · rw [start_A'] at hA
      obtain ⟨j, hj, h⟩ := (mem_edgesFrom_negOne _ _ _).1 hA
      exact bshape_W _ hd e (2 * (m : ℤ) + 5 - (j : ℤ)) (2 * (m : ℤ) + 5) (by rw [h]; simp; omega)
        (by unfold ladderInT; omega) (by unfold ladderInT; omega)
  · rw [mem_single_negI] at h5
    exact bshape_S _ hd e 3 (2 * (m : ℤ) + 5) (by rw [h5]; simp [Unit4.vec]; omega)
      (by unfold ladderInT; omega) (by unfold ladderInT; omega)
  · obtain ⟨j, hj, h⟩ := (mem_edgesFrom_negOne _ _ _).1 h6
    exact bshape_W _ hd e (2 - (j : ℤ)) (2 * (m : ℤ) + 4) (by rw [h]; simp; omega)
      (by unfold ladderInT; omega) (by unfold ladderInT; omega)
  · rcases ladderS_cases m e h7 with h | h | ⟨j, hj, h | h⟩ | h
    · exact bshape_S _ hd e (-2 * (m : ℤ) - 2) (2 * (m : ℤ) + 4) (by rw [h]; simp; omega)
        (by unfold ladderInT; omega) (by unfold ladderInT; omega)
    · exact bshape_S _ hd e (-2 * (m : ℤ) - 2) (2 * (m : ℤ) + 3) (by rw [h]; simp; omega)
        (by unfold ladderInT; omega) (by unfold ladderInT; omega)
    · exact bshape_E _ hd e (-2 * (m : ℤ) - 2 + (j : ℤ)) (2 * (m : ℤ) + 3 - (j : ℤ)) (by rw [h])
        (by unfold ladderInT; omega) (by unfold ladderInT; omega)
    · exact bshape_S _ hd e (-2 * (m : ℤ) - 1 + (j : ℤ)) (2 * (m : ℤ) + 2 - (j : ℤ)) (by rw [h]; simp; omega)
        (by unfold ladderInT; omega) (by unfold ladderInT; omega)
    · exact bshape_S _ hd e 0 0 (by rw [h]; simp) (by unfold ladderInT; omega) (by unfold ladderInT; omega)

/-- The boundary edges of the ladder cell tile are edges of its walk. -/
theorem ladder_bdry_sub (m : ℕ) (e : GInt × GInt) (h : BShape (ladderCells (2 * (m : ℤ) + 4)) e) :
    e ∈ edgesFrom (0, 0) (ladderWord m) := by
  have hd : (4 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  obtain ⟨a, b, hs⟩ := h
  rcases hs with ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2⟩
  · -- north edges
    rw [mem_ladderCells' _ hd] at h1 h2
    rcases ladder_N_cases _ hd a b ⟨h1, h2⟩ with ⟨hb, ha⟩ | ⟨hb, ha⟩ | ⟨hb1, hb2, ha⟩ | ⟨hb, ha⟩
    · subst hb
      subst ha
      exact walk_X2 m e ((mem_single_i _ _).2 (by rw [he]; simp [Unit4.vec]; omega))
    · subst hb
      subst ha
      exact walk_X4 m e (mem_X4_of_Q m e (ladderQ_mem m e (Or.inl (by rw [he]; simp; omega))))
    · by_cases hb2' : b = 2
      · subst hb2'
        subst ha
        exact walk_X4 m e (mem_X4_of_Q m e (ladderQ_mem m e (Or.inr (Or.inl (by rw [he]; simp; omega)))))
      · obtain ⟨j, hj⟩ := exists_nat_of_int (b - 3) (by omega)
        have hj' : j < 2 * m + 1 + 1 := by omega
        exact walk_X4 m e (mem_X4_of_Q m e (ladderQ_mem m e
          (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inr (by rw [he]; simp; omega)⟩)))))
    · subst hb
      subst ha
      exact walk_X4 m e (mem_X4_of_Q m e (ladderQ_mem m e
        (Or.inr (Or.inr (Or.inr (by rw [he]; simp; omega))))))
  · -- south edges
    rw [mem_ladderCells' _ hd] at h1 h2
    rcases ladder_S_cases _ hd a b ⟨h1, h2⟩ with ⟨hb, ha⟩ | ⟨hb1, hb2, ha⟩ | ⟨hb, ha⟩ | ⟨hb, ha⟩
    · subst hb
      subst ha
      exact walk_X7 m e (ladderS_mem m e (Or.inr (Or.inr (Or.inr (by rw [he]; simp)))))
    · by_cases hb3 : b = 2 * (m : ℤ) + 3
      · exact walk_X7 m e (ladderS_mem m e (Or.inr (Or.inl (by rw [he]; simp; omega))))
      · obtain ⟨j, hj⟩ := exists_nat_of_int (2 * (m : ℤ) + 2 - b) (by omega)
        have hj' : j < 2 * m + 1 + 1 := by omega
        exact walk_X7 m e (ladderS_mem m e
          (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inr (by rw [he]; simp; omega)⟩))))
    · subst hb
      subst ha
      exact walk_X7 m e (ladderS_mem m e (Or.inl (by rw [he]; simp; omega)))
    · subst hb
      subst ha
      exact walk_X5 m e ((mem_single_negI _ _).2 (by rw [he]; simp [Unit4.vec]; omega))
  · -- bottom edges
    rw [mem_ladderCells' _ hd] at h1 h2
    rcases ladder_E_cases _ hd a b ⟨h1, h2⟩ with ⟨hb, ha1, ha2⟩ | ⟨hb, ha1, ha2⟩ | ⟨hb1, hb2, ha⟩
    · subst hb
      obtain ⟨j, hj⟩ := exists_nat_of_int a ha1
      exact walk_X1 m e ((mem_edgesFrom_one _ _ _).2 ⟨j, by omega, by rw [he]; simp; omega⟩)
    · subst hb
      obtain ⟨j, hj⟩ := exists_nat_of_int (a - (2 * (m : ℤ) + 3)) (by omega)
      exact walk_X3 m e ((mem_edgesFrom_one _ _ _).2 ⟨j, by omega, by rw [he]; simp; omega⟩)
    · obtain ⟨j, hj⟩ := exists_nat_of_int (2 * (m : ℤ) + 3 - b) (by omega)
      have hj' : j < 2 * m + 1 + 1 := by omega
      exact walk_X7 m e (ladderS_mem m e
        (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inl (by rw [he]; simp; omega)⟩))))
  · -- top edges
    rw [mem_ladderCells' _ hd] at h1 h2
    rcases ladder_W_cases _ hd a b ⟨h1, h2⟩ with ⟨hb1, hb2, ha⟩ | ⟨hb, ha1, ha2⟩ | ⟨hb, ha1, ha2⟩
    · obtain ⟨j, hj⟩ := exists_nat_of_int (b - 2) (by omega)
      have hj' : j < 2 * m + 1 + 1 := by omega
      exact walk_X4 m e (mem_X4_of_Q m e (ladderQ_mem m e
        (Or.inr (Or.inr (Or.inl ⟨j, hj', Or.inl (by rw [he]; simp; omega)⟩)))))
    · subst hb
      obtain ⟨j, hj⟩ := exists_nat_of_int (2 - a) (by omega)
      exact walk_X6 m e ((mem_edgesFrom_negOne _ _ _).2 ⟨j, by omega, by rw [he]; simp; omega⟩)
    · subst hb
      obtain ⟨j, hj⟩ := exists_nat_of_int (2 * (m : ℤ) + 5 - a) (by omega)
      exact walk_X4 m e (mem_X4_of_A m e ((mem_edgesFrom_negOne _ _ _).2 ⟨j, by omega, by rw [he]; simp; omega⟩))

theorem letters_Q (n k : ℕ) : ∀ x ∈ [Unit4.i, Unit4.i] ++ (List.replicate n [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] ++ List.replicate k Unit4.negOne, x = Unit4.i ∨ x = Unit4.negOne := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · simp at h; exact Or.inl h
      · rcases mem_flat_pair _ _ _ x h with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
    · simp at h; exact Or.inl h
  · exact Or.inr (List.eq_of_mem_replicate h)

theorem letters_S (n : ℕ) : ∀ x ∈ [Unit4.negI, Unit4.negI] ++ (List.replicate n [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI], x = Unit4.one ∨ x = Unit4.negI := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · simp at h; exact Or.inr h
    · rcases mem_flat_pair _ _ _ x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
  · simp at h; exact Or.inr h

abbrev ladX1 (m : ℕ) : List (GInt × GInt) := edgesFrom (0, 0) (List.replicate (2 * m + 3) Unit4.one)
abbrev ladX2 (m : ℕ) : List (GInt × GInt) := edgesFrom (2 * (m : ℤ) + 3, 0) [Unit4.i]
abbrev ladX3 (m : ℕ) : List (GInt × GInt) := edgesFrom (2 * (m : ℤ) + 3, 1) (List.replicate (2 * m + 5) Unit4.one)
abbrev ladX4 (m : ℕ) : List (GInt × GInt) :=
  edgesFrom (4 * (m : ℤ) + 8, 1) ([Unit4.i, Unit4.i] ++ (List.replicate (2 * m + 1 + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i] ++ List.replicate (2 * m + 3) Unit4.negOne)
abbrev ladX5 (m : ℕ) : List (GInt × GInt) := edgesFrom (3, 2 * (m : ℤ) + 6) [Unit4.negI]
abbrev ladX6 (m : ℕ) : List (GInt × GInt) := edgesFrom (3, 2 * (m : ℤ) + 5) (List.replicate (2 * m + 5) Unit4.negOne)
abbrev ladX7 (m : ℕ) : List (GInt × GInt) :=
  edgesFrom (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5) ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * m + 1 + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])

theorem ladF1 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX1 m) :
    ∃ j : ℕ, j < 2 * m + 3 ∧ a = (((j : ℤ), 0), ((j : ℤ) + 1, 0)) := by
  obtain ⟨j, hj, h'⟩ := (mem_edgesFrom_one _ _ _).1 h
  exact ⟨j, hj, by rw [h']; simp⟩

theorem ladF2 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX2 m) :
    a = ((2 * (m : ℤ) + 3, 0), (2 * (m : ℤ) + 3, 1)) := by
  rw [mem_single_i] at h
  rw [h]; simp [Unit4.vec]

theorem ladF3 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX3 m) :
    ∃ j : ℕ, j < 2 * m + 5 ∧ a = ((2 * (m : ℤ) + 3 + (j : ℤ), 1), (2 * (m : ℤ) + 3 + (j : ℤ) + 1, 1)) := by
  obtain ⟨j, hj, h'⟩ := (mem_edgesFrom_one _ _ _).1 h
  exact ⟨j, hj, by rw [h']⟩

theorem ladF4 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX4 m) :
    (a = ((4 * (m : ℤ) + 8, 1), (4 * (m : ℤ) + 8, 2)) ∨ a = ((4 * (m : ℤ) + 8, 2), (4 * (m : ℤ) + 8, 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (a = ((4 * (m : ℤ) + 8 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ))) ∨
          a = ((4 * (m : ℤ) + 7 - (j : ℤ), 3 + (j : ℤ)), (4 * (m : ℤ) + 7 - (j : ℤ), 4 + (j : ℤ))))) ∨
      a = ((2 * (m : ℤ) + 6, 2 * (m : ℤ) + 5), (2 * (m : ℤ) + 6, 2 * (m : ℤ) + 6))) ∨
    (∃ j : ℕ, j < 2 * m + 3 ∧ a = ((2 * (m : ℤ) + 6 - (j : ℤ), 2 * (m : ℤ) + 6),
      (2 * (m : ℤ) + 6 - (j : ℤ) - 1, 2 * (m : ℤ) + 6))) := by
  rw [ladX4, edgesFrom_append] at h
  rcases List.mem_append.1 h with hQ | hA
  · exact Or.inl (ladderQ_cases m a hQ)
  · rw [start_A'] at hA
    obtain ⟨j, hj, h'⟩ := (mem_edgesFrom_negOne _ _ _).1 hA
    exact Or.inr ⟨j, hj, h'⟩

theorem ladF5 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX5 m) :
    a = ((3, 2 * (m : ℤ) + 6), (3, 2 * (m : ℤ) + 5)) := by
  rw [mem_single_negI] at h
  rw [h]; simp [Unit4.vec]; omega

theorem ladF6 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX6 m) :
    ∃ j : ℕ, j < 2 * m + 5 ∧ a = ((3 - (j : ℤ), 2 * (m : ℤ) + 5), (3 - (j : ℤ) - 1, 2 * (m : ℤ) + 5)) := by
  obtain ⟨j, hj, h'⟩ := (mem_edgesFrom_negOne _ _ _).1 h
  exact ⟨j, hj, by rw [h']⟩

theorem ladF7 (m : ℕ) (a : GInt × GInt) (h : a ∈ ladX7 m) :
    a = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 5), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4)) ∨
      a = ((-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 4), (-2 * (m : ℤ) - 2, 2 * (m : ℤ) + 3)) ∨
      (∃ j : ℕ, j < 2 * m + 1 + 1 ∧
        (a = ((-2 * (m : ℤ) - 2 + (j : ℤ), 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ))) ∨
          a = ((-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 3 - (j : ℤ)),
            (-2 * (m : ℤ) - 2 + (j : ℤ) + 1, 2 * (m : ℤ) + 2 - (j : ℤ))))) ∨
      a = ((0, 1), (0, 0)) :=
  ladderS_cases m a h

theorem ladDJ12 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX2 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF2 m _ hb with h ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ13 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX3 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF3 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ14 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX4 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF4 m _ hb with (h | h | ⟨j, hj, h | h⟩ | h) | ⟨j, hj, h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ15 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX5 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF5 m _ hb with h ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ16 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX6 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF6 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ17 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ23 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX3 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF2 m a ha with rfl; rcases ladF3 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ24 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX4 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF2 m a ha with rfl; rcases ladF4 m _ hb with (h | h | ⟨j, hj, h | h⟩ | h) | ⟨j, hj, h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ25 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX5 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF2 m a ha with rfl; rcases ladF5 m _ hb with h ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ26 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX6 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF2 m a ha with rfl; rcases ladF6 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ27 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF2 m a ha with rfl; rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ34 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX4 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF4 m _ hb with (h | h | ⟨j, hj, h | h⟩ | h) | ⟨j, hj, h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ35 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX5 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF5 m _ hb with h ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ36 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX6 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF6 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ37 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ45 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX5 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF5 m _ hb with h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ46 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX6 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF6 m _ hb with ⟨j, hj, h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ47 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ56 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX5 m) (hb : b ∈ ladX6 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF5 m a ha with rfl; rcases ladF6 m _ hb with ⟨j, hj, h⟩ ;
    simp only [Prod.mk.injEq] at h; omega

theorem ladDJ57 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX5 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF5 m a ha with rfl; rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

theorem ladDJ67 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX6 m) (hb : b ∈ ladX7 m) : a ≠ b := by
  intro heq
  rw [← heq] at hb
  rcases ladF6 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m _ hb with h | h | ⟨j, hj, h | h⟩ | h <;>
    simp only [Prod.mk.injEq] at h <;> omega


theorem cross_app {α : Type} {X Y Z : List α} (h1 : ∀ a ∈ X, ∀ b ∈ Y, a ≠ b) (h2 : ∀ a ∈ X, ∀ b ∈ Z, a ≠ b) :
    ∀ a ∈ X, ∀ b ∈ Y ++ Z, a ≠ b := by
  intro a ha b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact h1 a ha b hb
  · exact h2 a ha b hb

theorem ladderWord_nodup (m : ℕ) : (edgesFrom (0, 0) (ladderWord m)).Nodup := by
  have n1 : (ladX1 m).Nodup := edgesFrom_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  have n2 : (ladX2 m).Nodup := edgesFrom_nodup_pos _ _ (fun x hx => by simp at hx; exact Or.inl hx)
  have n3 : (ladX3 m).Nodup := edgesFrom_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  have n4 : (ladX4 m).Nodup := edgesFrom_nodup_pos _ _ (letters_Q (2 * m + 1 + 1) (2 * m + 3))
  have n5 : (ladX5 m).Nodup := edgesFrom_nodup_neg _ _ (fun x hx => by simp at hx; exact Or.inr hx)
  have n6 : (ladX6 m).Nodup := edgesFrom_nodup_pos _ _ (fun x hx => Or.inr (List.eq_of_mem_replicate hx))
  have n7 : (ladX7 m).Nodup := edgesFrom_nodup_neg _ _ (letters_S (2 * m + 1 + 1))
  have d12 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX2 m, a ≠ b := fun a ha b hb => ladDJ12 m a b ha hb
  have d13 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX3 m, a ≠ b := fun a ha b hb => ladDJ13 m a b ha hb
  have d14 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX4 m, a ≠ b := fun a ha b hb => ladDJ14 m a b ha hb
  have d15 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX5 m, a ≠ b := fun a ha b hb => ladDJ15 m a b ha hb
  have d16 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX6 m, a ≠ b := fun a ha b hb => ladDJ16 m a b ha hb
  have d17 : ∀ a ∈ ladX1 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ17 m a b ha hb
  have d23 : ∀ a ∈ ladX2 m, ∀ b ∈ ladX3 m, a ≠ b := fun a ha b hb => ladDJ23 m a b ha hb
  have d24 : ∀ a ∈ ladX2 m, ∀ b ∈ ladX4 m, a ≠ b := fun a ha b hb => ladDJ24 m a b ha hb
  have d25 : ∀ a ∈ ladX2 m, ∀ b ∈ ladX5 m, a ≠ b := fun a ha b hb => ladDJ25 m a b ha hb
  have d26 : ∀ a ∈ ladX2 m, ∀ b ∈ ladX6 m, a ≠ b := fun a ha b hb => ladDJ26 m a b ha hb
  have d27 : ∀ a ∈ ladX2 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ27 m a b ha hb
  have d34 : ∀ a ∈ ladX3 m, ∀ b ∈ ladX4 m, a ≠ b := fun a ha b hb => ladDJ34 m a b ha hb
  have d35 : ∀ a ∈ ladX3 m, ∀ b ∈ ladX5 m, a ≠ b := fun a ha b hb => ladDJ35 m a b ha hb
  have d36 : ∀ a ∈ ladX3 m, ∀ b ∈ ladX6 m, a ≠ b := fun a ha b hb => ladDJ36 m a b ha hb
  have d37 : ∀ a ∈ ladX3 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ37 m a b ha hb
  have d45 : ∀ a ∈ ladX4 m, ∀ b ∈ ladX5 m, a ≠ b := fun a ha b hb => ladDJ45 m a b ha hb
  have d46 : ∀ a ∈ ladX4 m, ∀ b ∈ ladX6 m, a ≠ b := fun a ha b hb => ladDJ46 m a b ha hb
  have d47 : ∀ a ∈ ladX4 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ47 m a b ha hb
  have d56 : ∀ a ∈ ladX5 m, ∀ b ∈ ladX6 m, a ≠ b := fun a ha b hb => ladDJ56 m a b ha hb
  have d57 : ∀ a ∈ ladX5 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ57 m a b ha hb
  have d67 : ∀ a ∈ ladX6 m, ∀ b ∈ ladX7 m, a ≠ b := fun a ha b hb => ladDJ67 m a b ha hb
  have R6 : (ladX6 m ++ ladX7 m).Nodup := List.nodup_append.2 ⟨n6, n7, d67⟩
  have R5 : (ladX5 m ++ (ladX6 m ++ ladX7 m)).Nodup := List.nodup_append.2 ⟨n5, R6, cross_app d56 d57⟩
  have R4 : (ladX4 m ++ (ladX5 m ++ (ladX6 m ++ ladX7 m))).Nodup :=
    List.nodup_append.2 ⟨n4, R5, cross_app d45 (cross_app d46 d47)⟩
  have R3 : (ladX3 m ++ (ladX4 m ++ (ladX5 m ++ (ladX6 m ++ ladX7 m)))).Nodup :=
    List.nodup_append.2 ⟨n3, R4, cross_app d34 (cross_app d35 (cross_app d36 d37))⟩
  have R2 : (ladX2 m ++ (ladX3 m ++ (ladX4 m ++ (ladX5 m ++ (ladX6 m ++ ladX7 m))))).Nodup :=
    List.nodup_append.2 ⟨n2, R3, cross_app d23 (cross_app d24 (cross_app d25 (cross_app d26 d27)))⟩
  rw [ladderWord_edges]
  exact List.nodup_append.2 ⟨n1, R2, cross_app d12 (cross_app d13 (cross_app d14 (cross_app d15 (cross_app d16 d17))))⟩

/-! ### The ladder boundary word: sum, boundary and admissibility -/

theorem ladderWord_sum (m : ℕ) : F2Word.sum (ladderWord m) = 0 := by
  simp only [ladderWord, f2sum_append, sum_rep_one, sum_rep_negOne, sum_single_i, sum_single_negI, sum_ii,
    sum_negI_negI, sum_flat_negOne_i, sum_flat_one_negI]
  apply Prod.ext <;> simp <;> ring

/-- The reciprocal doubled staircase tile: `ladderWord m` is a boundary word of its cell set, at `(0,0)`. -/
theorem ladder_boundary (m : ℕ) :
    IsBoundaryWordAt (ladderCells (2 * (m : ℤ) + 4)) (0, 0) (ladderWord m) := by
  have hd : (4 : ℤ) ≤ 2 * (m : ℤ) + 4 := by omega
  refine ⟨ladderCells_lowerLeft _ hd, ladderWord_sum m, ?_, ?_⟩
  · rw [zip_walk_eq]
    exact ladderWord_nodup m
  · rw [zip_walk_eq]
    ext e
    rw [List.mem_toFinset, mem_boundaryEdges_iff_shape]
    exact ⟨fun h => ladder_walk_sub m e h, fun h => ladder_bdry_sub m e h⟩

theorem ifollow_base (b : ℕ) (hb : 3 ≤ b) : IFollowedBy 3 (Unit4.i :: List.replicate b Unit4.one) := by
  intro j hj m hm
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero] at hj
    simp only [show 0 + 1 + m = m + 1 by omega, List.getElem?_cons_succ, List.getElem?_replicate]
    simp [show m < b by omega]
  | succ j =>
    simp only [List.getElem?_cons_succ, List.getElem?_replicate] at hj
    split_ifs at hj; simp at hj

theorem ifollow_cons_one (w : F2Word) (h : IFollowedBy 3 w) : IFollowedBy 3 (Unit4.one :: w) := by
  intro j hj m hm
  cases j with
  | zero => simp at hj
  | succ j =>
    rw [List.getElem?_cons_succ] at hj
    rw [show j + 1 + 1 + m = (j + 1 + m) + 1 by omega, List.getElem?_cons_succ]
    exact h j hj m hm

theorem ifollow_block (a b : ℕ) (hb : 3 ≤ b) :
    IFollowedBy 3 (List.replicate a Unit4.one ++ [Unit4.i] ++ List.replicate b Unit4.one) := by
  induction a with
  | zero => simpa using ifollow_base b hb
  | succ a ih =>
    simp only [List.replicate_succ, List.cons_append]
    exact ifollow_cons_one _ ih

theorem ladder_w1_eq (m : ℕ) :
    List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one =
      [Unit4.one] ++ (List.replicate (2 * m + 2) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 2) Unit4.one) ++
        [Unit4.one, Unit4.one, Unit4.one] := by
  have e1 : List.replicate (2 * m + 3) Unit4.one = [Unit4.one] ++ List.replicate (2 * m + 2) Unit4.one := rfl
  have e2 : List.replicate (2 * m + 5) Unit4.one =
      List.replicate (2 * m + 2) Unit4.one ++ [Unit4.one, Unit4.one, Unit4.one] :=
    List.replicate_add (2 * m + 2) 3 Unit4.one
  rw [e1, e2]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

theorem ladder_admissible_w1 (m : ℕ) :
    Admissible (List.replicate (2 * m + 3) Unit4.one ++ [Unit4.i] ++ List.replicate (2 * m + 5) Unit4.one) := by
  have hw := ladder_w1_eq m
  unfold Admissible
  refine ⟨?_, ?_, ?_, Or.inr (Or.inr ⟨_, hw, ?_, ifollow_block (2 * m + 3) (2 * m + 5) (by omega)⟩)⟩
  · intro x hx
    rw [hw] at hx
    rcases List.mem_append.1 hx with h | h
    · rcases List.mem_append.1 h with h | h
      · simp at h; exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl (List.eq_of_mem_replicate h)
          · simp at h; exact Or.inr h
        · exact Or.inl (List.eq_of_mem_replicate h)
    · simp at h; exact Or.inl h
  · rw [hw]
    simp
  · rw [hw, List.getLast?_append]
    simp
  · simp [List.reverse_append, List.reverse_replicate]

theorem ladder_W2_mulNegI (m : ℕ) :
    (gV (ladderV (m + 1))).map Unit4.mulNegI =
      [Unit4.one, Unit4.one] ++ (List.replicate (2 * m + 1 + 1) [Unit4.i, Unit4.one]).flatten ++ [Unit4.one] := by
  rw [gV_ladder]
  simp only [List.map_append, List.map_cons, List.map_nil, map_mulNegI_flat]
  simp [Unit4.mulNegI, Unit4.mulI]

theorem ladder_admissible_w2 (m : ℕ) : Admissible ((gV (ladderV (m + 1))).map Unit4.mulNegI) := by
  rw [ladder_W2_mulNegI]
  exact admissible_pal _

theorem sum_gV_ladder_explicit (m : ℕ) : F2Word.sum (gV (ladderV (m + 1))) = (-(2 * (m : ℤ) + 2), 2 * (m : ℤ) + 5) := by
  rw [gV_ladder, f2sum_append, f2sum_append, sum_ii, sum_flat_negOne_i, sum_single_i]
  apply Prod.ext <;> simp <;> ring

theorem almostV1_ladder (m : ℕ) :
    almostV₁ (gH (ladderH (m + 1))) = (2 * (2 * (m : ℤ) + 4), 2 * 1) := by
  rw [almostV₁, gH_ladderH, f2sum_append, f2sum_append, sum_rep_one, sum_single_i, sum_rep_one, gI]
  apply Prod.ext <;> simp; ring

theorem almostV2_ladder (m : ℕ) :
    almostV₂ (gV (ladderV (m + 1))) = (1 - (2 * (m : ℤ) + 4), 1 + (2 * (m : ℤ) + 4)) := by
  rw [almostV₂, sum_gV_ladder_explicit, gOne]
  apply Prod.ext <;> simp <;> ring

theorem ladder_lattice (m : ℕ) :
    latticeOf (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1))))
      = paperLattice 1 (2 * (m : ℤ) + 4) := by
  rw [almostV1_ladder, almostV2_ladder, paperLattice, if_neg (by omega)]

/-! ### The base tiles of `prop:base_cases` -/

theorem stair_boundary_word (k : ℕ) :
    IsBoundaryWord (stairCells (2 * (k : ℤ) + 3)) (boundaryWordOf (gH (stairH k)) (gV (stairV k))) := by
  refine ⟨(0, 0), ?_⟩
  have h := stairWord_boundary k
  rw [← pseudoBoundaryWord_stair] at h
  exact h

theorem ladder_boundary_word (m : ℕ) :
    IsBoundaryWord (ladderCells (2 * (m : ℤ) + 4))
      (boundaryWordOf (gH (ladderH (m + 1))) (gV (ladderV (m + 1)))) := by
  refine ⟨(0, 0), ?_⟩
  have h := ladder_boundary m
  rw [← pseudoBoundaryWord_ladder] at h
  exact h

/-- The staircase base tile `d = 2k + 3`: (i) its boundary word, (ii) admissibility of `w₁` and `-i·w₂`,
(iii) the lattice generated by `Σw₁ + i` and `Σw₂ - 1` is `L'(1/d)`. -/
theorem stair_base_tile (k : ℕ) :
    IsBoundaryWord (stairCells (2 * (k : ℤ) + 3)) (boundaryWordOf (gH (stairH k)) (gV (stairV k))) ∧
      Admissible (gH (stairH k)) ∧ Admissible ((gV (stairV k)).map Unit4.mulNegI) ∧
      latticeOf (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) = paperLattice 1 (2 * (k : ℤ) + 3) :=
  ⟨stair_boundary_word k, (stair_admissible k).1, (stair_admissible k).2, stair_lattice k⟩

/-- The doubled staircase base tile `d = 2k + 2` with `k = m + 1`: (i)-(iii) as for `stair_base_tile`. -/
theorem ladder_base_tile (m : ℕ) :
    IsBoundaryWord (ladderCells (2 * (m : ℤ) + 4))
      (boundaryWordOf (gH (ladderH (m + 1))) (gV (ladderV (m + 1)))) ∧
      Admissible (gH (ladderH (m + 1))) ∧ Admissible ((gV (ladderV (m + 1))).map Unit4.mulNegI) ∧
      latticeOf (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1))))
        = paperLattice 1 (2 * (m : ℤ) + 4) :=
  ⟨ladder_boundary_word m, by rw [gH_ladderH]; exact ladder_admissible_w1 m, ladder_admissible_w2 m,
    ladder_lattice m⟩

end FLatticePaper.Tiles
