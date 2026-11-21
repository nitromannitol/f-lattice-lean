import FLatticePaper.Tiles.NearOneRotation
import FLatticePaper.Tiles.BaseCaseDecided
import FLatticePaper.Tiles.BaseCaseGlobal

/-! The near-one almost tilings of `prop:base_cases` (a).

The near-one cell tile is the quarter turn of the reciprocal cell tile. A cell `c` of the turned tile sits over the
reciprocal cell `turnCell v c = (c2 - v2, v1 - c1 - 1)`, and the linear part of the turn is `lin u = (u2, -u1)`
(multiplication by `-i`), with inverse `unlin w = (-w2, w1)`. The translates of the turned tile are indexed by the
lattice `unlin (L0)`, where `L0` is the reciprocal lattice. All four predicates of a regular almost tiling, the two
global inputs `NoFirstCrossing` and `NoFarAdjacency`, and the edge-sharing clause transport along this turn. The
decided inputs of the reciprocal stairs (`d = 3, 5, 7`) therefore carry over. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction (paperNearStairTile paperNearLadderTile)

namespace NearTurn

/-- The linear part of the quarter turn: multiplication by `-i`. -/
def lin (u : GInt) : GInt := (u.2, -u.1)

/-- The inverse quarter turn: multiplication by `i`. -/
def unlin (w : GInt) : GInt := (-w.2, w.1)

/-- The reciprocal cell of the turned cell `c`: `c` lies in the turned tile iff `turnCell v c` lies in the reciprocal
tile. -/
def turnCell (v c : GInt) : GInt := (c.2 - v.2, v.1 - c.1 - 1)

/-- The turned cell over a reciprocal cell `p`: the inverse of `turnCell v`. -/
def turnBackCell (v p : GInt) : GInt := (v.1 - p.2 - 1, p.1 + v.2)

/-- The turned cell tile: the cells `c` with `turnCell v c` in `T0`. -/
def cellTurn (v : GInt) (T0 : CellTile) : CellTile := T0.image (turnBackCell v)

theorem lin_unlin (w : GInt) : lin (unlin w) = w := by
  ext <;> simp [lin, unlin]

theorem unlin_lin (u : GInt) : unlin (lin u) = u := by
  ext <;> simp [lin, unlin]

theorem unlin_zero : unlin 0 = 0 := by
  ext <;> simp [unlin]

theorem unlin_neg (w : GInt) : unlin (-w) = -unlin w := by
  ext <;> simp [unlin]

theorem lin_ne_zero {u : GInt} (hu : u ≠ 0) : lin u ≠ 0 :=
  fun h => hu (by rw [← unlin_lin u, h, unlin_zero])

theorem mem_dirs4 {e : GInt} :
    e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)] ↔
      e = (1, 0) ∨ e = (0, 1) ∨ e = (-1, 0) ∨ e = (0, -1) := by
  simp

theorem lin_mem_dirs4 {e : GInt} (he : e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)]) :
    lin e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)] := by
  rw [mem_dirs4] at he ⊢
  rcases he with rfl | rfl | rfl | rfl <;> simp [lin]

theorem unlin_mem_dirs4 {e : GInt} (he : e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)]) :
    unlin e ∈ [((1 : ℤ), (0 : ℤ)), (0, 1), (-1, 0), (0, -1)] := by
  rw [mem_dirs4] at he ⊢
  rcases he with rfl | rfl | rfl | rfl <;> simp [unlin]

theorem turnCell_add (v c u : GInt) : turnCell v (c + u) = turnCell v c + lin u := by
  ext <;> simp only [turnCell, lin, Prod.fst_add, Prod.snd_add] <;> omega

theorem turnCell_sub (v c u : GInt) : turnCell v (c - u) = turnCell v c - lin u := by
  ext <;> simp only [turnCell, lin, Prod.fst_sub, Prod.snd_sub] <;> omega

theorem turnBack_turnCell (v c : GInt) : turnBackCell v (turnCell v c) = c := by
  ext <;> simp only [turnBackCell, turnCell] <;> omega

theorem turnCell_turnBack (v p : GInt) : turnCell v (turnBackCell v p) = p := by
  ext <;> simp only [turnBackCell, turnCell] <;> omega

theorem mem_cellTurn (v : GInt) (T0 : CellTile) (c : GInt) :
    c ∈ cellTurn v T0 ↔ turnCell v c ∈ T0 := by
  unfold cellTurn
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rwa [turnCell_turnBack]
  · intro h
    exact ⟨turnCell v c, h, turnBack_turnCell v c⟩

/-- A reciprocal corner test: `x` is a corner of the cell `c` iff the turned point of `x` is a corner of the turned
cell of `c`. -/
theorem mem_cellCorners_turn (v x c : GInt) :
    x ∈ cellCorners c ↔ (x.2 - v.2, v.1 - x.1) ∈ cellCorners (turnCell v c) := by
  rw [mem_cellCorners_iff, mem_cellCorners_iff]
  dsimp only [turnCell]
  constructor <;> intro h <;> omega

theorem mem_latticeOf_unlin (a b u : GInt) :
    u ∈ latticeOf (unlin a) (unlin b) ↔ lin u ∈ latticeOf a b := by
  simp only [latticeOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, k', rfl⟩
    exact ⟨k, k', Prod.ext (by simp only [lin, unlin]) (by simp only [lin, unlin]; ring)⟩
  · rintro ⟨k, k', h⟩
    refine ⟨k, k', ?_⟩
    rw [← unlin_lin u, h]
    exact Prod.ext (by simp only [unlin]; ring) (by simp only [unlin])

theorem mem_surround_unlin (a b n : GInt) :
    n ∈ surroundVectors (unlin a) (unlin b) ↔ lin n ∈ surroundVectors a b := by
  simp only [surroundVectors, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, k', h1, h2, h3, h4, h5, rfl⟩
    exact ⟨k, k', h1, h2, h3, h4, h5, Prod.ext (by simp only [lin, unlin]) (by simp only [lin, unlin]; ring)⟩
  · rintro ⟨k, k', h1, h2, h3, h4, h5, h⟩
    refine ⟨k, k', h1, h2, h3, h4, h5, ?_⟩
    rw [← unlin_lin n, h]
    exact Prod.ext (by simp only [unlin]; ring) (by simp only [unlin])

theorem overlap_cellTurn (v : GInt) (T0 : CellTile) (u : GInt) :
    Overlap (cellTurn v T0) u ↔ Overlap T0 (lin u) := by
  unfold Overlap
  constructor
  · rintro ⟨x, hx, hxu⟩
    refine ⟨turnCell v x, (mem_cellTurn v T0 x).1 hx, ?_⟩
    have h := (mem_cellTurn v T0 (x - u)).1 hxu
    rwa [turnCell_sub] at h
  · rintro ⟨p, hp, hpu⟩
    refine ⟨turnBackCell v p, (mem_cellTurn v T0 _).2 (by rw [turnCell_turnBack]; exact hp), ?_⟩
    rw [mem_cellTurn, turnCell_sub, turnCell_turnBack]
    exact hpu

/-- The turned tile has the transported translates: the almost tiling property passes to the turned tile, over the
unlin-image of the lattice. -/
theorem almost_cellTurn (v : GInt) {T0 : CellTile} {a b : GInt}
    (h : IsAlmostTiling T0 (latticeOf a b)) :
    IsAlmostTiling (cellTurn v T0) (latticeOf (unlin a) (unlin b)) := by
  obtain ⟨hU, hC⟩ := h
  refine ⟨?_, ?_⟩
  · intro c u hu u' hu' hcu hcu'
    rw [mem_latticeOf_unlin] at hu hu'
    rw [mem_cellTurn, turnCell_sub] at hcu hcu'
    have key := hU (turnCell v c) (lin u) hu (lin u') hu' hcu hcu'
    rw [← unlin_lin u, key, unlin_lin]
  · intro x
    obtain ⟨w, hw, y', hy', hq⟩ := hC (x.2 - v.2, v.1 - x.1)
    refine ⟨unlin w, (mem_latticeOf_unlin a b (unlin w)).2 (by rw [lin_unlin]; exact hw),
      turnBackCell v y', (mem_cellTurn v T0 _).2 (by rw [turnCell_turnBack]; exact hy'), ?_⟩
    rw [mem_cellCorners_turn v x, turnCell_add, turnCell_turnBack, lin_unlin]
    exact hq

theorem noFirst_cellTurn (v : GInt) {T0 : CellTile} {a b : GInt} (h : NoFirstCrossing T0 a b) :
    NoFirstCrossing (cellTurn v T0) (unlin a) (unlin b) := by
  refine ⟨fun u hu hne hov => ?_⟩
  rw [mem_latticeOf_unlin] at hu
  rw [overlap_cellTurn] at hov
  obtain ⟨n0, hn0, hovn0⟩ := h.propagate (lin u) hu (lin_ne_zero hne) hov
  refine ⟨unlin n0, (mem_surround_unlin a b (unlin n0)).2 (by rw [lin_unlin]; exact hn0), ?_⟩
  rw [overlap_cellTurn, lin_unlin]
  exact hovn0

theorem noFar_cellTurn (v : GInt) {T0 : CellTile} {a b : GInt} (h : NoFarAdjacency T0 a b) :
    NoFarAdjacency (cellTurn v T0) (unlin a) (unlin b) := by
  refine ⟨fun d hd hdT => ?_⟩
  obtain ⟨c, hc, e, he, hce⟩ := hd
  have hc' : turnCell v c ∈ T0 := (mem_cellTurn v T0 c).1 hc
  have hdT' : turnCell v d ∉ T0 := fun h' => hdT ((mem_cellTurn v T0 d).2 h')
  have key : turnCell v c + lin e = turnCell v d := by
    rw [← turnCell_add, hce]
  rcases h.gap (turnCell v d) ⟨turnCell v c, hc', lin e, lin_mem_dirs4 he, key⟩ hdT' with
    ⟨s, hs, hsT⟩ | hall
  · left
    refine ⟨unlin s, (mem_surround_unlin a b (unlin s)).2 (by rw [lin_unlin]; exact hs), ?_⟩
    rw [mem_cellTurn, turnCell_sub, lin_unlin]
    exact hsT
  · right
    intro u hu hdu
    have h1 : turnCell v d - lin u ∈ T0 := by
      have h2 := (mem_cellTurn v T0 (d - u)).1 hdu
      rwa [turnCell_sub] at h2
    exact hall (lin u) ((mem_latticeOf_unlin a b u).1 hu) h1

theorem sharesEdge_cellTurn (v : GInt) (T0 : CellTile) (u : GInt) :
    SharesEdge (cellTurn v T0) u ↔ SharesEdge T0 (lin u) := by
  unfold SharesEdge
  constructor
  · rintro ⟨c, hc, e, he, hce⟩
    refine ⟨turnCell v c, (mem_cellTurn v T0 c).1 hc, lin e, lin_mem_dirs4 he, ?_⟩
    have h := (mem_cellTurn v T0 (c + e - u)).1 hce
    rwa [turnCell_sub, turnCell_add] at h
  · rintro ⟨p, hp, e', he', hpe⟩
    refine ⟨turnBackCell v p, (mem_cellTurn v T0 _).2 (by rw [turnCell_turnBack]; exact hp),
      unlin e', unlin_mem_dirs4 he', ?_⟩
    rw [mem_cellTurn, turnCell_sub, turnCell_add, turnCell_turnBack, lin_unlin]
    exact hpe

theorem edge_cellTurn (v : GInt) {T0 : CellTile} {a b : GInt} (h : EdgeSharingClause T0 a b) :
    EdgeSharingClause (cellTurn v T0) (unlin a) (unlin b) := by
  intro u hu hne hsh
  rw [mem_latticeOf_unlin] at hu
  rcases h (lin u) hu (lin_ne_zero hne) ((sharesEdge_cellTurn v T0 u).1 hsh) with
    h1 | h2 | h3 | h4
  · left
    rw [← unlin_lin u, h1]
  · right; left
    rw [← unlin_lin u, h2, unlin_neg]
  · right; right; left
    rw [← unlin_lin u, h3]
  · right; right; right
    rw [← unlin_lin u, h4, unlin_neg]

/-- The vertices of the turned cell tile are the turned vertices of `T0`. -/
theorem vertices_cellTurn (v : GInt) (T0 : CellTile) (x : GInt) :
    x ∈ (cellTurn v T0).vertices ↔ (x.2 - v.2, v.1 - x.1) ∈ T0.vertices := by
  unfold CellTile.vertices
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hx⟩
    exact ⟨turnCell v c, (mem_cellTurn v T0 c).1 hc, (mem_cellCorners_turn v x c).1 hx⟩
  · rintro ⟨p, hp, hq⟩
    refine ⟨turnBackCell v p, (mem_cellTurn v T0 _).2 (by rw [turnCell_turnBack]; exact hp), ?_⟩
    rw [mem_cellCorners_turn v x, turnCell_turnBack]
    exact hq

/-- The unlin-image of the reciprocal lattice `latticeOf (2k+3, 1) (1-(2k+3), 1+(2k+3))` is `paperLattice (k+1) (k+2)`,
the paper lattice `L'(R(1/d))` of the rotated fraction `(k+1)/(k+2)`, `d = 2k+3`. -/
theorem stair_unlin_lattice (k : ℤ) :
    latticeOf (unlin (2 * k + 3, 1)) (unlin (1 - (2 * k + 3), 1 + (2 * k + 3))) =
      paperLattice (k + 1) (k + 2) := by
  have hpar : ¬ (k + 1 + (k + 2)) % 2 = 0 := by omega
  unfold paperLattice
  rw [if_neg hpar]
  ext u
  simp only [latticeOf, Set.mem_setOf_eq, unlin]
  constructor
  · rintro ⟨k1, k2, rfl⟩
    exact ⟨-k2, k1, by ext <;> dsimp only <;> ring⟩
  · rintro ⟨c, c', rfl⟩
    exact ⟨c', -c, by ext <;> dsimp only <;> ring⟩

/-- The near-one stair cell tile over the reciprocal stair `stairCells (2k+3)`: an almost tiling of the paper lattice
`L'(R(1/d))`, with the reciprocal global inputs carried by the turn. -/
theorem nearStair_almost (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k)))) :
    IsAlmostTiling (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
      (paperLattice ((k : ℤ) + 1) ((k : ℤ) + 2)) := by
  have hR : IsAlmostTiling (stairCells (2 * (k : ℤ) + 3))
      (latticeOf (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k)))) := by
    rw [(stair_base_tile k).2.2.2]
    exact stair_almost_tiling_paper k hF hG
  have h := almost_cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) hR
  rw [almostV1_stair, almostV2_stair, stair_unlin_lattice] at h
  exact h

/-- The two global inputs and the edge-sharing clause for the near-one stair, transported from the reciprocal ones. -/
theorem nearStair_global (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k)))
      (almostV₂ (gV (stairV k)))) :
    NoFirstCrossing (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) ∧
      NoFarAdjacency (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) ∧
      EdgeSharingClause
        (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) :=
  ⟨noFirst_cellTurn _ hF, noFar_cellTurn _ hG, edge_cellTurn _ (stair_almost_tiling k hF hG).2⟩

/-- The decided input for `d = 3` (`k = 0`). -/
theorem nearStair_almost_d3 :
    IsAlmostTiling
      (cellTurn (2 * ((0 : ℕ) : ℤ) + 3 + 1, 2 * ((0 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((0 : ℕ) : ℤ) + 3)))
      (paperLattice (((0 : ℕ) : ℤ) + 1) (((0 : ℕ) : ℤ) + 2)) :=
  nearStair_almost 0
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The decided input for `d = 5` (`k = 1`). -/
theorem nearStair_almost_d5 :
    IsAlmostTiling
      (cellTurn (2 * ((1 : ℕ) : ℤ) + 3 + 1, 2 * ((1 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((1 : ℕ) : ℤ) + 3)))
      (paperLattice (((1 : ℕ) : ℤ) + 1) (((1 : ℕ) : ℤ) + 2)) :=
  nearStair_almost 1
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The decided input for `d = 7` (`k = 2`). -/
theorem nearStair_almost_d7 :
    IsAlmostTiling
      (cellTurn (2 * ((2 : ℕ) : ℤ) + 3 + 1, 2 * ((2 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((2 : ℕ) : ℤ) + 3)))
      (paperLattice (((2 : ℕ) : ℤ) + 1) (((2 : ℕ) : ℤ) + 2)) :=
  nearStair_almost 2
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The vertex set of the near-one stair cell tile is the near-one chart `chartDown (paperNearStairTile d)`, the set
the pseudo-square `nearStair_isRotPseudoSquareT` is stated on. -/
theorem nearStair_vertices (k : ℕ) (x : GInt) :
    x ∈ (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3))).vertices ↔
      x ∈ chartDown (paperNearStairTile (2 * (k : ℤ) + 3)) := by
  rw [vertices_cellTurn, chartDown_nearStair, mem_turnedTile,
    mem_stairVertices (2 * (k : ℤ) + 3) (by omega)]

/-- The unlin-image of the reciprocal ladder lattice `latticeOf (4m+8, 2) (-(2m+3), 2m+5)` is `paperLattice (2m+3) (2m+5)`,
the paper lattice `L'(R(1/d))` of the rotated fraction `(2m+3)/(2m+5)`, `d = 2m+4`. -/
theorem ladder_unlin_lattice (m : ℤ) :
    latticeOf (unlin (2 * (2 * m + 4), 2 * 1)) (unlin (1 - (2 * m + 4), 1 + (2 * m + 4))) =
      paperLattice (2 * m + 3) (2 * m + 5) := by
  have hpar : (2 * m + 3 + (2 * m + 5)) % 2 = 0 := by omega
  unfold paperLattice
  rw [if_pos hpar]
  ext u
  simp only [latticeOf, Set.mem_setOf_eq, unlin]
  constructor
  · rintro ⟨k1, k2, rfl⟩
    exact ⟨-k2, k1, by ext <;> dsimp only <;> ring⟩
  · rintro ⟨c, c', rfl⟩
    exact ⟨c', -c, by ext <;> dsimp only <;> ring⟩

/-- The near-one ladder cell tile over the reciprocal ladder `ladderCells (2m+4)`: an almost tiling of the paper lattice
`L'(R(1/d))`, `d = 2m+4`. -/
theorem nearLadder_almost (m : ℕ)
    (hF : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1)))))
    (hG : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1))))) :
    IsAlmostTiling (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
      (paperLattice (2 * (m : ℤ) + 3) (2 * (m : ℤ) + 5)) := by
  have hR : IsAlmostTiling (ladderCells (2 * (m : ℤ) + 4))
      (latticeOf (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1))))) := by
    rw [(ladder_base_tile m).2.2.2]
    exact ladder_almost_tiling_paper m hF hG
  have h := almost_cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) hR
  rw [almostV1_ladder, almostV2_ladder, ladder_unlin_lattice] at h
  exact h

/-- The two global inputs and the edge-sharing clause for the near-one ladder, transported from the reciprocal ones. -/
theorem nearLadder_global (m : ℕ)
    (hF : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1)))))
    (hG : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4)) (almostV₁ (gH (ladderH (m + 1))))
      (almostV₂ (gV (ladderV (m + 1))))) :
    NoFirstCrossing (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) ∧
      NoFarAdjacency (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) ∧
      EdgeSharingClause
        (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) :=
  ⟨noFirst_cellTurn _ hF, noFar_cellTurn _ hG, edge_cellTurn _ (ladder_almost_tiling m hF hG).2⟩

/-- The decided input for `d = 4` (`m = 0`). -/
theorem nearLadder_almost_d4 :
    IsAlmostTiling
      (cellTurn (2 * ((0 : ℕ) : ℤ) + 4 + 1, 2 * ((0 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)))
      (paperLattice (2 * ((0 : ℕ) : ℤ) + 3) (2 * ((0 : ℕ) : ℤ) + 5)) :=
  nearLadder_almost 0
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The decided input for `d = 6` (`m = 1`). -/
theorem nearLadder_almost_d6 :
    IsAlmostTiling
      (cellTurn (2 * ((1 : ℕ) : ℤ) + 4 + 1, 2 * ((1 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)))
      (paperLattice (2 * ((1 : ℕ) : ℤ) + 3) (2 * ((1 : ℕ) : ℤ) + 5)) :=
  nearLadder_almost 1
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The vertex set of the near-one ladder cell tile is the near-one chart `chartDown (paperNearLadderTile d)`. -/
theorem nearLadder_vertices (m : ℕ) (x : GInt) :
    x ∈ (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4))).vertices ↔
      x ∈ chartDown (paperNearLadderTile (2 * (m : ℤ) + 4)) := by
  rw [vertices_cellTurn, chartDown_nearLadder, mem_turnedTile,
    mem_ladderVertices (2 * (m : ℤ) + 4) (by omega)]

/-- The decided near-one stair inputs for `d = 3`, `5`, `7`: the two global inputs and the edge-sharing clause of the
turned tile, transported from the decided reciprocal inputs. -/
theorem nearStair_global_d3 :
    NoFirstCrossing
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 3 + 1, 2 * ((0 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((0 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 0)))) (unlin (almostV₂ (gV (stairV 0)))) ∧
      NoFarAdjacency
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 3 + 1, 2 * ((0 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((0 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 0)))) (unlin (almostV₂ (gV (stairV 0)))) ∧
      EdgeSharingClause
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 3 + 1, 2 * ((0 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((0 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 0)))) (unlin (almostV₂ (gV (stairV 0)))) :=
  nearStair_global 0
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

theorem nearStair_global_d5 :
    NoFirstCrossing
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 3 + 1, 2 * ((1 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((1 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 1)))) (unlin (almostV₂ (gV (stairV 1)))) ∧
      NoFarAdjacency
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 3 + 1, 2 * ((1 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((1 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 1)))) (unlin (almostV₂ (gV (stairV 1)))) ∧
      EdgeSharingClause
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 3 + 1, 2 * ((1 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((1 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 1)))) (unlin (almostV₂ (gV (stairV 1)))) :=
  nearStair_global 1
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

theorem nearStair_global_d7 :
    NoFirstCrossing
        (cellTurn (2 * ((2 : ℕ) : ℤ) + 3 + 1, 2 * ((2 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((2 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 2)))) (unlin (almostV₂ (gV (stairV 2)))) ∧
      NoFarAdjacency
        (cellTurn (2 * ((2 : ℕ) : ℤ) + 3 + 1, 2 * ((2 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((2 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 2)))) (unlin (almostV₂ (gV (stairV 2)))) ∧
      EdgeSharingClause
        (cellTurn (2 * ((2 : ℕ) : ℤ) + 3 + 1, 2 * ((2 : ℕ) : ℤ) + 3 - 2) (stairCells (2 * ((2 : ℕ) : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH 2)))) (unlin (almostV₂ (gV (stairV 2)))) :=
  nearStair_global 2
    (by rw [almostV1_stair, almostV2_stair]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_stair, almostV2_stair]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The decided near-one ladder inputs for `d = 4` (`m = 0`). -/
theorem nearLadder_global_d4 :
    NoFirstCrossing
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 4 + 1, 2 * ((0 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (0 + 1))))) (unlin (almostV₂ (gV (ladderV (0 + 1))))) ∧
      NoFarAdjacency
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 4 + 1, 2 * ((0 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (0 + 1))))) (unlin (almostV₂ (gV (ladderV (0 + 1))))) ∧
      EdgeSharingClause
        (cellTurn (2 * ((0 : ℕ) : ℤ) + 4 + 1, 2 * ((0 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((0 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (0 + 1))))) (unlin (almostV₂ (gV (ladderV (0 + 1))))) :=
  nearLadder_global 0
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- The decided near-one ladder inputs for `d = 6` (`m = 1`). -/
theorem nearLadder_global_d6 :
    NoFirstCrossing
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 4 + 1, 2 * ((1 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (1 + 1))))) (unlin (almostV₂ (gV (ladderV (1 + 1))))) ∧
      NoFarAdjacency
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 4 + 1, 2 * ((1 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (1 + 1))))) (unlin (almostV₂ (gV (ladderV (1 + 1))))) ∧
      EdgeSharingClause
        (cellTurn (2 * ((1 : ℕ) : ℤ) + 4 + 1, 2 * ((1 : ℕ) : ℤ) + 4 - 2) (ladderCells (2 * ((1 : ℕ) : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (1 + 1))))) (unlin (almostV₂ (gV (ladderV (1 + 1))))) :=
  nearLadder_global 1
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFirstCrossing_of_decide _ _ _ (by decide +kernel))
    (by rw [almostV1_ladder, almostV2_ladder]; exact noFarAdjacency_of_decide _ _ _ (by decide +kernel))

/-- `prop:base_cases` (a), near-one stair rows: the turned stair tile is an almost tiling of `L'(R(1/d))`, `d = 2k+3`,
for every `k`, with no global hypothesis (the global inputs are w3's `stair_global`). -/
theorem nearStair_almost_all (k : ℕ) :
    IsAlmostTiling (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
      (paperLattice ((k : ℤ) + 1) ((k : ℤ) + 2)) :=
  nearStair_almost k (stair_global k).1 (stair_global k).2

/-- The near-one stair global inputs and edge-sharing clause, for every `k`, with no global hypothesis. -/
theorem nearStair_global_all (k : ℕ) :
    NoFirstCrossing
        (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) ∧
      NoFarAdjacency
        (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) ∧
      EdgeSharingClause
        (cellTurn (2 * (k : ℤ) + 3 + 1, 2 * (k : ℤ) + 3 - 2) (stairCells (2 * (k : ℤ) + 3)))
        (unlin (almostV₁ (gH (stairH k)))) (unlin (almostV₂ (gV (stairV k)))) :=
  nearStair_global k (stair_global k).1 (stair_global k).2

/-- `prop:base_cases` (a), near-one ladder rows: the turned doubled staircase is an almost tiling of `L'(R(1/d))`,
`d = 2m+4`, for every `m`, with no global hypothesis (the global inputs are w3's `ladder_global`). -/
theorem nearLadder_almost_all (m : ℕ) :
    IsAlmostTiling (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
      (paperLattice (2 * (m : ℤ) + 3) (2 * (m : ℤ) + 5)) :=
  nearLadder_almost m (ladder_global m).1 (ladder_global m).2

/-- The near-one ladder global inputs and edge-sharing clause, for every `m`, with no global hypothesis. -/
theorem nearLadder_global_all (m : ℕ) :
    NoFirstCrossing
        (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) ∧
      NoFarAdjacency
        (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) ∧
      EdgeSharingClause
        (cellTurn (2 * (m : ℤ) + 4 + 1, 2 * (m : ℤ) + 4 - 2) (ladderCells (2 * (m : ℤ) + 4)))
        (unlin (almostV₁ (gH (ladderH (m + 1))))) (unlin (almostV₂ (gV (ladderV (m + 1))))) :=
  nearLadder_global m (ladder_global m).1 (ladder_global m).2

end NearTurn

end FLatticePaper.Tiles
