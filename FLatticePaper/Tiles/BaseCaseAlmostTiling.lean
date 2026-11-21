import FLatticePaper.Tiles.BaseCaseTiling
import FLatticePaper.Tiles.AlmostTilingAssembly

/-! The base tiles of `prop:base_cases` as almost tiles. The vertices of the boundary walk of the reciprocal staircase
and of the doubled staircase are distinct except for the closing vertex, and their cell sets are edge-connected. So both
tiles are simple (`IsSimpleTile`), and `almost_square_tiling` applies to them, with the two global inputs carried as
hypotheses. -/

namespace FLatticePaper.Tiles

/-! ### The vertices of the walk -/

theorem walk_dropLast (c : GInt) (w : F2Word) :
    (F2Word.walk c w).dropLast = (edgesFrom c w).map Prod.fst := by
  induction w generalizing c with
  | nil => simp [F2Word.walk, edgesFrom]
  | cons x w ih =>
    obtain ⟨t, ht⟩ := walk_eq_cons (c + x.vec) w
    have ih' := ih (c + x.vec)
    rw [ht] at ih'
    rw [walkCons, ht, edgesFrom, List.map_cons, ← ih', List.dropLast_cons_of_ne_nil (List.cons_ne_nil (c + x.vec) t)]

theorem starts_nodup_pos (w : F2Word) (c : GInt) (hw : ∀ x ∈ w, x = Unit4.i ∨ x = Unit4.negOne) :
    ((edgesFrom c w).map Prod.fst).Nodup :=
  List.Nodup.of_map yMinusX (by
    rw [List.map_map]
    exact List.Pairwise.imp (fun h => ne_of_lt h) (yMinusX_pairwise_pos w c hw))

theorem starts_nodup_neg (w : F2Word) (c : GInt) (hw : ∀ x ∈ w, x = Unit4.one ∨ x = Unit4.negI) :
    ((edgesFrom c w).map Prod.fst).Nodup :=
  List.Nodup.of_map yMinusX (by
    rw [List.map_map]
    exact List.Pairwise.imp (fun h => ne_of_gt h) (yMinusX_pairwise_neg w c hw))

theorem cross_starts {X Y : List (GInt × GInt)} (h : ∀ e ∈ X, ∀ f ∈ Y, e.1 ≠ f.1) :
    ∀ a ∈ X.map Prod.fst, ∀ b ∈ Y.map Prod.fst, a ≠ b := by
  intro a ha b hb
  rw [List.mem_map] at ha hb
  obtain ⟨e, he, rfl⟩ := ha
  obtain ⟨f, hf, rfl⟩ := hb
  exact h e he f hf

/-! ### Adjacency of cells -/

theorem adj_right (a b : ℤ) : CellAdj ((a, b) : GInt) ((a + 1, b) : GInt) :=
  Or.inl (eq_add_one (a, b)).symm

theorem adj_left (a b : ℤ) : CellAdj ((a, b) : GInt) ((a - 1, b) : GInt) :=
  Or.inr (Or.inl (eq_sub_one (a, b)).symm)

theorem adj_up (a b : ℤ) : CellAdj ((a, b) : GInt) ((a, b + 1) : GInt) :=
  Or.inr (Or.inr (Or.inl (eq_add_I (a, b)).symm))

theorem adj_down (a b : ℤ) : CellAdj ((a, b) : GInt) ((a, b - 1) : GInt) :=
  Or.inr (Or.inr (Or.inr (eq_sub_I (a, b)).symm))

theorem adj_down' (a b c : ℤ) (h : c = b - 1) : CellAdj ((a, b) : GInt) ((a, c) : GInt) := by
  subst h
  exact adj_down a b

theorem adj_up' (a b c : ℤ) (h : c = b + 1) : CellAdj ((a, b) : GInt) ((a, c) : GInt) := by
  subst h
  exact adj_up a b

theorem adj_right' (a b c : ℤ) (h : c = a + 1) : CellAdj ((a, b) : GInt) ((c, b) : GInt) := by
  subst h
  exact adj_right a b

theorem cellAdj_symm {x y : GInt} (h : CellAdj x y) : CellAdj y x := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inr (by simp)))
  · exact Or.inr (Or.inr (Or.inl (by simp)))

theorem rtg_swap {α : Type} {R : α → α → Prop} (h : ∀ a b, R a b → R b a) {a b : α}
    (hab : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (h _ _ hbc) ih


/-! ### The starts of the staircase walk are distinct -/

theorem sd_PQ2 (k : ℕ) (e f : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one))
    (hf : f ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i])) :
    e.1 ≠ f.1 := by
  obtain ⟨j, hj, rfl⟩ := seg1_cases k e he
  intro heq
  rcases seg2_cases k f hf with rfl | rfl | ⟨m, hm, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem sd_PQ3 (k : ℕ) (e f : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one))
    (hf : f ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne)) :
    e.1 ≠ f.1 := by
  obtain ⟨j, hj, rfl⟩ := seg1_cases k e he
  obtain ⟨m, hm, rfl⟩ := seg3_cases k f hf
  intro heq
  dsimp only at heq
  simp only [Prod.mk.injEq] at heq; omega

theorem sd_PR (k : ℕ) (e f : GInt × GInt)
    (he : e ∈ edgesFrom (0, 0) (List.replicate (2 * k + 3) Unit4.one))
    (hf : f ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e.1 ≠ f.1 := by
  obtain ⟨j, hj, rfl⟩ := seg1_cases k e he
  intro heq
  rcases seg4_cases k f hf with rfl | rfl | ⟨n, hn, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem sd_QR2 (k : ℕ) (e f : GInt × GInt)
    (he : e ∈ edgesFrom (2 * (k : ℤ) + 3, 0)
      ([Unit4.i, Unit4.i] ++ (List.replicate (2 * k + 1) [Unit4.negOne, Unit4.i]).flatten ++ [Unit4.i]))
    (hf : f ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e.1 ≠ f.1 := by
  intro heq
  rcases seg2_cases k e he with rfl | rfl | ⟨m, hm, rfl | rfl⟩ | rfl <;>
    rcases seg4_cases k f hf with rfl | rfl | ⟨n, hn, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem sd_QR3 (k : ℕ) (e f : GInt × GInt)
    (he : e ∈ edgesFrom (2, 2 * (k : ℤ) + 4) (List.replicate (2 * k + 3) Unit4.negOne))
    (hf : f ∈ edgesFrom (2 - (2 * (k : ℤ) + 3), 2 * (k : ℤ) + 4)
      ([Unit4.negI, Unit4.negI] ++ (List.replicate (2 * k + 1) [Unit4.one, Unit4.negI]).flatten ++ [Unit4.negI])) :
    e.1 ≠ f.1 := by
  obtain ⟨m, hm, rfl⟩ := seg3_cases k e he
  intro heq
  rcases seg4_cases k f hf with rfl | rfl | ⟨n, hn, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem stairWord_starts_nodup (k : ℕ) : ((edgesFrom (0, 0) (stairWord k)).map Prod.fst).Nodup := by
  rw [stairWord_edges k]
  simp only [List.map_append]
  have h := starts_nodup_pos _ (2 * (k : ℤ) + 3, 0) (letters_W2C k)
  rw [edgesFrom_append, sum_w2_stair, start_p3] at h
  simp only [List.map_append] at h
  refine nodup_arcs ?_ h ?_ ?_ ?_ ?_
  · exact starts_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  · exact starts_nodup_neg _ _ (letters_W4 k)
  · intro a ha b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact cross_starts (fun e he f hf => sd_PQ2 k e f he hf) a ha b hb
    · exact cross_starts (fun e he f hf => sd_PQ3 k e f he hf) a ha b hb
  · intro a ha b hb
    exact cross_starts (fun e he f hf => sd_PR k e f he hf) a ha b hb
  · intro a ha b hb
    rcases List.mem_append.1 ha with ha | ha
    · exact cross_starts (fun e he f hf => sd_QR2 k e f he hf) a ha b hb
    · exact cross_starts (fun e he f hf => sd_QR3 k e f he hf) a ha b hb

/-! ### Edge-connectivity of the staircase cells -/

theorem stair_row0 (d : ℤ) (hd : 3 ≤ d) : ∀ n : ℕ, ∀ a : ℤ, a = 1 + (n : ℤ) → a ≤ d - 1 →
    Relation.ReflTransGen (fun x y : GInt => x ∈ stairCells d ∧ y ∈ stairCells d ∧ CellAdj x y)
      ((a, 0) : GInt) ((1, 0) : GInt) := by
  intro n
  induction n with
  | zero =>
    intro a ha _
    have h1 : a = 1 := by simpa using ha
    subst h1
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro a ha hA
    push_cast at ha
    refine Relation.ReflTransGen.head ⟨(mem_sc d hd a 0).2 ?_, (mem_sc d hd (a - 1) 0).2 ?_, adj_left a 0⟩
      (ih (a - 1) (by omega) (by omega))
    · unfold stairInT; omega
    · unfold stairInT; omega

theorem stair_rows (d : ℤ) (hd : 3 ≤ d) : ∀ n : ℕ, ∀ a b : ℤ, b = (n : ℤ) → stairInT d a b →
    Relation.ReflTransGen (fun x y : GInt => x ∈ stairCells d ∧ y ∈ stairCells d ∧ CellAdj x y)
      ((a, b) : GInt) ((1, 0) : GInt) := by
  intro n
  induction n with
  | zero =>
    intro a b hb hin
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    by_cases ha0 : a = 0
    · subst ha0
      exact Relation.ReflTransGen.single
        ⟨(mem_sc d hd 0 0).2 (by unfold stairInT; omega), (mem_sc d hd 1 0).2 (by unfold stairInT; omega),
          adj_right' 0 0 1 (by norm_num)⟩
    · unfold stairInT at hin
      have hA : a ≤ d - 1 := by
        rcases hin with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · omega
        · have h0 : (0 : ℤ) = d := h2
          omega
      have hnn : (0 : ℤ) ≤ a - 1 := by
        rcases hin with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · omega
        · have h0 : (0 : ℤ) = d := h2
          omega
      have hc := Int.toNat_of_nonneg hnn
      exact stair_row0 d hd (a - 1).toNat a (by rw [hc]; ring) hA
  | succ n ih =>
    intro a b hb hin
    push_cast at hb
    subst hb
    by_cases hs : 1 ≤ a + (n : ℤ)
    · refine Relation.ReflTransGen.head
        ⟨(mem_sc d hd a ((n : ℤ) + 1)).2 hin, (mem_sc d hd a n).2 ?_, adj_down' a ((n : ℤ) + 1) n (by ring)⟩
        (ih a n rfl ?_)
      · unfold stairInT at hin ⊢; omega
      · unfold stairInT at hin ⊢; omega
    · refine Relation.ReflTransGen.head
        ⟨(mem_sc d hd a ((n : ℤ) + 1)).2 hin, (mem_sc d hd (a + 1) ((n : ℤ) + 1)).2 ?_, adj_right a ((n : ℤ) + 1)⟩
        (Relation.ReflTransGen.head
          ⟨(mem_sc d hd (a + 1) ((n : ℤ) + 1)).2 ?_, (mem_sc d hd (a + 1) n).2 ?_,
            adj_down' (a + 1) ((n : ℤ) + 1) n (by ring)⟩
          (ih (a + 1) n rfl ?_))
      · unfold stairInT at hin ⊢; omega
      · unfold stairInT at hin ⊢; omega
      · unfold stairInT at hin ⊢; omega
      · unfold stairInT at hin ⊢; omega

theorem stair_conn (d : ℤ) (hd : 3 ≤ d) (x : GInt) (hx : x ∈ stairCells d) :
    Relation.ReflTransGen (fun x y : GInt => x ∈ stairCells d ∧ y ∈ stairCells d ∧ CellAdj x y) x ((1, 0) : GInt) := by
  obtain ⟨a, b⟩ := x
  rw [mem_sc d hd] at hx
  unfold stairInT at hx
  rcases hx with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h7, h8⟩ | ⟨h9, h10⟩
  · have hb : b = ((b.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    exact stair_rows d hd b.toNat a b hb (by unfold stairInT; omega)
  · obtain ⟨rfl, rfl⟩ := And.intro h7 h8
    exact Relation.ReflTransGen.single
      ⟨(mem_sc d hd 0 0).2 (by unfold stairInT; omega), (mem_sc d hd 1 0).2 (by unfold stairInT; omega),
        adj_right' 0 0 1 (by norm_num)⟩
  · have ha1 : a = 1 := h9
    have hb1 : b = d := h10
    rw [ha1, hb1]
    have hnn : (0 : ℤ) ≤ d - 1 := by omega
    have hc := Int.toNat_of_nonneg hnn
    refine Relation.ReflTransGen.head
      ⟨(mem_sc d hd 1 d).2 (by unfold stairInT; omega), (mem_sc d hd 1 (d - 1)).2 (by unfold stairInT; omega),
        adj_down' 1 d (d - 1) (by ring)⟩
      (stair_rows d hd (d - 1).toNat 1 (d - 1) (by omega) (by unfold stairInT; omega))

theorem stair_edgeConnected (d : ℤ) (hd : 3 ≤ d) : EdgeConnected (stairCells d) := by
  intro x hx y hy
  exact Relation.ReflTransGen.trans (stair_conn d hd x hx)
    (rtg_swap (fun a b h => ⟨h.2.1, h.1, cellAdj_symm h.2.2⟩) (stair_conn d hd y hy))

theorem stair_simple (k : ℕ) : IsSimpleTile (stairCells (2 * (k : ℤ) + 3)) := by
  refine ⟨⟨(0, 0), stairWord k, stairWord_boundary k, ?_⟩, stair_edgeConnected _ (by omega)⟩
  rw [walk_dropLast]
  exact stairWord_starts_nodup k

/-! ### The staircase base tile is an almost tiling -/

theorem stair_boundary_at (k : ℕ) :
    IsBoundaryWordAt (stairCells (2 * (k : ℤ) + 3)) (0, 0) (boundaryWordOf (gH (stairH k)) (gV (stairV k))) := by
  have h := stairWord_boundary k
  rw [← pseudoBoundaryWord_stair] at h
  exact h

/-- `prop:base_cases` (a) for the reciprocal staircase `d = 2k + 3`, from `almost_square_tiling`: the tile generates the
`(Σw₁ + i, Σw₂ - 1)`-regular almost tiling and its edge clause, given the two global inputs for this tile. -/
theorem stair_almost_tiling (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k)))) :
    IsRegularAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) ∧
      EdgeSharingClause (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))) :=
  almost_square_tiling (stair_simple k) (stair_boundary_at k) (stair_admissible k).1 (stair_admissible k).2 hF hG

/-- The same, with the lattice written as the paper's `L'(1/d)`. -/
theorem stair_almost_tiling_paper (k : ℕ)
    (hF : NoFirstCrossing (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k))))
    (hG : NoFarAdjacency (stairCells (2 * (k : ℤ) + 3)) (almostV₁ (gH (stairH k))) (almostV₂ (gV (stairV k)))) :
    IsAlmostTiling (stairCells (2 * (k : ℤ) + 3)) (paperLattice 1 (2 * (k : ℤ) + 3)) := by
  have h := (stair_almost_tiling k hF hG).1
  rw [IsRegularAlmostTiling, stair_lattice] at h
  exact h
theorem ladSD12 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX2 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF2 m b hb with rfl ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD13 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX3 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF3 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD14 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX4 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF4 m b hb with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD15 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX5 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF5 m b hb with rfl ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD16 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX6 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF6 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD17 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX1 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF1 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD23 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX3 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF2 m a ha with rfl; rcases ladF3 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD24 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX4 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF2 m a ha with rfl; rcases ladF4 m b hb with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD25 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX5 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF2 m a ha with rfl; rcases ladF5 m b hb with rfl ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD26 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX6 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF2 m a ha with rfl; rcases ladF6 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD27 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX2 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF2 m a ha with rfl; rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD34 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX4 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF4 m b hb with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD35 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX5 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF5 m b hb with rfl ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD36 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX6 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF6 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD37 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX3 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF3 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD45 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX5 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF5 m b hb with rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD46 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX6 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF6 m b hb with ⟨j, hj, rfl⟩ <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD47 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX4 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF4 m a ha with (rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl) | ⟨j, hj, rfl⟩ <;> rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD56 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX5 m) (hb : b ∈ ladX6 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF5 m a ha with rfl; rcases ladF6 m b hb with ⟨j, hj, rfl⟩ ;
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD57 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX5 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF5 m a ha with rfl; rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)

theorem ladSD67 (m : ℕ) (a b : GInt × GInt) (ha : a ∈ ladX6 m) (hb : b ∈ ladX7 m) :
    a.1 ≠ b.1 := by
  intro heq
  rcases ladF6 m a ha with ⟨j, hj, rfl⟩; rcases ladF7 m b hb with rfl | rfl | ⟨j, hj, rfl | rfl⟩ | rfl <;>
    (dsimp only at heq; simp only [Prod.mk.injEq] at heq; omega)


theorem ladderWord_starts_nodup (m : ℕ) : ((edgesFrom (0, 0) (ladderWord m)).map Prod.fst).Nodup := by
  have n1 : ((ladX1 m).map Prod.fst).Nodup :=
    starts_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  have n2 : ((ladX2 m).map Prod.fst).Nodup := starts_nodup_pos _ _ (fun x hx => by simp at hx; exact Or.inl hx)
  have n3 : ((ladX3 m).map Prod.fst).Nodup :=
    starts_nodup_neg _ _ (fun x hx => Or.inl (List.eq_of_mem_replicate hx))
  have n4 : ((ladX4 m).map Prod.fst).Nodup := starts_nodup_pos _ _ (letters_Q (2 * m + 1 + 1) (2 * m + 3))
  have n5 : ((ladX5 m).map Prod.fst).Nodup := starts_nodup_neg _ _ (fun x hx => by simp at hx; exact Or.inr hx)
  have n6 : ((ladX6 m).map Prod.fst).Nodup := starts_nodup_pos _ _ (fun x hx => Or.inr (List.eq_of_mem_replicate hx))
  have n7 : ((ladX7 m).map Prod.fst).Nodup := starts_nodup_neg _ _ (letters_S (2 * m + 1 + 1))

  have d12 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX2 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD12 m e f he hf)

  have d13 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX3 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD13 m e f he hf)

  have d14 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX4 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD14 m e f he hf)

  have d15 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX5 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD15 m e f he hf)

  have d16 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX6 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD16 m e f he hf)

  have d17 : ∀ a ∈ (ladX1 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD17 m e f he hf)

  have d23 : ∀ a ∈ (ladX2 m).map Prod.fst, ∀ b ∈ (ladX3 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD23 m e f he hf)

  have d24 : ∀ a ∈ (ladX2 m).map Prod.fst, ∀ b ∈ (ladX4 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD24 m e f he hf)

  have d25 : ∀ a ∈ (ladX2 m).map Prod.fst, ∀ b ∈ (ladX5 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD25 m e f he hf)

  have d26 : ∀ a ∈ (ladX2 m).map Prod.fst, ∀ b ∈ (ladX6 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD26 m e f he hf)

  have d27 : ∀ a ∈ (ladX2 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD27 m e f he hf)

  have d34 : ∀ a ∈ (ladX3 m).map Prod.fst, ∀ b ∈ (ladX4 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD34 m e f he hf)

  have d35 : ∀ a ∈ (ladX3 m).map Prod.fst, ∀ b ∈ (ladX5 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD35 m e f he hf)

  have d36 : ∀ a ∈ (ladX3 m).map Prod.fst, ∀ b ∈ (ladX6 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD36 m e f he hf)

  have d37 : ∀ a ∈ (ladX3 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD37 m e f he hf)

  have d45 : ∀ a ∈ (ladX4 m).map Prod.fst, ∀ b ∈ (ladX5 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD45 m e f he hf)

  have d46 : ∀ a ∈ (ladX4 m).map Prod.fst, ∀ b ∈ (ladX6 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD46 m e f he hf)

  have d47 : ∀ a ∈ (ladX4 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD47 m e f he hf)

  have d56 : ∀ a ∈ (ladX5 m).map Prod.fst, ∀ b ∈ (ladX6 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD56 m e f he hf)

  have d57 : ∀ a ∈ (ladX5 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD57 m e f he hf)

  have d67 : ∀ a ∈ (ladX6 m).map Prod.fst, ∀ b ∈ (ladX7 m).map Prod.fst, a ≠ b :=
    cross_starts (fun e he f hf => ladSD67 m e f he hf)

  have R6 : ((ladX6 m).map Prod.fst ++ (ladX7 m).map Prod.fst).Nodup := List.nodup_append.2 ⟨n6, n7, d67⟩
  have R5 : ((ladX5 m).map Prod.fst ++ ((ladX6 m).map Prod.fst ++ (ladX7 m).map Prod.fst)).Nodup :=
    List.nodup_append.2 ⟨n5, R6, cross_app d56 d57⟩
  have R4 := List.nodup_append.2 ⟨n4, R5, cross_app d45 (cross_app d46 d47)⟩
  have R3 := List.nodup_append.2 ⟨n3, R4, cross_app d34 (cross_app d35 (cross_app d36 d37))⟩
  have R2 := List.nodup_append.2 ⟨n2, R3, cross_app d23 (cross_app d24 (cross_app d25 (cross_app d26 d27)))⟩
  rw [ladderWord_edges]
  simp only [List.map_append]
  exact List.nodup_append.2 ⟨n1, R2, cross_app d12 (cross_app d13 (cross_app d14 (cross_app d15 (cross_app d16 d17))))⟩

/-! ### Edge-connectivity of the doubled staircase cells -/

/-- The cells of the ladder tile away from the two corner cells `(0,0)` and `(d+1,d+1)`. -/
def ladderC (d a b : ℤ) : Prop :=
  (-d + 2 ≤ a ∧ a ≤ 2 * d - 1 ∧ 0 ≤ b ∧ b ≤ d + 1 ∧ 1 ≤ a + b ∧ a + b ≤ 2 * d + 1) ∧
    (b ≠ 0 ∨ a ≤ d - 2) ∧ (b ≠ d + 1 ∨ 3 ≤ a)

theorem mem_ladC (d : ℤ) (hd : 4 ≤ d) (a b : ℤ) (h : ladderC d a b) : ((a, b) : GInt) ∈ ladderCells d :=
  (mem_ladderCells' d hd a b).2 (Or.inl h)

theorem ladder_row1 (d : ℤ) (hd : 4 ≤ d) : ∀ n : ℕ, ∀ a : ℤ, a = (n : ℤ) → a ≤ 2 * d - 1 →
    Relation.ReflTransGen (fun x y : GInt => x ∈ ladderCells d ∧ y ∈ ladderCells d ∧ CellAdj x y)
      ((a, 1) : GInt) ((0, 1) : GInt) := by
  intro n
  induction n with
  | zero =>
    intro a ha _
    have h0 : a = 0 := by simpa using ha
    subst h0
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro a ha hA
    push_cast at ha
    refine Relation.ReflTransGen.head
      ⟨mem_ladC d hd a 1 (by unfold ladderC; omega), mem_ladC d hd (a - 1) 1 (by unfold ladderC; omega),
        adj_left a 1⟩
      (ih (a - 1) (by omega) (by omega))

theorem ladder_rows (d : ℤ) (hd : 4 ≤ d) : ∀ n : ℕ, ∀ a b : ℤ, b = (n : ℤ) + 1 → ladderC d a b →
    Relation.ReflTransGen (fun x y : GInt => x ∈ ladderCells d ∧ y ∈ ladderCells d ∧ CellAdj x y)
      ((a, b) : GInt) ((0, 1) : GInt) := by
  intro n
  induction n with
  | zero =>
    intro a b hb hC
    have hb1 : b = 1 := by simpa using hb
    subst hb1
    have hn : (0 : ℤ) ≤ a := by unfold ladderC at hC; omega
    have hc := Int.toNat_of_nonneg hn
    exact ladder_row1 d hd a.toNat a hc.symm (by unfold ladderC at hC; omega)
  | succ n ih =>
    intro a b hb hC
    push_cast at hb
    subst hb
    by_cases hs : 1 ≤ a + ((n : ℤ) + 1)
    · have hC' : ladderC d a ((n : ℤ) + 1) := by unfold ladderC at hC ⊢; omega
      refine Relation.ReflTransGen.head
        ⟨mem_ladC d hd a ((n : ℤ) + 1 + 1) hC, mem_ladC d hd a ((n : ℤ) + 1) hC',
          adj_down' a ((n : ℤ) + 1 + 1) ((n : ℤ) + 1) (by ring)⟩
        (ih a ((n : ℤ) + 1) rfl hC')
    · have hC'' : ladderC d (a + 1) ((n : ℤ) + 1) := by unfold ladderC at hC ⊢; omega
      have hC2 : ladderC d (a + 1) ((n : ℤ) + 1 + 1) := by unfold ladderC at hC ⊢; omega
      refine Relation.ReflTransGen.head
        ⟨mem_ladC d hd a ((n : ℤ) + 1 + 1) hC, mem_ladC d hd (a + 1) ((n : ℤ) + 1 + 1) hC2,
          adj_right a ((n : ℤ) + 1 + 1)⟩
        (Relation.ReflTransGen.head
          ⟨mem_ladC d hd (a + 1) ((n : ℤ) + 1 + 1) hC2, mem_ladC d hd (a + 1) ((n : ℤ) + 1) hC'',
            adj_down' (a + 1) ((n : ℤ) + 1 + 1) ((n : ℤ) + 1) (by ring)⟩
          (ih (a + 1) ((n : ℤ) + 1) rfl hC''))

theorem ladder_conn (d : ℤ) (hd : 4 ≤ d) (x : GInt) (hx : x ∈ ladderCells d) :
    Relation.ReflTransGen (fun x y : GInt => x ∈ ladderCells d ∧ y ∈ ladderCells d ∧ CellAdj x y) x
      ((0, 1) : GInt) := by
  obtain ⟨a, b⟩ := x
  rw [mem_ladderCells' d hd] at hx
  unfold ladderInT at hx
  rcases hx with hC | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hC' : ladderC d a b := hC
    unfold ladderC at hC'
    by_cases hb0 : b = 0
    · subst hb0
      have ha1 : (0 : ℤ) ≤ a := by omega
      have hc := Int.toNat_of_nonneg ha1
      refine Relation.ReflTransGen.head
        ⟨mem_ladC d hd a 0 (by unfold ladderC; omega), mem_ladC d hd a 1 (by unfold ladderC; omega),
          adj_up' a 0 1 (by norm_num)⟩
        (ladder_row1 d hd a.toNat a hc.symm (by omega))
    · have hb1 : (0 : ℤ) ≤ b - 1 := by omega
      have hc := Int.toNat_of_nonneg hb1
      exact ladder_rows d hd (b - 1).toNat a b (by rw [hc]; ring) (by unfold ladderC; omega)
  · have ha : a = 0 := h1
    have hb : b = 0 := h2
    rw [ha, hb]
    exact Relation.ReflTransGen.single
      ⟨(mem_ladderCells' d hd 0 0).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        (mem_ladderCells' d hd 0 1).2 (Or.inl (by omega)), adj_up' 0 0 1 (by norm_num)⟩
  · have ha : a = d + 1 := h1
    have hb : b = d + 1 := h2
    rw [ha, hb]
    have hnn : (0 : ℤ) ≤ d - 1 := by omega
    have hc := Int.toNat_of_nonneg hnn
    refine Relation.ReflTransGen.head
      ⟨(mem_ladderCells' d hd (d + 1) (d + 1)).2 (Or.inr (Or.inr ⟨rfl, rfl⟩)),
        mem_ladC d hd (d + 1) d (by unfold ladderC; omega), adj_down' (d + 1) (d + 1) d (by ring)⟩
      (ladder_rows d hd (d - 1).toNat (d + 1) d (by rw [hc]; ring) (by unfold ladderC; omega))

theorem ladder_edgeConnected (d : ℤ) (hd : 4 ≤ d) : EdgeConnected (ladderCells d) := by
  intro x hx y hy
  exact Relation.ReflTransGen.trans (ladder_conn d hd x hx)
    (rtg_swap (fun a b h => ⟨h.2.1, h.1, cellAdj_symm h.2.2⟩) (ladder_conn d hd y hy))

theorem ladder_simple (m : ℕ) : IsSimpleTile (ladderCells (2 * (m : ℤ) + 4)) := by
  refine ⟨⟨(0, 0), ladderWord m, ladder_boundary m, ?_⟩, ladder_edgeConnected _ (by omega)⟩
  rw [walk_dropLast]
  exact ladderWord_starts_nodup m

/-! ### The doubled staircase base tile is an almost tiling -/

theorem ladder_boundary_at (m : ℕ) :
    IsBoundaryWordAt (ladderCells (2 * (m : ℤ) + 4)) (0, 0)
      (boundaryWordOf (gH (ladderH (m + 1))) (gV (ladderV (m + 1)))) := by
  have h := ladder_boundary m
  rw [← pseudoBoundaryWord_ladder] at h
  exact h

/-- `prop:base_cases` (a) for the doubled staircase `d = 2k + 2`, `k = m + 1`, from `almost_square_tiling`. -/
theorem ladder_almost_tiling (m : ℕ)
    (hF : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))))
    (hG : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1))))) :
    IsRegularAlmostTiling (ladderCells (2 * (m : ℤ) + 4))
        (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) ∧
      EdgeSharingClause (ladderCells (2 * (m : ℤ) + 4))
        (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))) :=
  almost_square_tiling (ladder_simple m) (ladder_boundary_at m)
    (by rw [gH_ladderH]; exact ladder_admissible_w1 m) (ladder_admissible_w2 m) hF hG

theorem ladder_almost_tiling_paper (m : ℕ)
    (hF : NoFirstCrossing (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1)))))
    (hG : NoFarAdjacency (ladderCells (2 * (m : ℤ) + 4))
      (almostV₁ (gH (ladderH (m + 1)))) (almostV₂ (gV (ladderV (m + 1))))) :
    IsAlmostTiling (ladderCells (2 * (m : ℤ) + 4)) (paperLattice 1 (2 * (m : ℤ) + 4)) := by
  have h := (ladder_almost_tiling m hF hG).1
  rw [IsRegularAlmostTiling, ladder_lattice] at h
  exact h

end FLatticePaper.Tiles
