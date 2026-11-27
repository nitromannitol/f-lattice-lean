import FLatticePaper.Tiles.ClosedWalkOdd
import FLatticePaper.Tiles.Gluing
import FLatticePaper.Tiles.DeckCoverage
import FLatticePaper.Tiles.StandardAll

/-! Gluing the translated odd odometers into one function on `Z^2` (step (1) of the surgical global odometers, the
standard case, odd child). The closed walks of the overlap graph of the translates have zero offset sum, so the translates
glue to a function `f` (`exists_compatible_iff_walkSum_eq_zero`). The overlap graph is connected, its unit steps being the
overlaps of `oddTile` with its translates (`oddTile_hA1h`, `oddTile_hA1v`). The translates cover `Z^2` through the modified
deck (`deck_covers_odd_all`). Then `compatible_unique` turns the two translation rules of `f` into constants. The covering
hypotheses H2 of the closed-walk theorems are inherited. -/

namespace FLatticePaper.Tiles

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.CommonExtFamily
  FLatticePaper.Tiles.CommonExtStandard FLatticePaper.Tiles.PointNonNeighbour FLatticePaper.Tiles.Standard
  FLatticePaper.Tiles.CommonExtWitness FLatticePaper.Tiles.CellDerivation

theorem glue_vP_e1 (v1 v2 : ℤ × ℤ) : vP v1 v2 (1, 0) = v1 := by
  ext <;> simp [vP]

theorem glue_vP_e2 (v1 v2 : ℤ × ℤ) : vP v1 v2 (0, 1) = v2 := by
  ext <;> simp [vP]

theorem glue_vP_zero (v1 v2 : ℤ × ℤ) : vP v1 v2 (0, 0) = 0 := by
  ext <;> simp [vP]

/-- A graph whose horizontal and vertical unit steps are edges is connected. -/
theorem glue_grid_connected (G : SimpleGraph (ℤ × ℤ)) (h1 : ∀ i j : ℤ, G.Adj (i, j) (i + 1, j))
    (h2 : ∀ i j : ℤ, G.Adj (i, j) (i, j + 1)) : G.Connected := by
  have hrow : ∀ i : ℤ, G.Reachable (0, 0) (i, 0) := by
    intro i
    induction i using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (h1 (n : ℤ) 0).reachable
    | pred n ih =>
      have e := h1 (-(n : ℤ) - 1) 0
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at e
      exact ih.trans e.reachable.symm
  have hcol : ∀ i j : ℤ, G.Reachable (i, 0) (i, j) := by
    intro i j
    induction j using Int.induction_on with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (h2 i (n : ℤ)).reachable
    | pred n ih =>
      have e := h2 i (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at e
      exact ih.trans e.reachable.symm
  have hall : ∀ p : ℤ × ℤ, G.Reachable (0, 0) p := fun p => (hrow p.1).trans (hcol p.1 p.2)
  exact ⟨fun u v => (hall u).symm.trans (hall v)⟩

/-- Shifting the base point by `(1,0)` and the argument by `v₁` changes the translated odometer by `a_p · v₁`
(the affine factor `a₁` is zero). -/
theorem glue_famOf_e1 (o : ℤ × ℤ → ℤ) (v1 v2 a2 p x : ℤ × ℤ) :
    famOf o v1 v2 (0, 0) a2 (p + (1, 0)) (x + v1) - famOf o v1 v2 (0, 0) a2 p x =
      dotZ (aP (0, 0) a2 p) v1 := by
  have harg : x + v1 - vP v1 v2 (p + (1, 0)) = x - vP v1 v2 p := by
    rw [vP_add, glue_vP_e1]
    abel
  have haP : aP (0, 0) a2 (p + (1, 0)) = aP (0, 0) a2 p := by
    rw [aP_add, aP_e1]
    ext <;> simp
  unfold famOf
  rw [harg, haP, dotZ_add_right]
  ring

/-- Shifting the base point by `(0,1)` and the argument by `v₂` changes the translated odometer by
`a_p · v₂ + a₂ · x + a₂ · v₂`. -/
theorem glue_famOf_e2 (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 p x : ℤ × ℤ) :
    famOf o v1 v2 a1 a2 (p + (0, 1)) (x + v2) - famOf o v1 v2 a1 a2 p x =
      dotZ (aP a1 a2 p) v2 + dotZ a2 x + dotZ a2 v2 := by
  have harg : x + v2 - vP v1 v2 (p + (0, 1)) = x - vP v1 v2 p := by
    rw [vP_add, glue_vP_e2]
    abel
  have haP : aP a1 a2 (p + (0, 1)) = aP a1 a2 p + a2 := by
    rw [aP_add, aP_e2]
  unfold famOf
  rw [harg, haP, dotZ_add_left, dotZ_add_right, dotZ_add_right]
  ring

theorem glue_famOf_zero (o : ℤ × ℤ → ℤ) (v1 v2 a1 a2 x : ℤ × ℤ) :
    famOf o v1 v2 a1 a2 (0, 0) x = o x := by
  have h0 : aP a1 a2 (0, 0) = (0, 0) := by
    ext <;> simp [aP]
  unfold famOf
  rw [glue_vP_zero, sub_zero, h0]
  simp [dotZ]

/-- The glued function, from closed walks and connectivity, with its two translation rules. -/
theorem glue_core (T : Set (ℤ × ℤ)) (o : ℤ × ℤ → ℤ) (n d : ℤ) (v1 v2 a1 a2 : ℤ × ℤ) (κ : ℤ × ℤ → ℤ)
    (hκ : ∀ d' y : ℤ × ℤ, y ∈ T → y - vP v1 v2 d' ∈ T →
      o y - (o (y - vP v1 v2 d') + dotZ (aP a1 a2 d') y) = κ d')
    (hA1h : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i + 1, j))
    (hA1v : ∀ i j : ℤ, ∃ x, x ∈ dom T v1 v2 (i, j) ∧ x ∈ dom T v1 v2 (i, j + 1))
    (hA2 : ∀ x y : ℤ × ℤ, (overlapGraph (dom T v1 v2)).Adj x y →
      (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
        (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1))
    (ha1 : a1 = (0, 0)) (ha2 : a2 = (n, -d)) (hv1 : v1 = (d, n) ∨ v1 = (2 * d, 2 * n))
    (hcover : ∀ x : ℤ × ℤ, ∃ i : ℤ × ℤ, x ∈ dom T v1 v2 i) :
    ∃ f : ℤ × ℤ → ℤ, (∃ c : ℤ, ∀ x ∈ T, f x = o x + c) ∧
      (∃ c1 : ℤ, ∀ x : ℤ × ℤ, f (x + v1) = f x + c1) ∧
      (∃ c2 : ℤ, ∀ x : ℤ × ℤ, f (x + v2) = f x + dotZ a2 x + c2) := by
  subst ha1
  have hw : ∀ (i : ℤ × ℤ) (walk : (overlapGraph (dom T v1 v2)).Walk i i),
      walkSum (offFam κ v1 v2 (0, 0) a2) walk = 0 :=
    fun i walk => family_closed_walks_zero_paper T o n d v1 v2 (0, 0) a2 κ hκ hA1h hA1v hA2 rfl ha2 hv1 i walk
  have hconn : (overlapGraph (dom T v1 v2)).Connected := by
    refine glue_grid_connected _ (fun i j => ?_) (fun i j => ?_)
    · obtain ⟨x, hx1, hx2⟩ := hA1h i j
      show (i, j) ≠ (i + 1, j) ∧ (dom T v1 v2 (i, j) ∩ dom T v1 v2 (i + 1, j)).Nonempty
      exact ⟨fun e => by have := congrArg Prod.fst e; simp at this, ⟨x, hx1, hx2⟩⟩
    · obtain ⟨x, hx1, hx2⟩ := hA1v i j
      show (i, j) ≠ (i, j + 1) ∧ (dom T v1 v2 (i, j) ∩ dom T v1 v2 (i, j + 1)).Nonempty
      exact ⟨fun e => by have := congrArg Prod.snd e; simp at this, ⟨x, hx1, hx2⟩⟩
  have hoff : ∀ i j : ℤ × ℤ, ∀ x ∈ dom T v1 v2 i ∩ dom T v1 v2 j,
      famOf o v1 v2 (0, 0) a2 i x - famOf o v1 v2 (0, 0) a2 j x = offFam κ v1 v2 (0, 0) a2 i j :=
    fun i j x hx => famOf_sub_eq_offFam T o v1 v2 (0, 0) a2 κ hκ i j x hx.1 hx.2
  obtain ⟨f, hfc⟩ := (exists_compatible_iff_walkSum_eq_zero (dom T v1 v2) (famOf o v1 v2 (0, 0) a2)
    (offFam κ v1 v2 (0, 0) a2) hcover hconn hoff).2 hw
  have hmem1 : ∀ (q x : ℤ × ℤ), x ∈ dom T v1 v2 q → x + v1 ∈ dom T v1 v2 (q + (1, 0)) := by
    intro q x hx
    show x + v1 - vP v1 v2 (q + (1, 0)) ∈ T
    have e : x + v1 - vP v1 v2 (q + (1, 0)) = x - vP v1 v2 q := by
      rw [vP_add, glue_vP_e1]
      abel
    rw [e]
    exact hx
  have hmem2 : ∀ (q x : ℤ × ℤ), x ∈ dom T v1 v2 q → x + v2 ∈ dom T v1 v2 (q + (0, 1)) := by
    intro q x hx
    show x + v2 - vP v1 v2 (q + (0, 1)) ∈ T
    have e : x + v2 - vP v1 v2 (q + (0, 1)) = x - vP v1 v2 q := by
      rw [vP_add, glue_vP_e2]
      abel
    rw [e]
    exact hx
  have hg1 : ∀ q : ℤ × ℤ, ∃ c : ℤ, ∀ x ∈ dom T v1 v2 q,
      f (x + v1) - famOf o v1 v2 (0, 0) a2 q x = c := by
    intro q
    obtain ⟨c', hc'⟩ := hfc (q + (1, 0))
    refine ⟨c' + dotZ (aP (0, 0) a2 q) v1, fun x hx => ?_⟩
    have h1 := hc' (x + v1) (hmem1 q x hx)
    have h2 := glue_famOf_e1 o v1 v2 a2 q x
    linarith
  have hg2 : ∀ q : ℤ × ℤ, ∃ c : ℤ, ∀ x ∈ dom T v1 v2 q,
      f (x + v2) - dotZ a2 x - famOf o v1 v2 (0, 0) a2 q x = c := by
    intro q
    obtain ⟨c', hc'⟩ := hfc (q + (0, 1))
    refine ⟨c' + dotZ (aP (0, 0) a2 q) v2 + dotZ a2 v2, fun x hx => ?_⟩
    have h1 := hc' (x + v2) (hmem2 q x hx)
    have h2 := glue_famOf_e2 o v1 v2 (0, 0) a2 q x
    linarith
  obtain ⟨c1, hc1⟩ := compatible_unique (dom T v1 v2) (famOf o v1 v2 (0, 0) a2) hcover hconn hfc
    (f := f) (g := fun x => f (x + v1)) (fun q => hg1 q)
  obtain ⟨c2, hc2⟩ := compatible_unique (dom T v1 v2) (famOf o v1 v2 (0, 0) a2) hcover hconn hfc
    (f := f) (g := fun x => f (x + v2) - dotZ a2 x) (fun q => hg2 q)
  have key1 : ∀ x : ℤ × ℤ, f x = f (x + v1) + c1 := hc1
  have key2 : ∀ x : ℤ × ℤ, f x = f (x + v2) - dotZ a2 x + c2 := hc2
  refine ⟨f, ?_, ⟨-c1, fun x => by linarith [key1 x]⟩, ⟨-c2, fun x => by linarith [key2 x]⟩⟩
  obtain ⟨c0, hc0⟩ := hfc (0, 0)
  refine ⟨c0, fun x hx => ?_⟩
  have hx0 : x ∈ dom T v1 v2 (0, 0) := by
    show x - vP v1 v2 (0, 0) ∈ T
    rw [glue_vP_zero, sub_zero]
    exact hx
  have h0 := hc0 x hx0
  rw [glue_famOf_zero] at h0
  linarith

/-- Every site lies in a translate of the odd standard tile (the modified deck covers the tile). -/
theorem odd_cover (w : Word) :
    ∀ x : ℤ × ℤ, ∃ i : ℤ × ℤ, x ∈ dom (↑(oddTile w) : Set (ℤ × ℤ)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) i := by
  intro x
  obtain ⟨rep, hrep, hspan⟩ := FLatticePaper.Tiles.StandardAll.deck_covers_odd_all w x
  obtain ⟨k, k', hk⟩ := hspan
  have hkern : (fracOdd w).modifiedDeck.kernel = texV1Odd (fracOdd w) :=
    FLatticePaper.Tiles.DeckCoverage.modifiedDeck_kernel_of_odd (parentsAt_valid w).current_odd_parity
  have hvP : vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (k, k') =
      PeriodDeck.combine (fracOdd w).modifiedDeck k k' := by
    simp only [PeriodDeck.combine, vP, hkern]
    rfl
  refine ⟨(k, k'), ?_⟩
  show x - vP (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) (k, k') ∈ (↑(oddTile w) : Set (ℤ × ℤ))
  have e : x - PeriodDeck.combine (fracOdd w).modifiedDeck k k' = rep := by
    rw [← hk]
    exact sub_sub_cancel x rep
  rw [hvP, e, Finset.mem_coe]
  exact hrep

/-- The glued odd odometer: a function on `Z^2` extending the odd odometer on its tile up to a constant, with the two
translation rules of the modified deck of `fracOdd w`. The covering hypotheses H2 are inherited from the closed walks. -/
theorem odd_glue (S : FLatticePaper.Tiles.SurgicalWeak.WeakData)
    (oddO evenO : FLatticePaper.Farey.Word → PartialOdometer)
    (h : FLatticePaper.Tiles.SurgicalWeak.IsWeakStdFamily S oddO evenO) (w : FLatticePaper.Farey.Word)
    (H2X_v : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z →
      tileCovers (vStringAt (vWordOf w false) (lastPosOf (hStringAt (hWordOf w false) 0))) z)
    (H2Y_v : ∀ z, BoundaryVertex ({t : GInt | t - texV1Odd (fracOdd w) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      tileCovers (vRevStringAt (vWordOf w false).reverse (texV1Odd (fracOdd w))) z)
    (H2X_h : ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z →
      tileCovers (hStringAt (hWordOf w false) 0) z)
    (H2Y_h : ∀ z, BoundaryVertex ({t : GInt | t - (-texV2 (fracOdd w)) ∈ cellTileOf (oddTile w)} : Set GInt) z →
      tileCovers (hRevStringAt (hWordOf w false).reverse (1, -2)) z) :
    ∃ f : ℤ × ℤ → ℤ, (∃ c : ℤ, ∀ x ∈ (↑(oddTile w) : Set (ℤ × ℤ)), f x = (oddO w).val x + c) ∧
      (∃ c1 : ℤ, ∀ x : ℤ × ℤ, f (x + texV1Odd (fracOdd w)) = f x + c1) ∧
      (∃ c2 : ℤ, ∀ x : ℤ × ℤ, f (x + texV2 (fracOdd w)) =
        f x + dotZ ((fracOdd w).num, -(fracOdd w).den) x + c2) := by
  obtain ⟨κ, hκ⟩ := odd_hkappa S oddO evenO h w H2X_v H2Y_v H2X_h H2Y_h
  exact glue_core (↑(oddTile w)) (oddO w).val (fracOdd w).num (fracOdd w).den (texV1Odd (fracOdd w))
    (texV2 (fracOdd w)) (0, 0) ((fracOdd w).num, -(fracOdd w).den) κ hκ (oddTile_hA1h w) (oddTile_hA1v w)
    (oddTile_hA2 w) rfl rfl (Or.inr rfl) (odd_cover w)

end FLatticePaper.Tiles
