import FLatticePaper.Tiles.PTAffineTransport

/-! Uniqueness of a respecting family up to one common affine function (the (B) step of the hκ bridge).

Two families `F`, `G` on the same tile list respecting the same string differ by a common affine function, provided every
pair of consecutive tiles has a non-overlapping unit-apart pair of sites (`hadj`, the geometric input of the boundary clause:
`Respects` only constrains unit-apart pairs of non-overlapping consecutive tiles). The slope clause makes the slope factor
`a_{k+1} - a_k` the same for `F` and `G`; the boundary clause then makes the constant `b_{k+1} - b_k` the same. -/

namespace FLatticePaper.Tiles

theorem PTFamily.tile_eq_of_ts (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) : G.tile k = F.tile k := by
  unfold PTFamily.tile
  rw [hts]

theorem PTFamily.dom_eq_of_ts (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) : G.dom k = F.dom k := by
  unfold PTFamily.dom
  rw [PTFamily.tile_eq_of_ts F G hts k]

theorem PTFamily.n_eq_of_ts (F G : PTFamily) (hts : G.ts = F.ts) : G.n = F.n := by
  unfold PTFamily.n
  rw [hts]

/-- The odometers of two families on the same tile list differ by the affine function `δ_k · x + d_k`. -/
theorem PTFamily.odo_sub_affine (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) (x : GInt) :
    G.odo k x = F.odo k x + (G.a k - F.a k).1 * x.1 + (G.a k - F.a k).2 * x.2 + (G.b k - F.b k) := by
  unfold PTFamily.odo
  rw [PTFamily.tile_eq_of_ts F G hts k]
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The slope of `G`'s odometer is the slope of `F`'s, shifted by the slope factor difference. -/
theorem PTFamily.slopeOf_odo_sub (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) :
    slopeOf (G.odo k) (F.dom k) =
      slopeOf (F.odo k) (F.dom k) + (((G.a k - F.a k).1 : ℚ), ((G.a k - F.a k).2 : ℚ)) := by
  have hfun : G.odo k = fun x => F.odo k x + (G.a k - F.a k).1 * x.1 + (G.a k - F.a k).2 * x.2 + (G.b k - F.b k) :=
    funext (PTFamily.odo_sub_affine F G hts k)
  rw [hfun]
  exact slopeOf_affineAdd (F.odo k) (F.dom k) (G.a k - F.a k) (G.b k - F.b k) (F.dom_unitSquares_ne k)

/-- The odometer of `G` minus its dot product with its own factor equals the same quantity for `F`, plus the constant difference. -/
theorem PTFamily.val_sub_dot (F G : PTFamily) (hts : G.ts = F.ts) (k : ℕ) (x : GInt) :
    G.odo k x - ptDot (G.a k) x = F.odo k x - ptDot (F.a k) x + (G.b k - F.b k) := by
  rw [PTFamily.odo_sub_affine F G hts k x]
  unfold ptDot
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The slope clause pins the slope factor: `δ_{k+1} = δ_k`. -/
theorem PTFamily.delta_step (o : Orientation) (rev : Bool) (F G : PTFamily) (hts : G.ts = F.ts)
    (hF : F.Respects o rev) (hG : G.Respects o rev) (k : ℕ) (hk : k + 1 < F.n) :
    G.a (k + 1) - F.a (k + 1) = G.a k - F.a k := by
  have hkG : k + 1 < G.n := by
    rw [PTFamily.n_eq_of_ts F G hts]
    exact hk
  have hF1 := (hF k hk).1
  have hG1 := (hG k hkG).1
  simp only [PTFamily.dom_eq_of_ts F G hts, PTFamily.tile_eq_of_ts F G hts] at hG1
  rw [PTFamily.slopeOf_odo_sub F G hts (k + 1), PTFamily.slopeOf_odo_sub F G hts k] at hG1
  have h := hG1.trans hF1.symm
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add] at h1 h2
  have e1 : ((((G.a (k + 1)).1 - (F.a (k + 1)).1 : ℤ)) : ℚ) = (((G.a k).1 - (F.a k).1 : ℤ) : ℚ) := by linarith
  have e2 : ((((G.a (k + 1)).2 - (F.a (k + 1)).2 : ℤ)) : ℚ) = (((G.a k).2 - (F.a k).2 : ℤ) : ℚ) := by linarith
  exact Prod.ext (by simp only [Prod.fst_sub]; exact_mod_cast e1) (by simp only [Prod.snd_sub]; exact_mod_cast e2)

/-- The boundary clause pins the constant: `d_{k+1} = d_k`, given the unit-apart non-overlapping pair `x`, `y`. -/
theorem PTFamily.b_step (o : Orientation) (rev : Bool) (F G : PTFamily) (hts : G.ts = F.ts)
    (hF : F.Respects o rev) (hG : G.Respects o rev) (k : ℕ) (hk : k + 1 < F.n)
    (hδ : G.a (k + 1) - F.a (k + 1) = G.a k - F.a k)
    (hno : ¬ ∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) (x y : GInt) (hx : x ∈ F.dom k) (hy : y ∈ F.dom (k + 1))
    (hu : unitApart x y) :
    G.b (k + 1) - F.b (k + 1) = G.b k - F.b k := by
  have hkG : k + 1 < G.n := by
    rw [PTFamily.n_eq_of_ts F G hts]
    exact hk
  have hnoG : ¬ ∃ x, x ∈ G.dom k ∧ x ∈ G.dom (k + 1) := by
    simp only [PTFamily.dom_eq_of_ts F G hts]
    exact hno
  have hxG : x ∈ G.dom k := by
    rw [PTFamily.dom_eq_of_ts F G hts]
    exact hx
  have hyG : y ∈ G.dom (k + 1) := by
    rw [PTFamily.dom_eq_of_ts F G hts]
    exact hy
  have hFc := (hF k hk).2 hno x hx y hy hu
  have hGc := (hG k hkG).2 hnoG x hxG y hyG hu
  -- the dot-product difference across the index k to k+1, for the point y
  have hdot : ptDot (G.a (k + 1)) y - ptDot (G.a k) y = ptDot (F.a (k + 1)) y - ptDot (F.a k) y := by
    have e1 : (G.a (k + 1)).1 - (G.a k).1 = (F.a (k + 1)).1 - (F.a k).1 := by
      have := congrArg Prod.fst hδ
      simp only [Prod.fst_sub] at this
      linarith
    have e2 : (G.a (k + 1)).2 - (G.a k).2 = (F.a (k + 1)).2 - (F.a k).2 := by
      have := congrArg Prod.snd hδ
      simp only [Prod.snd_sub] at this
      linarith
    unfold ptDot
    have f1 : (G.a (k + 1)).1 * y.1 - (G.a k).1 * y.1 = (F.a (k + 1)).1 * y.1 - (F.a k).1 * y.1 := by
      rw [← sub_mul, ← sub_mul, e1]
    have f2 : (G.a (k + 1)).2 * y.2 - (G.a k).2 * y.2 = (F.a (k + 1)).2 * y.2 - (F.a k).2 * y.2 := by
      rw [← sub_mul, ← sub_mul, e2]
    linarith
  have hk1 := PTFamily.val_sub_dot F G hts (k + 1) y
  have hk0 := PTFamily.val_sub_dot F G hts k x
  cases o with
  | horizontal =>
    have hFh := hFc.1 rfl
    have hGh := hGc.1 rfl
    linarith
  | vertical =>
    have hFv := hFc.2 rfl
    have hGv := hGc.2 rfl
    linarith

/-- **Uniqueness up to a common affine function.** If `G` and `F` respect the same string on the same tile list, and each
consecutive pair of tiles has a non-overlapping unit-apart pair of sites, then `G` is `F` plus one affine function on all
odometers. -/
theorem PTFamily.exists_affine_of_respects (o : Orientation) (rev : Bool) (F G : PTFamily) (hts : G.ts = F.ts)
    (hF : F.Respects o rev) (hG : G.Respects o rev)
    (hadj : ∀ k, k + 1 < F.n → (¬ ∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∧
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y) :
    ∃ (a : GInt) (c : ℤ), ∀ k < F.n, ∀ x : GInt,
      G.odo k x = F.odo k x + a.1 * x.1 + a.2 * x.2 + c := by
  have hδ : ∀ k, k + 1 < F.n → G.a (k + 1) - F.a (k + 1) = G.a k - F.a k :=
    fun k hk => PTFamily.delta_step o rev F G hts hF hG k hk
  have hbs : ∀ k, k + 1 < F.n → G.b (k + 1) - F.b (k + 1) = G.b k - F.b k := by
    intro k hk
    obtain ⟨hno, x, hx, y, hy, hu⟩ := hadj k hk
    exact PTFamily.b_step o rev F G hts hF hG k hk (hδ k hk) hno x y hx hy hu
  have main : ∀ k, k < F.n → G.a k - F.a k = G.a 0 - F.a 0 ∧ G.b k - F.b k = G.b 0 - F.b 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨(hδ k hk).trans h1, (hbs k hk).trans h2⟩
  refine ⟨G.a 0 - F.a 0, G.b 0 - F.b 0, fun k hk x => ?_⟩
  rw [PTFamily.odo_sub_affine F G hts k x, (main k hk).1, (main k hk).2]

/-- The boundary step, with the overlap case: if the consecutive tiles overlap at `x`, the `WithinCommon` agreement of
both families (the odometers of `F` and `G` agree at the common point) fixes `d_{k+1} = d_k`; otherwise the boundary
clause of `Respects` applies to a unit-apart pair. -/
theorem PTFamily.b_step_gen (o : Orientation) (rev : Bool) (F G : PTFamily) (hts : G.ts = F.ts)
    (hF : F.Respects o rev) (hG : G.Respects o rev)
    (hWF : ∀ k < F.n, ∀ j < F.n, ∀ x ∈ F.dom k, x ∈ F.dom j → F.odo k x = F.odo j x)
    (hWG : ∀ k < G.n, ∀ j < G.n, ∀ x ∈ G.dom k, x ∈ G.dom j → G.odo k x = G.odo j x)
    (k : ℕ) (hk : k + 1 < F.n)
    (hδ : G.a (k + 1) - F.a (k + 1) = G.a k - F.a k)
    (hadj : (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y) :
    G.b (k + 1) - F.b (k + 1) = G.b k - F.b k := by
  by_cases hov : ∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)
  · obtain ⟨x, hx, hx1⟩ := hov
    have hkG : k + 1 < G.n := by
      rw [PTFamily.n_eq_of_ts F G hts]
      exact hk
    have hF' : F.odo k x = F.odo (k + 1) x := hWF k (by omega) (k + 1) hk x hx hx1
    have hxG : x ∈ G.dom k := by
      rw [PTFamily.dom_eq_of_ts F G hts]
      exact hx
    have hx1G : x ∈ G.dom (k + 1) := by
      rw [PTFamily.dom_eq_of_ts F G hts]
      exact hx1
    have hG' : G.odo k x = G.odo (k + 1) x := hWG k (by omega) (k + 1) hkG x hxG hx1G
    have e0 := PTFamily.odo_sub_affine F G hts k x
    have e1 := PTFamily.odo_sub_affine F G hts (k + 1) x
    rw [hδ] at e1
    linarith
  · obtain ⟨x, hx, y, hy, hu⟩ := hadj.resolve_left hov
    exact PTFamily.b_step o rev F G hts hF hG k hk hδ hov x y hx hy hu

/-- **Uniqueness up to a common affine function, with the overlap case.** If `F` and `G` respect the same string on the same
tile list, both are `WithinCommon` (they agree on overlaps of their own domains), and each consecutive pair of tiles either
overlaps or has a unit-apart pair of sites, then `G` is `F` plus one affine function on all odometers. -/
theorem PTFamily.exists_affine_of_respects_gen (o : Orientation) (rev : Bool) (F G : PTFamily) (hts : G.ts = F.ts)
    (hF : F.Respects o rev) (hG : G.Respects o rev)
    (hWF : ∀ k < F.n, ∀ j < F.n, ∀ x ∈ F.dom k, x ∈ F.dom j → F.odo k x = F.odo j x)
    (hWG : ∀ k < G.n, ∀ j < G.n, ∀ x ∈ G.dom k, x ∈ G.dom j → G.odo k x = G.odo j x)
    (hadj : ∀ k, k + 1 < F.n → (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y) :
    ∃ (a : GInt) (c : ℤ), ∀ k < F.n, ∀ x : GInt,
      G.odo k x = F.odo k x + a.1 * x.1 + a.2 * x.2 + c := by
  have hδ : ∀ k, k + 1 < F.n → G.a (k + 1) - F.a (k + 1) = G.a k - F.a k :=
    fun k hk => PTFamily.delta_step o rev F G hts hF hG k hk
  have hbs : ∀ k, k + 1 < F.n → G.b (k + 1) - F.b (k + 1) = G.b k - F.b k :=
    fun k hk => PTFamily.b_step_gen o rev F G hts hF hG hWF hWG k hk (hδ k hk) (hadj k hk)
  have main : ∀ k, k < F.n → G.a k - F.a k = G.a 0 - F.a 0 ∧ G.b k - F.b k = G.b 0 - F.b 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      exact ⟨(hδ k hk).trans h1, (hbs k hk).trans h2⟩
  refine ⟨G.a 0 - F.a 0, G.b 0 - F.b 0, fun k hk x => ?_⟩
  rw [PTFamily.odo_sub_affine F G hts k x, (main k hk).1, (main k hk).2]

end FLatticePaper.Tiles
