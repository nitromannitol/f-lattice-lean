import FLatticePaper.Tiles.HorizontalMoreoverProof

/-! # `PTFamily.Respects` from recursive per-triple data

A family is *recursively determined* by letters `ℓ` and `prev` (the letter before tile `k`, with `prev (k+1) = ℓ k`) when:
* tile `k` has type `Tt (prev k) (ℓ k)` (it may depend on the previous and the current letter, e.g. an enlarged tile);
* positions step by `D (ℓ k) (ℓ (k+1))`: `P (k+1) = P k + D (ℓ k) (ℓ (k+1))`;
* affine factors step by `γ (prev k) (ℓ k) (ℓ (k+1))`: `a (k+1) = a k + γ (prev k) (ℓ k) (ℓ (k+1))`;
* centred constants `c k` (with `b k = c k - ptDot (a k) (P k)`) step by
  `c (k+1) = c k + β (prev k) (ℓ k) (ℓ (k+1)) + ptDot (a k) (D (ℓ k) (ℓ (k+1)))`.

Then `Respects` reduces to per-triple facts for the triples `(prev k, ℓ k, ℓ (k+1))` that occur (the predicate `Adm`): the slope
table, and the horizontal (`hH`) or vertical (`hV`) boundary identity for consecutive non-overlapping tiles.

`PTFamily.respects_of_letters` is the special case `Tt x y = letterZTile y`, `a k = α (ℓ k)`, `c k = c (ℓ k)`. -/

namespace FLatticePaper.Tiles

theorem tileShape_unitSquares_ne_zt (T : ZTile) : unitSquares (tileShape T) ≠ [] := by
  cases T <;> decide

/-- The slope of a placed odometer of any tile type: the base slope of its tile, plus its affine factor. -/
theorem slope_odo_zt (F : PTFamily) (k : ℕ) (T : ZTile) (p : GInt) (htile : F.tile k = (T, p)) :
    slopeOf (F.odo k) (F.dom k) =
      slopeOf (zTileOdo T) (tileShape T) + (((F.a k).1 : ℚ), ((F.a k).2 : ℚ)) := by
  have hodo : F.odo k = fun x => zTileOdo T (x - p) + dotS (F.a k) x + F.b k := by
    funext x
    unfold PTFamily.odo dotS
    rw [htile]
    dsimp only
    ring
  have hdom : F.dom k = (tileShape T).map (· + p) := by
    unfold PTFamily.dom; rw [htile]
  have hT : unitSquares ((tileShape T).map (· + p)) ≠ [] := by
    rw [unitSquares_map_add]
    intro h
    exact tileShape_unitSquares_ne_zt T (List.map_eq_nil_iff.mp h)
  rw [hodo, hdom, slopeOf_affine _ _ _ _ hT, slopeOf_translate]

theorem PTFamily.mem_dom_of_tile (F : PTFamily) (ℓ : ℕ → Letter) (P : ℕ → GInt)
    (hT : ∀ k < F.n, F.tile k = (letterZTile (ℓ k), P k)) (k : ℕ) (hk : k < F.n) (x : GInt) :
    x ∈ F.dom k ↔ ∃ u ∈ tileShape (letterZTile (ℓ k)), u + P k = x := by
  unfold PTFamily.dom
  rw [hT k hk]
  simp only [List.mem_map]

theorem PTFamily.odo_of_letters (F : PTFamily) (ℓ : ℕ → Letter) (P : ℕ → GInt) (α : Letter → GInt) (c : Letter → ℤ)
    (hT : ∀ k < F.n, F.tile k = (letterZTile (ℓ k), P k))
    (hA : ∀ k < F.n, F.a k = α (ℓ k))
    (hB : ∀ k < F.n, F.b k = c (ℓ k) - ptDot (α (ℓ k)) (P k))
    (k : ℕ) (hk : k < F.n) (x : GInt) :
    F.odo k x = zTileOdo (letterZTile (ℓ k)) (x - P k) + ptDot (α (ℓ k)) (x - P k) + c (ℓ k) := by
  unfold PTFamily.odo
  rw [hT k hk, hA k hk, hB k hk]
  simp only [ptDot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem PTFamily.slope_of_letters (F : PTFamily) (ℓ : ℕ → Letter) (P : ℕ → GInt) (α : Letter → GInt)
    (hT : ∀ k < F.n, F.tile k = (letterZTile (ℓ k), P k))
    (hA : ∀ k < F.n, F.a k = α (ℓ k)) (k : ℕ) (hk : k < F.n) :
    slopeOf (F.odo k) (F.dom k) =
      slopeOf (zTileOdo (letterZTile (ℓ k))) (tileShape (letterZTile (ℓ k)))
        + (((α (ℓ k)).1 : ℚ), ((α (ℓ k)).2 : ℚ)) := by
  rw [slope_odo_zt F k (letterZTile (ℓ k)) (P k) (hT k hk), hA k hk]

/-- The general lemma: a recursively determined family respects its string, given the per-triple slope table and the per-triple
boundary identities (horizontal `hH`, vertical `hV`) for the admissible triples. The boundary quantity
`zTileOdo (Tt x y) u - zTileOdo (Tt y z) v - ptDot (γ x y z) v` is `β x y z` (horizontal) or `β x y z + 1` (vertical). -/
theorem PTFamily.respects_of_triples (F : PTFamily) (o : Orientation) (rev : Bool)
    (ℓ prev : ℕ → Letter) (P : ℕ → GInt) (Tt : Letter → Letter → ZTile)
    (D : Letter → Letter → GInt) (γ : Letter → Letter → Letter → GInt) (c : ℕ → ℤ)
    (β : Letter → Letter → Letter → ℤ) (Adm : Letter → Letter → Letter → Prop)
    (hT : ∀ k < F.n, F.tile k = (Tt (prev k) (ℓ k), P k))
    (hprev : ∀ k, k + 1 < F.n → prev (k + 1) = ℓ k)
    (hD : ∀ k, k + 1 < F.n → P (k + 1) = P k + D (ℓ k) (ℓ (k + 1)))
    (hAa : ∀ k, k + 1 < F.n → F.a (k + 1) = F.a k + γ (prev k) (ℓ k) (ℓ (k + 1)))
    (hB : ∀ k < F.n, F.b k = c k - ptDot (F.a k) (P k))
    (hc : ∀ k, k + 1 < F.n →
      c (k + 1) = c k + β (prev k) (ℓ k) (ℓ (k + 1)) + ptDot (F.a k) (D (ℓ k) (ℓ (k + 1))))
    (hAdm : ∀ k, k + 1 < F.n → Adm (prev k) (ℓ k) (ℓ (k + 1)))
    (hTL : ∀ x y, zTileLetter (Tt x y) = y)
    (hslope : ∀ x y z, Adm x y z →
      slopeOf (zTileOdo (Tt y z)) (tileShape (Tt y z)) - slopeOf (zTileOdo (Tt x y)) (tileShape (Tt x y))
        + (((γ x y z).1 : ℚ), ((γ x y z).2 : ℚ)) = surgicalSlopeDiff o rev y z)
    (hH : o = .horizontal → ∀ x y z, Adm x y z → ∀ u ∈ tileShape (Tt x y), ∀ v ∈ tileShape (Tt y z),
      (∀ u' ∈ tileShape (Tt x y), ∀ v' ∈ tileShape (Tt y z), u' - v' ≠ D y z) →
      (u - v - D y z).1.natAbs + (u - v - D y z).2.natAbs = 1 →
      zTileOdo (Tt x y) u - zTileOdo (Tt y z) v - ptDot (γ x y z) v = β x y z)
    (hV : o = .vertical → ∀ x y z, Adm x y z → ∀ u ∈ tileShape (Tt x y), ∀ v ∈ tileShape (Tt y z),
      (∀ u' ∈ tileShape (Tt x y), ∀ v' ∈ tileShape (Tt y z), u' - v' ≠ D y z) →
      (u - v - D y z).1.natAbs + (u - v - D y z).2.natAbs = 1 →
      zTileOdo (Tt x y) u - zTileOdo (Tt y z) v - ptDot (γ x y z) v = β x y z + 1) :
    F.Respects o rev := by
  have memk : ∀ j < F.n, ∀ x, x ∈ F.dom j ↔ ∃ u ∈ tileShape (Tt (prev j) (ℓ j)), u + P j = x := by
    intro j hj x
    unfold PTFamily.dom
    rw [hT j hj]
    simp only [List.mem_map]
  have odoF : ∀ j < F.n, ∀ x, F.odo j x =
      zTileOdo (Tt (prev j) (ℓ j)) (x - P j) + ptDot (F.a j) (x - P j) + c j := by
    intro j hj x
    unfold PTFamily.odo
    rw [hT j hj, hB j hj]
    simp only [ptDot, Prod.fst_sub, Prod.snd_sub]
    ring
  have slopeF : ∀ j < F.n, slopeOf (F.odo j) (F.dom j) =
      slopeOf (zTileOdo (Tt (prev j) (ℓ j))) (tileShape (Tt (prev j) (ℓ j)))
        + (((F.a j).1 : ℚ), ((F.a j).2 : ℚ)) := by
    intro j hj
    exact slope_odo_zt F j _ (P j) (hT j hj)
  have hcs : ∀ p q : GInt, (((p + q).1 : ℚ), ((p + q).2 : ℚ))
      = (((p).1 : ℚ), ((p).2 : ℚ)) + (((q).1 : ℚ), ((q).2 : ℚ)) := by
    intro p q
    ext <;> simp
  intro k hk1
  have hk : k < F.n := by omega
  have hpk := hprev k hk1
  have hAd := hAdm k hk1
  have memk1 : ∀ x, x ∈ F.dom (k + 1) ↔ ∃ u ∈ tileShape (Tt (ℓ k) (ℓ (k + 1))), u + P (k + 1) = x := by
    intro x
    rw [memk (k + 1) hk1 x, hpk]
  have hDk : P (k + 1) = P k + D (ℓ k) (ℓ (k + 1)) := hD k hk1
  have hak : F.a (k + 1) = F.a k + γ (prev k) (ℓ k) (ℓ (k + 1)) := hAa k hk1
  have hck := hc k hk1
  refine ⟨?_, ?_⟩
  · simp only [slopeF (k + 1) hk1, slopeF k hk, hak, hpk, hT k hk, hT (k + 1) hk1, hTL]
    rw [hcs, ← hslope (prev k) (ℓ k) (ℓ (k + 1)) hAd]
    abel
  · intro hno x hx y hy hunit
    rw [memk k hk x] at hx
    rw [memk1 y] at hy
    obtain ⟨u, hu, hux⟩ := hx
    obtain ⟨v, hv, hvy⟩ := hy
    have hxy : u - v - D (ℓ k) (ℓ (k + 1)) = x - y := by
      rw [← hux, ← hvy, hDk]; abel
    have hno' : ∀ u' ∈ tileShape (Tt (prev k) (ℓ k)), ∀ v' ∈ tileShape (Tt (ℓ k) (ℓ (k + 1))),
        u' - v' ≠ D (ℓ k) (ℓ (k + 1)) := by
      intro u' hu' v' hv' heq
      apply hno
      refine ⟨u' + P k, (memk k hk _).2 ⟨u', hu', rfl⟩, (memk1 _).2 ⟨v', hv', ?_⟩⟩
      rw [hDk]
      have h' : u' = v' + D (ℓ k) (ℓ (k + 1)) := by rw [← heq]; abel
      rw [h']; abel
    have hunit' : (u - v - D (ℓ k) (ℓ (k + 1))).1.natAbs + (u - v - D (ℓ k) (ℓ (k + 1))).2.natAbs = 1 := by
      rw [hxy]; simpa only [unitApart, Prod.fst_sub, Prod.snd_sub] using hunit
    have ex : x - P k = u := by rw [← hux]; abel
    have ey : y - P (k + 1) = v := by rw [← hvy]; abel
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hH' := hH h (prev k) (ℓ k) (ℓ (k + 1)) hAd u hu v hv hno' hunit'
      rw [odoF k hk x, odoF (k + 1) hk1 y, hpk, hak, ex, ey, ← hux, ← hvy, hDk]
      unfold ptDot at hH' hck ⊢
      simp only [Prod.fst_add, Prod.snd_add] at hH' hck ⊢
      linarith [hH', hck]
    · have hV' := hV h (prev k) (ℓ k) (ℓ (k + 1)) hAd u hu v hv hno' hunit'
      rw [odoF k hk x, odoF (k + 1) hk1 y, hpk, hak, ex, ey, ← hux, ← hvy, hDk]
      unfold ptDot at hV' hck ⊢
      simp only [Prod.fst_add, Prod.snd_add] at hV' hck ⊢
      linarith [hV', hck]

/-- The letter-determined case (the original lemma, now a corollary): the tile of `k` is `letterZTile (ℓ k)`, the affine factor
is `α (ℓ k)`, and the centred constant is `c (ℓ k)`. -/
theorem PTFamily.respects_of_letters (F : PTFamily) (o : Orientation) (rev : Bool) (ℓ : ℕ → Letter) (P : ℕ → GInt)
    (α : Letter → GInt) (c : Letter → ℤ) (D : Letter → Letter → GInt)
    (hT : ∀ k < F.n, F.tile k = (letterZTile (ℓ k), P k))
    (hD : ∀ k, k + 1 < F.n → P (k + 1) = P k + D (ℓ k) (ℓ (k + 1)))
    (hA : ∀ k < F.n, F.a k = α (ℓ k))
    (hB : ∀ k < F.n, F.b k = c (ℓ k) - ptDot (α (ℓ k)) (P k))
    (hslope : ∀ a b : Letter,
      slopeOf (zTileOdo (letterZTile b)) (tileShape (letterZTile b)) + (((α b).1 : ℚ), ((α b).2 : ℚ))
        - (slopeOf (zTileOdo (letterZTile a)) (tileShape (letterZTile a)) + (((α a).1 : ℚ), ((α a).2 : ℚ)))
        = surgicalSlopeDiff o rev a b)
    (hH : o = .horizontal → ∀ a b : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile b),
      (∀ u' ∈ tileShape (letterZTile a), ∀ v' ∈ tileShape (letterZTile b), u' - v' ≠ D a b) →
      (u - v - D a b).1.natAbs + (u - v - D a b).2.natAbs = 1 →
      zTileOdo (letterZTile a) u + c a
        = zTileOdo (letterZTile b) v + ptDot (α b - α a) v + c b - ptDot (α a) (D a b))
    (hV : o = .vertical → ∀ a b : Letter, ∀ u ∈ tileShape (letterZTile a), ∀ v ∈ tileShape (letterZTile b),
      (∀ u' ∈ tileShape (letterZTile a), ∀ v' ∈ tileShape (letterZTile b), u' - v' ≠ D a b) →
      (u - v - D a b).1.natAbs + (u - v - D a b).2.natAbs = 1 →
      zTileOdo (letterZTile b) v + ptDot (α b - α a) v + c b - ptDot (α a) (D a b)
          - (zTileOdo (letterZTile a) u + c a) = -1) :
    F.Respects o rev := by
  refine PTFamily.respects_of_triples F o rev ℓ (fun k => if k = 0 then ℓ 0 else ℓ (k - 1)) P
    (fun _ y => letterZTile y) D (fun _ y z => α z - α y) (fun k => c (ℓ k))
    (fun _ y z => c z - c y - ptDot (α y) (D y z)) (fun _ _ _ => True)
    (fun k hk => hT k hk)
    (fun k _ => by
      show (if k + 1 = 0 then ℓ 0 else ℓ (k + 1 - 1)) = ℓ k
      simp)
    hD
    (fun k hk => by
      show F.a (k + 1) = F.a k + (α (ℓ (k + 1)) - α (ℓ k))
      rw [hA (k + 1) hk, hA k (by omega)]
      abel)
    (fun k hk => by
      show F.b k = c (ℓ k) - ptDot (F.a k) (P k)
      rw [hA k hk]
      exact hB k hk)
    (fun k hk => by
      show c (ℓ (k + 1)) = c (ℓ k) + (c (ℓ (k + 1)) - c (ℓ k) - ptDot (α (ℓ k)) (D (ℓ k) (ℓ (k + 1))))
        + ptDot (F.a k) (D (ℓ k) (ℓ (k + 1)))
      rw [hA k (by omega)]
      ring)
    (fun _ _ => trivial)
    (fun _ y => zTileLetter_letterZTile y)
    ?_ ?_ ?_
  · intro x y z _
    have h := hslope y z
    have hc : (((α z - α y).1 : ℚ), ((α z - α y).2 : ℚ))
        = (((α z).1 : ℚ), ((α z).2 : ℚ)) - (((α y).1 : ℚ), ((α y).2 : ℚ)) := by
      ext <;> simp
    show slopeOf (zTileOdo (letterZTile z)) (tileShape (letterZTile z))
        - slopeOf (zTileOdo (letterZTile y)) (tileShape (letterZTile y))
        + (((α z - α y).1 : ℚ), ((α z - α y).2 : ℚ)) = surgicalSlopeDiff o rev y z
    rw [hc, ← h]
    abel
  · intro h x y z _ u hu v hv hno hunit
    have := hH h y z u hu v hv hno hunit
    show zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (α z - α y) v
      = c z - c y - ptDot (α y) (D y z)
    linarith
  · intro h x y z _ u hu v hv hno hunit
    have := hV h y z u hu v hv hno hunit
    show zTileOdo (letterZTile y) u - zTileOdo (letterZTile z) v - ptDot (α z - α y) v
      = c z - c y - ptDot (α y) (D y z) + 1
    linarith

/-- Check: the forward explicit family is letter-determined (no affine part, no constant). -/
theorem HP_respects_letters (w : BinaryWord) : (HP w).Respects .horizontal false :=
  PTFamily.respects_of_letters (HP w) .horizontal false (lettersOf w false)
    (fun k => posF .horizontal false (lettersOf w false) k) (fun _ => 0) (fun _ => 0)
    (fun _ b => zeroOneHorizontalStep b)
    (fun k hk => HP_tile w k (by simpa only [HP_n] using hk))
    (fun k _ => posF_fwd_succ _ k)
    (fun _ _ => rfl)
    (fun k _ => by simp [HP, ptDot])
    (fun a b => slope_diff_plus a b)
    (fun _ a b u hu v hv hno hunit => by simpa [ptDot] using local_plus_adj a b u hu v hv hno hunit)
    (fun h => by cases h)

/-- Check: the minus explicit family is letter-determined with affine factor `alphaH`, constant `cstH` and step `rsH`. -/
theorem HM_respects_letters (w : BinaryWord) : (HM w).Respects .horizontal true :=
  PTFamily.respects_of_letters (HM w) .horizontal true (lettersOf w true) (posMH w) alphaH cstH rsH
    (fun k hk => HM_tile w k (by simpa only [HM_n] using hk))
    (fun k _ => posMH_succ w k)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun a b => slope_diff_minus a b)
    (fun _ a b u hu v hv hno hunit => local_minus_adj a b u hu v hv hno hunit)
    (fun h => by cases h)


/-- Within-family overlaps of consecutive tiles of a recursively determined family agree: the odometers of `k` and `k+1` are
equal on their common points, when the boundary quantity equals `β` on the overlaps. -/
theorem PTFamily.within_consecutive_of_triples (F : PTFamily)
    (ℓ prev : ℕ → Letter) (P : ℕ → GInt) (Tt : Letter → Letter → ZTile)
    (D : Letter → Letter → GInt) (γ : Letter → Letter → Letter → GInt) (c : ℕ → ℤ)
    (β : Letter → Letter → Letter → ℤ) (Adm : Letter → Letter → Letter → Prop)
    (hT : ∀ k < F.n, F.tile k = (Tt (prev k) (ℓ k), P k))
    (hprev : ∀ k, k + 1 < F.n → prev (k + 1) = ℓ k)
    (hD : ∀ k, k + 1 < F.n → P (k + 1) = P k + D (ℓ k) (ℓ (k + 1)))
    (hAa : ∀ k, k + 1 < F.n → F.a (k + 1) = F.a k + γ (prev k) (ℓ k) (ℓ (k + 1)))
    (hB : ∀ k < F.n, F.b k = c k - ptDot (F.a k) (P k))
    (hc : ∀ k, k + 1 < F.n →
      c (k + 1) = c k + β (prev k) (ℓ k) (ℓ (k + 1)) + ptDot (F.a k) (D (ℓ k) (ℓ (k + 1))))
    (hAdm : ∀ k, k + 1 < F.n → Adm (prev k) (ℓ k) (ℓ (k + 1)))
    (hov : ∀ x y z, Adm x y z → ∀ u ∈ tileShape (Tt x y), ∀ v ∈ tileShape (Tt y z),
      u - v = D y z → zTileOdo (Tt x y) u - zTileOdo (Tt y z) v - ptDot (γ x y z) v = β x y z) :
    ∀ k, k + 1 < F.n → ∀ x, x ∈ F.dom k → x ∈ F.dom (k + 1) → F.odo k x = F.odo (k + 1) x := by
  have memk : ∀ j < F.n, ∀ x, x ∈ F.dom j ↔ ∃ u ∈ tileShape (Tt (prev j) (ℓ j)), u + P j = x := by
    intro j hj x
    unfold PTFamily.dom
    rw [hT j hj]
    simp only [List.mem_map]
  have odoF : ∀ j < F.n, ∀ x, F.odo j x =
      zTileOdo (Tt (prev j) (ℓ j)) (x - P j) + ptDot (F.a j) (x - P j) + c j := by
    intro j hj x
    unfold PTFamily.odo
    rw [hT j hj, hB j hj]
    simp only [ptDot, Prod.fst_sub, Prod.snd_sub]
    ring
  intro k hk1 x hx1 hx2
  have hk : k < F.n := by omega
  have hpk := hprev k hk1
  have hAd := hAdm k hk1
  have hDk : P (k + 1) = P k + D (ℓ k) (ℓ (k + 1)) := hD k hk1
  have hak := hAa k hk1
  have hcc := hc k hk1
  have memk1 : ∀ x, x ∈ F.dom (k + 1) ↔ ∃ u ∈ tileShape (Tt (ℓ k) (ℓ (k + 1))), u + P (k + 1) = x := by
    intro x
    rw [memk (k + 1) hk1 x, hpk]
  obtain ⟨u, hu, hux⟩ := (memk k hk x).1 hx1
  obtain ⟨v, hv, hvx⟩ := (memk1 x).1 hx2
  have e1 : u = x - P k := by rw [← hux]; abel
  have e2 : v = x - P (k + 1) := by rw [← hvx]; abel
  have huv : u - v = D (ℓ k) (ℓ (k + 1)) := by rw [e1, e2, hDk]; abel
  have hu' : u = v + D (ℓ k) (ℓ (k + 1)) := by rw [← huv]; abel
  have hov' := hov (prev k) (ℓ k) (ℓ (k + 1)) hAd u hu v hv huv
  rw [odoF k hk x, odoF (k + 1) hk1 x, hpk, hak, ← e1, ← e2, hcc]
  subst hu'
  unfold ptDot at hov' ⊢
  simp only [Prod.fst_add, Prod.snd_add] at hov' ⊢
  linarith [hov']

end FLatticePaper.Tiles
