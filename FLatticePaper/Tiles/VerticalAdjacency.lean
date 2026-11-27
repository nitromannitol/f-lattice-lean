import FLatticePaper.Tiles.VerticalIdentities

/-! The adjacency dichotomy of the vertical families: for consecutive tiles of a vertical zero-one string, the two tiles
either overlap or contain a unit-apart pair of sites. This is the `hadjP` / `hadjM` input of `hkappa_of_families`. The
four letter pairs of each vertical table are checked by `decide`. -/

namespace FLatticePaper.Tiles

/-- The two tile shapes `A` at `0` and `B` at `off` overlap, or have a unit-apart pair of sites. -/
abbrev vDich (A B : ZTile) (off : GInt) : Prop :=
  (∃ s ∈ tileShape A, ∃ t ∈ tileShape B, s = t + off) ∨
    (∃ s ∈ tileShape A, ∃ t ∈ tileShape B, (s.1 - (t + off).1).natAbs + (s.2 - (t + off).2).natAbs = 1)

theorem vDich_fwd (a b : Letter) : vDich (letterZTile a) (letterZTile b) (vOffset b) := by
  cases a <;> cases b <;> decide

theorem vDich_rev (a b : Letter) : vDich (letterZTile a) (letterZTile b) (vRevOffset a b) := by
  cases a <;> cases b <;> decide

/-- Translating a dichotomy of shapes to the positions `p` and `q = p + off`. -/
theorem dich_pos (A B : ZTile) (off p q : GInt) (hq : q = p + off) (h : vDich A B off) :
    (∃ x, x ∈ (tileShape A).map (· + p) ∧ x ∈ (tileShape B).map (· + q)) ∨
      ∃ x, x ∈ (tileShape A).map (· + p) ∧ ∃ y, y ∈ (tileShape B).map (· + q) ∧ unitApart x y := by
  rcases h with ⟨s, hs, t, ht, hst⟩ | ⟨s, hs, t, ht, hu⟩
  · left
    refine ⟨s + p, List.mem_map.2 ⟨s, hs, rfl⟩, List.mem_map.2 ⟨t, ht, ?_⟩⟩
    rw [hq, hst]
    abel
  · right
    refine ⟨s + p, List.mem_map.2 ⟨s, hs, rfl⟩, t + q, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
    unfold unitApart
    have e1 : (s + p).1 - (t + q).1 = s.1 - (t + off).1 := by
      rw [hq]
      simp only [Prod.fst_add]
      ring
    have e2 : (s + p).2 - (t + q).2 = s.2 - (t + off).2 := by
      rw [hq]
      simp only [Prod.snd_add]
      ring
    rw [e1, e2]
    exact hu

theorem getD_map_f {α β : Type*} (f : α → β) (L : List α) (k : ℕ) (a : α) :
    (L.map f).getD k (f a) = f (L.getD k a) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  generalize L[k]? = o
  cases o <;> simp

theorem getD_map_fst' {α β : Type*} (L : List (α × β)) (k : ℕ) (a : α) (b : β) :
    (L.map Prod.fst).getD k a = (L.getD k (a, b)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  generalize L[k]? = o
  cases o <;> simp

theorem getD_map_snd' {α β : Type*} (L : List (α × β)) (k : ℕ) (a : α) (b : β) :
    (L.map Prod.snd).getD k b = (L.getD k (a, b)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  generalize L[k]? = o
  cases o <;> simp

/-- The tile of the forward vertical string at `k`: its letter and its position. -/
theorem vStringAt_getD_pair (w : BinaryWord) (c : GInt) (k : ℕ) (hk : k < w.length) :
    (vStringAt w c).getD k (ZTile.zero, (0 : GInt)) =
      (letterZTile (w.getD k Letter.p), (List.scanl (· + ·) c (w.tail.map vOffset)).getD k 0) := by
  have hw : 0 < w.length := by omega
  have hl1 : (w.map letterZTile).length ≤ (List.scanl (· + ·) c (w.tail.map vOffset)).length := by
    simp only [List.length_map, List.length_scanl, List.length_tail]
    omega
  have hl2 : (List.scanl (· + ·) c (w.tail.map vOffset)).length ≤ (w.map letterZTile).length := by
    simp only [List.length_map, List.length_scanl, List.length_tail]
    omega
  have hfst : (vStringAt w c).map Prod.fst = w.map letterZTile := by
    unfold vStringAt
    exact List.map_fst_zip hl1
  have hsnd : (vStringAt w c).map Prod.snd = List.scanl (· + ·) c (w.tail.map vOffset) := by
    unfold vStringAt
    exact List.map_snd_zip hl2
  apply Prod.ext
  · rw [← getD_map_fst' (vStringAt w c) k ZTile.zero (0 : GInt), hfst]
    exact getD_map_f letterZTile w k Letter.p
  · rw [← getD_map_snd' (vStringAt w c) k ZTile.zero (0 : GInt), hsnd]

/-- The tile of the reversed vertical string at `k`: its letter and its position. -/
theorem vRevStringAt_getD_pair (u : BinaryWord) (c : GInt) (k : ℕ) (hk : k < u.length) :
    (vRevStringAt u c).getD k (ZTile.zero, (0 : GInt)) =
      (letterZTile (u.getD k Letter.p),
        (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD k 0) := by
  have hu : 0 < u.length := by omega
  have hl1 : (u.map letterZTile).length ≤
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).length := by
    simp only [List.length_map, List.length_scanl, List.length_zip, List.length_tail]
    omega
  have hl2 : (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).length ≤
      (u.map letterZTile).length := by
    simp only [List.length_map, List.length_scanl, List.length_zip, List.length_tail]
    omega
  have hfst : (vRevStringAt u c).map Prod.fst = u.map letterZTile := by
    unfold vRevStringAt
    exact List.map_fst_zip hl1
  have hsnd : (vRevStringAt u c).map Prod.snd =
      List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2) := by
    unfold vRevStringAt
    exact List.map_snd_zip hl2
  apply Prod.ext
  · rw [← getD_map_fst' (vRevStringAt u c) k ZTile.zero (0 : GInt), hfst]
    exact getD_map_f letterZTile u k Letter.p
  · rw [← getD_map_snd' (vRevStringAt u c) k ZTile.zero (0 : GInt), hsnd]

/-- The adjacency dichotomy of consecutive tiles of a family on the forward vertical string `vStringAt w c`. -/
theorem adj_vStringAt (w : BinaryWord) (c : GInt) (F : PTFamily) (hF : F.ts = vStringAt w c)
    (k : ℕ) (hk : k + 1 < F.n) :
    (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y := by
  have hn : F.n = w.length := by
    unfold PTFamily.n
    rw [hF, vStringAt_length]
  rw [hn] at hk
  have hq : (List.scanl (· + ·) c (w.tail.map vOffset)).getD (k + 1) 0 =
      (List.scanl (· + ·) c (w.tail.map vOffset)).getD k 0 + vOffset (w.getD (k + 1) Letter.p) := by
    rw [scanl_getD_succ_gen _ c k (by simp; omega), vFwd_hL w k hk]
  have ht0 : F.tile k = (letterZTile (w.getD k Letter.p),
      (List.scanl (· + ·) c (w.tail.map vOffset)).getD k 0) := by
    unfold PTFamily.tile
    rw [hF, vStringAt_getD_pair w c k (by omega)]
  have ht1 : F.tile (k + 1) = (letterZTile (w.getD (k + 1) Letter.p),
      (List.scanl (· + ·) c (w.tail.map vOffset)).getD (k + 1) 0) := by
    unfold PTFamily.tile
    rw [hF, vStringAt_getD_pair w c (k + 1) hk]
  unfold PTFamily.dom
  rw [ht0, ht1]
  exact dich_pos _ _ _ _ _ hq (vDich_fwd _ _)

/-- The adjacency dichotomy of consecutive tiles of a family on the reversed vertical string `vRevStringAt u c`. -/
theorem adj_vRevStringAt (u : BinaryWord) (c : GInt) (F : PTFamily) (hF : F.ts = vRevStringAt u c)
    (k : ℕ) (hk : k + 1 < F.n) :
    (∃ x, x ∈ F.dom k ∧ x ∈ F.dom (k + 1)) ∨
      ∃ x, x ∈ F.dom k ∧ ∃ y, y ∈ F.dom (k + 1) ∧ unitApart x y := by
  have hn : F.n = u.length := by
    unfold PTFamily.n
    rw [hF, vRevStringAt_length]
  rw [hn] at hk
  have hq : (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD (k + 1) 0 =
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD k 0 +
        vRevOffset (u.getD k Letter.p) (u.getD (k + 1) Letter.p) := by
    rw [scanl_getD_succ_gen _ c k (by simp; omega), vRev_zip_getD u k hk]
  have ht0 : F.tile k = (letterZTile (u.getD k Letter.p),
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD k 0) := by
    unfold PTFamily.tile
    rw [hF, vRevStringAt_getD_pair u c k (by omega)]
  have ht1 : F.tile (k + 1) = (letterZTile (u.getD (k + 1) Letter.p),
      (List.scanl (· + ·) c ((u.zip u.tail).map fun ab => vRevOffset ab.1 ab.2)).getD (k + 1) 0) := by
    unfold PTFamily.tile
    rw [hF, vRevStringAt_getD_pair u c (k + 1) hk]
  unfold PTFamily.dom
  rw [ht0, ht1]
  exact dich_pos _ _ _ _ _ hq (vDich_rev _ _)

end FLatticePaper.Tiles
