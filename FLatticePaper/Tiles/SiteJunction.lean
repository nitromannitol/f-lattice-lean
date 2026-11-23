import FLatticePaper.Tiles.SiteConcat

/-! Task 53, marksIn (horizontal junction): a forward horizontal string whose first block starts with `q` and whose last
letter is `p` splits at the block boundary. The second block sits at the offset `(2|X| - #q X, #q X)` of its first tile.

This is letter arithmetic only. Once the blocks carry their ceiling slopes, this offset is `texV1Odd` or `texV1Even` of the
block's fraction (`CeilWords`), which is what the tile recursion `oddChildB`/`evenChildB` uses. -/

namespace FLatticePaper.Tiles.SiteJunction

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.SiteConcat

/-- The offset of a forward horizontal tile of letter `l` from the tile before it (`dxdy` with `rev = false` reads `l`). -/
def stepH (l : Letter) : ℤ × ℤ := (if l = .p then 2 else 1, if l = .q then 1 else 0)

/-- The total offset of the tiles of a letter list, each tile's step counted once. -/
def sumStep : List Letter → ℤ × ℤ
  | [] => (0, 0)
  | l :: ls => stepH l + sumStep ls

theorem dxdy_false_false (prev l : Letter) : dxdy false false prev l = stepH l := by
  cases prev <;> cases l <;> rfl

theorem origins_some_cons (pr l : Letter) (pos : ℤ × ℤ) (ls : List Letter) :
    origins false false (some pr) pos (l :: ls) =
      (pos + dxdy false false pr l, l, (!false && pr == Letter.q && l == Letter.q)) ::
        origins false false (some l) (pos + dxdy false false pr l) ls := rfl

/-- The origins of a horizontal string are translation-equivariant. -/
theorem origins_translate (v : ℤ × ℤ) : ∀ (o : Option Letter) (pos : ℤ × ℤ) (L : List Letter),
    origins false false o (pos + v) L = (origins false false o pos L).map fun t => (t.1 + v, t.2)
  | _, _, [] => rfl
  | none, pos, l :: ls => by
      change (pos + v, l, false) :: origins false false (some l) (pos + v) ls =
        ((pos, l, false) :: origins false false (some l) pos ls).map fun t => (t.1 + v, t.2)
      rw [List.map_cons, origins_translate v (some l) pos ls]
  | some pr, pos, l :: ls => by
      rw [origins_some_cons, origins_some_cons, List.map_cons, add_right_comm pos v,
        origins_translate v (some l) _ ls]

/-- The sites of a horizontal string are translation-equivariant. -/
theorem sitesFrom_translate (o : Option Letter) (pos v : ℤ × ℤ) (L : List Letter) :
    sitesFrom false false o (pos + v) L = (sitesFrom false false o pos L).map fun z => z + v := by
  unfold sitesFrom
  rw [origins_translate v o pos L, List.flatMap_map, List.map_flatMap]
  congr 1
  funext t
  rw [List.map_map]
  congr 1
  funext b
  simp only [Function.comp_def, Prod.fst_add, Prod.snd_add]
  ext <;> simp <;> ring

theorem origins_ne_nil_of (o : Option Letter) (pos : ℤ × ℤ) {L : List Letter} (h : L ≠ []) :
    origins false false o pos L ≠ [] := by
  cases L with
  | nil => exact absurd rfl h
  | cons x xs => cases o <;> simp [origins]

/-- The end origin of a string started at a letter: the origin of its first tile plus the total step. -/
theorem endOrigin_some_cons (pr : Letter) : ∀ (l : Letter) (ls : List Letter) (pos : ℤ × ℤ),
    endOrigin false false (some pr) pos (l :: ls) = pos + sumStep (l :: ls)
  | l, [], pos => by
      have h : sumStep [l] = stepH l := by simp [sumStep]
      rw [h]
      simp [endOrigin, origins, dxdy_false_false]
      rfl
  | l, l' :: ls, pos => by
      have hY := origins_ne_nil_of (some l) (pos + dxdy false false pr l) (L := l' :: ls) (List.cons_ne_nil _ _)
      have e : endOrigin false false (some pr) pos (l :: l' :: ls) =
          endOrigin false false (some l) (pos + dxdy false false pr l) (l' :: ls) := by
        unfold endOrigin
        rw [origins_some_cons, getLast?_cons_of_ne _ _ hY]
        exact getD_last_map_irrel (fun x => x.1) hY _ _
      rw [e, endOrigin_some_cons l l' ls (pos + dxdy false false pr l), dxdy_false_false]
      simp only [sumStep, add_assoc]

/-- The end origin of a string started at the empty state: the origin `pos` plus the total step of the letters after the
first. -/
theorem endOrigin_none_cons (x : Letter) (X' : List Letter) (pos : ℤ × ℤ) :
    endOrigin false false none pos (x :: X') = pos + sumStep X' := by
  cases X' with
  | nil => simp [endOrigin, origins, sumStep]
  | cons y Y =>
      have hY := origins_ne_nil_of (some x) pos (L := y :: Y) (List.cons_ne_nil _ _)
      have e : endOrigin false false none pos (x :: y :: Y) =
          endOrigin false false (some x) pos (y :: Y) := by
        unfold endOrigin
        rw [show origins false false none pos (x :: y :: Y) =
            (pos, x, false) :: origins false false (some x) pos (y :: Y) from rfl,
          getLast?_cons_of_ne _ _ hY]
      rw [e, endOrigin_some_cons x y Y pos]

/-- A `q` after a `p` is not enlarged, and its tile is at the step `(1, 1)` from the `p`. -/
theorem sitesFrom_some_p (e : ℤ × ℤ) (Y' : List Letter) :
    sitesFrom false false (some Letter.p) e (Letter.q :: Y') =
      sitesFrom false false none (e + (1, 1)) (Letter.q :: Y') := by
  have hd : dxdy false false Letter.p Letter.q = (1, 1) := rfl
  have h1 : origins false false (some Letter.p) e (Letter.q :: Y') =
      (e + (1, 1), Letter.q, false) :: origins false false (some Letter.q) (e + (1, 1)) Y' := by
    rw [origins_some_cons, hd]
    rfl
  have h2 : origins false false none (e + (1, 1)) (Letter.q :: Y') =
      (e + (1, 1), Letter.q, false) :: origins false false (some Letter.q) (e + (1, 1)) Y' := rfl
  unfold sitesFrom
  rw [h1, h2]

/-- The step of the block `q :: X'`, read through the letters after its first one, plus the step `(1,1)` of a following `q`. -/
theorem sumStep_fst (L : List Letter) : (sumStep L).1 = (L.length : ℤ) + (L.count Letter.p : ℤ) := by
  induction L with
  | nil => simp [sumStep]
  | cons l L ih =>
      cases l <;> simp [sumStep, stepH, ih]
      all_goals omega

theorem sumStep_snd (L : List Letter) : (sumStep L).2 = (L.count Letter.q : ℤ) := by
  induction L with
  | nil => simp [sumStep]
  | cons l L ih =>
      cases l <;> simp [sumStep, stepH, ih]
      all_goals omega

theorem count_pq_sum (L : List Letter) : L.count Letter.p + L.count Letter.q = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      cases l <;> simp
      all_goals omega

/-- The offset of the second block: `sumStep X' + (1,1)` is `(2|X| - #q X, #q X)` for `X = q :: X'`. -/
theorem junction_formula (X' : List Letter) :
    sumStep X' + (1, 1) =
      (2 * ((Letter.q :: X').length : ℤ) - ((Letter.q :: X').count Letter.q : ℤ), ((Letter.q :: X').count Letter.q : ℤ)) := by
  have h1 := sumStep_fst X'
  have h2 := sumStep_snd X'
  have h3 := count_pq_sum X'
  have h4 : ((Letter.q :: X').count Letter.q : ℤ) = (X'.count Letter.q : ℤ) + 1 := by
    simp
  have h5 : ((Letter.q :: X').length : ℤ) = (X'.length : ℤ) + 1 := by simp
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    omega
  · simp only [Prod.snd_add]
    omega

/-- **Junction of a horizontal string.** If the block `q :: X'` ends with `p` and the next block starts with `q`, the sites of
their concatenation are the sites of the first block, followed by the sites of the second block shifted by its offset. -/
theorem stringSites_block (X' Y' : List Letter) (hlast : (Letter.q :: X').getLast? = some Letter.p) :
    stringSites false false ((Letter.q :: X') ++ (Letter.q :: Y')) =
      stringSites false false (Letter.q :: X') ++
        (stringSites false false (Letter.q :: Y')).map fun z =>
          z + (2 * ((Letter.q :: X').length : ℤ) - ((Letter.q :: X').count Letter.q : ℤ),
            ((Letter.q :: X').count Letter.q : ℤ)) := by
  have hs : startPos false false = (0, 0) := rfl
  simp only [stringSites_eq_sitesFrom, hs]
  rw [sitesFrom_append false false Letter.q X' (Letter.q :: Y') none (0, 0), hlast]
  congr 1
  have key : sitesFrom false false (some Letter.p) ((0, 0) + sumStep X') (Letter.q :: Y') =
      (sitesFrom false false none (0, 0) (Letter.q :: Y')).map fun z => z + (sumStep X' + (1, 1)) := by
    rw [sitesFrom_some_p, add_assoc, sitesFrom_translate]
  rw [endOrigin_none_cons, key, junction_formula X']

end FLatticePaper.Tiles.SiteJunction
