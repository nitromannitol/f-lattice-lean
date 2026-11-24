import FLatticePaper.Tiles.SiteJunction
import FLatticePaper.Tiles.CeilBlocks
import FLatticePaper.Tiles.IncrementCounts
import FLatticePaper.Construction.OffsetTables

/-! Task 53, marksIn (vertical junction): the vertical strings of two blocks.

The vertical marks of a tile are the vertical string of the reversed, letter-exchanged block word `vert X = (X.map swapLetter).reverse`
(`markedSites` reads `vw.reverse`), started at `(1,1)` and shifted to `(0,0)` by `VS0`. A vertical step reads the previous letter
for the `x` coordinate and the current letter for the `y` coordinate, and a vertical string has no enlarged tiles. So the junction of
a block `Y` (starting with `q`) and a block `Z` (starting with `q`) is the translate of the string of `Z` by
`jv Y = (-#p Y, #p Y + 2 #q Y)`, and for a block `X` of slope `f` the junction offset of `vert X` is `texV2 f.rotate`. -/

namespace FLatticePaper.Tiles.VJunction

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.CeilWords
open FLatticePaper.Tiles.CeilBlocks FLatticePaper.Construction

/-- The vertical letter list of a block: the letters exchanged and reversed (`markedSites` reads `vw.reverse`). -/
def vert (X : List Letter) : List Letter := (X.map swapLetter).reverse

/-- The vertical sites of a letter list, started at the origin `(0,0)` (the start `(1,1)` of `stringSites true true`, shifted). -/
def VS0 (L : List Letter) : List (ℤ × ℤ) := sitesFrom true true none (0, 0) L

/-- The junction offset of a vertical block `Y` (its first letter is `q`). -/
def jv (Y : List Letter) : ℤ × ℤ :=
  (-(Y.count Letter.p : ℤ), (Y.count Letter.p : ℤ) + 2 * (Y.count Letter.q : ℤ))

theorem vert_count_p (X : List Letter) : (vert X).count Letter.p = X.count Letter.q := by
  unfold vert
  rw [List.count_reverse, count_map_swapLetter_p]

theorem vert_count_q (X : List Letter) : (vert X).count Letter.q = X.count Letter.p := by
  unfold vert
  rw [List.count_reverse, count_map_swapLetter_q]

theorem vert_append (X Y : List Letter) : vert (X ++ Y) = vert Y ++ vert X := by
  unfold vert
  simp [List.map_append, List.reverse_append]

theorem origins_some_cons_gen (vt rv : Bool) (pr l : Letter) (pos : ℤ × ℤ) (ls : List Letter) :
    origins vt rv (some pr) pos (l :: ls) =
      (pos + dxdy vt rv pr l, l, (!vt && pr == Letter.q && l == Letter.q)) ::
        origins vt rv (some l) (pos + dxdy vt rv pr l) ls := rfl

/-- The translation of the origins of a string, for any mode. -/
theorem origins_translate_gen (vt rv : Bool) (v : ℤ × ℤ) :
    ∀ (o : Option Letter) (pos : ℤ × ℤ) (L : List Letter),
      origins vt rv o (pos + v) L = (origins vt rv o pos L).map fun t => (t.1 + v, t.2)
  | _, _, [] => rfl
  | none, pos, l :: ls => by
      change (pos + v, l, false) :: origins vt rv (some l) (pos + v) ls =
        ((pos, l, false) :: origins vt rv (some l) pos ls).map fun t => (t.1 + v, t.2)
      rw [List.map_cons, origins_translate_gen vt rv v (some l) pos ls]
  | some pr, pos, l :: ls => by
      rw [origins_some_cons_gen, origins_some_cons_gen, List.map_cons, add_right_comm pos v,
        origins_translate_gen vt rv v (some l) _ ls]

/-- The translation of the sites of a string, for any mode. -/
theorem sitesFrom_translate_gen (vt rv : Bool) (o : Option Letter) (pos v : ℤ × ℤ) (L : List Letter) :
    sitesFrom vt rv o (pos + v) L = (sitesFrom vt rv o pos L).map fun z => z + v := by
  unfold sitesFrom
  rw [origins_translate_gen vt rv v o pos L, List.flatMap_map, List.map_flatMap]
  congr 1
  funext t
  rw [List.map_map]
  congr 1
  funext b
  simp only [Function.comp_def, Prod.fst_add, Prod.snd_add]
  ext <;> simp <;> ring

theorem origins_ne_nil_gen (vt rv : Bool) (o : Option Letter) (pos : ℤ × ℤ) {L : List Letter} (h : L ≠ []) :
    origins vt rv o pos L ≠ [] := by
  cases L with
  | nil => exact absurd rfl h
  | cons x xs => cases o <;> simp [origins]

/-- The end origin does not depend on the first letter's own step (it is the origin of the last tile of the rest). -/
theorem endOrigin_cons_some (vt rv : Bool) (pr l : Letter) (e : ℤ × ℤ) (L : List Letter) :
    endOrigin vt rv (some pr) e (l :: L) = endOrigin vt rv (some l) (e + dxdy vt rv pr l) L := by
  cases L with
  | nil =>
      simp [endOrigin, origins]
      rfl
  | cons l' L' =>
    have hY := origins_ne_nil_gen vt rv (some l) (e + dxdy vt rv pr l) (L := l' :: L') (List.cons_ne_nil _ _)
    unfold endOrigin
    rw [origins_some_cons_gen, getLast?_cons_of_ne _ _ hY]
    exact getD_last_map_irrel (fun x => x.1) hY _ _

theorem endOrigin_none_cons_gen (vt rv : Bool) (x : Letter) (X : List Letter) (pos : ℤ × ℤ) :
    endOrigin vt rv none pos (x :: X) = endOrigin vt rv (some x) pos X := by
  cases X with
  | nil => simp [endOrigin, origins]
  | cons y Y =>
    have hY := origins_ne_nil_gen vt rv (some x) pos (L := y :: Y) (List.cons_ne_nil _ _)
    unfold endOrigin
    rw [show origins vt rv none pos (x :: y :: Y) = (pos, x, false) :: origins vt rv (some x) pos (y :: Y) from rfl,
      getLast?_cons_of_ne _ _ hY]

/-- The closed form of the end origin of a vertical string started at the letter `pr` (the origin `e` of the state `pr`):
the `x` coordinate retreats by one for each `p` read as the previous letter, the `y` coordinate advances by one for `p` and two
for `q`. -/
theorem vend_some (pr : Letter) : ∀ (L : List Letter) (e : ℤ × ℤ),
    endOrigin true true (some pr) e L =
      e + (-(((pr :: L).dropLast).count Letter.p : ℤ), (L.count Letter.p : ℤ) + 2 * (L.count Letter.q : ℤ))
  | [], e => by
      simp [endOrigin, origins]
  | l :: L, e => by
      have hne : (l :: L) ≠ [] := List.cons_ne_nil _ _
      rw [endOrigin_cons_some, vend_some l L (e + dxdy true true pr l), List.dropLast_cons_of_ne_nil hne]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, dxdy, List.count_cons]
        cases pr <;> cases l <;> simp <;> omega
      · simp only [Prod.snd_add, dxdy, List.count_cons]
        cases pr <;> cases l <;> simp <;> omega

/-- The count of `a` splits at the last letter of a nonempty list. -/
theorem count_split_last (X : List Letter) (pr : Letter) (hpr : X.getLast? = some pr) (a : Letter) :
    X.count a = X.dropLast.count a + (if pr = a then 1 else 0) := by
  have hne : X ≠ [] := by
    rintro rfl
    simp at hpr
  have hl : X.getLast hne = pr := by
    have h := List.getLast?_eq_some_getLast hne
    rw [h] at hpr
    simpa using hpr
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]
  simp [List.count_append, List.count_cons]

theorem vertical_head (X : List Letter) (hpr : X.getLast? = some Letter.p) :
    ∃ Y', vert X = Letter.q :: Y' := by
  have hne : X ≠ [] := by
    rintro rfl
    simp at hpr
  have hl : X.getLast hne = Letter.p := by
    have h := List.getLast?_eq_some_getLast hne
    rw [h] at hpr
    simpa using hpr
  refine ⟨(X.dropLast.map swapLetter).reverse, ?_⟩
  unfold vert
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]
  simp [swapLetter]

/-- The vertical junction: the string of `Y ++ Z` is the string of `Y` followed by the string of `Z` translated by `jv Y`,
for blocks `Y` and `Z` both starting with `q`. -/
theorem vjunction (Y' Z' : List Letter) :
    VS0 ((Letter.q :: Y') ++ (Letter.q :: Z')) =
      VS0 (Letter.q :: Y') ++ (VS0 (Letter.q :: Z')).map fun z => z + jv (Letter.q :: Y') := by
  obtain ⟨pr, hpr⟩ : ∃ pr, (Letter.q :: Y').getLast? = some pr := by
    cases h : (Letter.q :: Y').getLast? with
    | none => simp at h
    | some pr => exact ⟨pr, rfl⟩
  unfold VS0
  rw [sitesFrom_append true true Letter.q Y' (Letter.q :: Z') none (0, 0), hpr]
  congr 1
  rw [endOrigin_none_cons_gen, vend_some Letter.q Y' (0, 0)]
  have hE : (sitesFrom true true (some pr)
      ((0, 0) + (-(((Letter.q :: Y').dropLast).count Letter.p : ℤ),
        (Y'.count Letter.p : ℤ) + 2 * (Y'.count Letter.q : ℤ))) (Letter.q :: Z')) =
      sitesFrom true true none
        ((0, 0) + (-(((Letter.q :: Y').dropLast).count Letter.p : ℤ),
          (Y'.count Letter.p : ℤ) + 2 * (Y'.count Letter.q : ℤ)) + dxdy true true pr Letter.q)
        (Letter.q :: Z') := by
    unfold sitesFrom
    rw [origins_some_cons_gen]
    rfl
  rw [hE, show (0, 0) + (-(((Letter.q :: Y').dropLast).count Letter.p : ℤ),
        (Y'.count Letter.p : ℤ) + 2 * (Y'.count Letter.q : ℤ)) + dxdy true true pr Letter.q =
      jv (Letter.q :: Y') from ?_]
  · have := sitesFrom_translate_gen true true none (0, 0) (jv (Letter.q :: Y')) (Letter.q :: Z')
    have hz : ((0 : ℤ), (0 : ℤ)) + jv (Letter.q :: Y') = jv (Letter.q :: Y') := by
      ext <;> simp
    rw [hz] at this
    exact this
  · have hs := count_split_last (Letter.q :: Y') pr hpr Letter.p
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, jv, dxdy, List.count_cons] at hs ⊢
      cases pr <;> simp at hs ⊢ <;> omega
    · simp only [Prod.snd_add, jv, dxdy, List.count_cons]
      cases pr <;> simp <;> omega

/-- The junction offset of a block whose slope is odd: `jv (vert X) = texV2 (f.rotate)` for the slope `(2 num, den + num)`. -/
theorem vert_jv_odd (X : List Letter) (f : Fraction) (hX : CeilWord X (2 * f.num) (f.den + f.num))
    (hl : 1 ≤ f.den + f.num) (hf : f.Odd) :
    jv (vert X) = texV2 f.rotate := by
  have hlen := hX.1
  have hc := ceil_count_q X _ _ hX hl
  have hpq := count_pq_sum X
  rw [Fraction.rotate_of_odd hf]
  unfold jv texV2
  rw [vert_count_p, vert_count_q]
  refine Prod.ext ?_ ?_
  · dsimp only
    omega
  · dsimp only
    omega

/-- The junction offset of a block whose slope is even: `jv (vert X) = texV2 (f.rotate)` for the slope `(num, (den + num)/2)`. -/
theorem vert_jv_even (X : List Letter) (f : Fraction) (hX : CeilWord X f.num ((f.den + f.num) / 2))
    (hl : 1 ≤ (f.den + f.num) / 2) (hf : f.Even) :
    jv (vert X) = texV2 f.rotate := by
  have hlen := hX.1
  have hc := ceil_count_q X _ _ hX hl
  have hpq := count_pq_sum X
  have hf' : (f.num + f.den) % 2 = 0 := hf
  rw [Fraction.rotate_of_even hf]
  unfold jv texV2
  rw [vert_count_p, vert_count_q]
  refine Prod.ext ?_ ?_
  · dsimp only
    omega
  · dsimp only
    omega

end FLatticePaper.Tiles.VJunction
