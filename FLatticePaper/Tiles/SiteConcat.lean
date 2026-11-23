import FLatticePaper.Tiles.SiteStrings

/-! Task 53, item 4 (concatenation): the origins of a string split at a block boundary.

The origins of `A ++ B` are the origins of `A`, followed by the origins of `B` started from the last letter and origin of `A`.
This is the form in which the marked strings of a child word split into the blocks `pw`, `qw` of `childWords`. -/

namespace FLatticePaper.Tiles.SiteConcat

open FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings

/-- The origin of the last tile of the string `A` started from the state `(o, pos)`; `pos` for the empty string. -/
def endOrigin (vert rev : Bool) (o : Option Letter) (pos : ℤ × ℤ) (A : List Letter) : ℤ × ℤ :=
  ((origins vert rev o pos A).getLast?.map (·.1)).getD pos

/-- For a nonempty list the default in `endOrigin` does not matter. -/
theorem getD_last_map_irrel {α β : Type} {X : List α} (f : α → β) (h : X ≠ []) (d d' : β) :
    ((X.getLast?.map f).getD d) = ((X.getLast?.map f).getD d') := by
  cases X with
  | nil => exact absurd rfl h
  | cons x xs => simp [List.getLast?_cons]

theorem getLast?_cons_of_ne {α : Type} (x : α) (L : List α) (h : L ≠ []) :
    (x :: L).getLast? = L.getLast? := by
  cases L with
  | nil => exact absurd rfl h
  | cons y L => simp [List.getLast?_cons]

theorem origins_append (vert rev : Bool) (a : Letter) (A B : List Letter) :
    ∀ (o : Option Letter) (pos : ℤ × ℤ),
      origins vert rev o pos ((a :: A) ++ B) =
        origins vert rev o pos (a :: A) ++ origins vert rev (a :: A).getLast? (endOrigin vert rev o pos (a :: A)) B := by
  induction A generalizing a with
  | nil =>
    intro o pos
    cases o with
    | none => simp [origins, endOrigin]
    | some pr => simp [origins, endOrigin]
  | cons a' A' ih =>
    intro o pos
    have hne : a' :: A' ≠ [] := List.cons_ne_nil _ _
    have hl : (a :: a' :: A').getLast? = (a' :: A').getLast? := getLast?_cons_of_ne _ _ hne
    cases o with
    | none =>
      have h := ih a' (some a) pos
      have e1 : origins vert rev none pos ((a :: a' :: A') ++ B) =
          (pos, a, false) :: origins vert rev (some a) pos ((a' :: A') ++ B) := rfl
      have e2 : origins vert rev none pos (a :: a' :: A') =
          (pos, a, false) :: origins vert rev (some a) pos (a' :: A') := rfl
      have he : endOrigin vert rev none pos (a :: a' :: A') = endOrigin vert rev (some a) pos (a' :: A') := by
        simp [endOrigin, origins]
      rw [e1, e2, h, hl, he]
      simp
    | some pr =>
      have h := ih a' (some a) (pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2)
      have e1 : origins vert rev (some pr) pos ((a :: a' :: A') ++ B) =
          ((pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2), a,
            (!vert && pr == Letter.q && a == Letter.q)) ::
          origins vert rev (some a) (pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2) ((a' :: A') ++ B) := rfl
      have e2 : origins vert rev (some pr) pos (a :: a' :: A') =
          ((pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2), a,
            (!vert && pr == Letter.q && a == Letter.q)) ::
          origins vert rev (some a) (pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2) (a' :: A') := rfl
      have hY : origins vert rev (some a) (pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2) (a' :: A') ≠ [] := by
        simp [origins]
      have he : endOrigin vert rev (some pr) pos (a :: a' :: A') =
          endOrigin vert rev (some a) (pos.1 + (dxdy vert rev pr a).1, pos.2 + (dxdy vert rev pr a).2) (a' :: A') := by
        unfold endOrigin
        rw [e2, getLast?_cons_of_ne _ _ hY]
        exact getD_last_map_irrel (fun x => x.1) hY _ _
      rw [e1, e2, h, hl, he]
      simp

/-- The sites of a string started from the state `(o, pos)`: the tiles of `origins`, each with its base sites. -/
def sitesFrom (vert rev : Bool) (o : Option Letter) (pos : ℤ × ℤ) (ls : List Letter) : List (ℤ × ℤ) :=
  (origins vert rev o pos ls).flatMap fun t => (baseSites t.2.1 t.2.2).map fun b => (t.1.1 + b.1, t.1.2 + b.2)

theorem stringSites_eq_sitesFrom (vert rev : Bool) (ls : List Letter) :
    stringSites vert rev ls = sitesFrom vert rev none (startPos vert rev) ls := rfl

/-- **Concatenation of a string.** The sites of `A ++ B` are the sites of `A`, followed by the sites of `B` started at the
last tile of `A`, with the enlargement of its first tile read from the last letter of `A`. -/
theorem sitesFrom_append (vert rev : Bool) (a : Letter) (A B : List Letter) (o : Option Letter) (pos : ℤ × ℤ) :
    sitesFrom vert rev o pos ((a :: A) ++ B) =
      sitesFrom vert rev o pos (a :: A) ++
        sitesFrom vert rev (a :: A).getLast? (endOrigin vert rev o pos (a :: A)) B := by
  unfold sitesFrom
  rw [origins_append vert rev a A B o pos, List.flatMap_append]

end FLatticePaper.Tiles.SiteConcat
