import FLatticePaper.Tiles.SiteJunction
import FLatticePaper.Tiles.IncrementCounts
import FLatticePaper.Tiles.StandardBoundary
import FLatticePaper.Tiles.BinaryWords
import FLatticePaper.Construction.OffsetTables

/-! Clause (b) of `lemma:standard_tile_properties` and the horizontal part of clause (c), over the origins of the SiteStrings
model (`SiteStrings.lastOrigin`).

* (b)(i): the last origin of the forward horizontal string `hWordOf w false` is `almostV₁ (oddBottom w) − (1,1)`.
* (b)(ii): the last origin of the reversed vertical string of `vWordOf w false` (started at `(1,1)`, shifted by `c − (1,1)` with
  `c = 0`) is `almostV₂ (oddRight w) + (2,−1)`.
* (c), horizontal: the first origin of the reversed horizontal string, `startPos false true = (1,−2)`, is that last vertical
  origin minus `almostV₂ (oddRight w)` (up to the shift `(1,1)`): the reversed horizontal string of the neighbour starts where
  the reversed vertical string ends.

The horizontal fold uses the step `stepH`, the vertical fold the step `dxdy true true`. The counts come from
`IncrementCounts` (`hIncSum_childP`, `vertWord_lastCorner`) and the endpoint letters from `almost_palindrome_two`. -/

namespace FLatticePaper.Tiles.StringCorners

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.SiteJunction FLatticePaper.Tiles.SiteConcat FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.StandardClause

/-! ### Horizontal: the last origin is the total step of the tail -/

/-- The last origin of a forward horizontal string started from the empty state is the total step of its tail. -/
theorem lastOrigin_horizontal (x : Letter) (X : List Letter) :
    lastOrigin false false (x :: X) = some (sumStep X) := by
  unfold lastOrigin
  rw [show startPos false false = (0, 0) from rfl]
  cases X with
  | nil => simp [origins, sumStep]
  | cons y Y =>
    have hne := origins_ne_nil_of (some x) (0, 0) (L := y :: Y) (List.cons_ne_nil _ _)
    have e := endOrigin_none_cons x (y :: Y) (0, 0)
    unfold endOrigin at e
    have hsome : ((origins false false none (0, 0) (x :: y :: Y)).getLast?.map (·.1)).isSome := by
      rw [show origins false false none (0, 0) (x :: y :: Y) =
          ((0, 0), x, false) :: origins false false (some x) (0, 0) (y :: Y) from rfl]
      rw [getLast?_cons_of_ne _ _ hne]
      cases h : (origins false false (some x) (0, 0) (y :: Y)).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
      | some z => simp
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
    rw [ha] at e ⊢
    simp only [Option.getD_some] at e
    rw [e]
    simp

/-! ### Vertical: the last origin is the chain of vertical steps -/

theorem dxdy_true_true (prev l : Letter) :
    dxdy true true prev l = ((if prev = .p then -1 else 0), if l = .p then 1 else 2) := by
  cases prev <;> cases l <;> rfl

/-- The total step of a reversed vertical string whose first letter is preceded by `pr`. -/
def vchain : Letter → List Letter → ℤ × ℤ
  | _, [] => (0, 0)
  | pr, l :: ls => dxdy true true pr l + vchain l ls

theorem origins_true_true_some_cons (pr l : Letter) (pos : ℤ × ℤ) (ls : List Letter) :
    origins true true (some pr) pos (l :: ls) =
      (pos + dxdy true true pr l, l, false) :: origins true true (some l) (pos + dxdy true true pr l) ls := rfl

theorem origins_true_true_ne (o : Option Letter) (pos : ℤ × ℤ) (l : Letter) (L : List Letter) :
    origins true true o pos (l :: L) ≠ [] := by
  cases o with
  | none => exact List.cons_ne_nil _ _
  | some pr => rw [origins_true_true_some_cons]; exact List.cons_ne_nil _ _

/-- The last origin of a reversed vertical string started from `pr` at `pos` is `pos` plus the chain. -/
theorem vlast_some (pr : Letter) : ∀ (pos : ℤ × ℤ) (ls : List Letter), ls ≠ [] →
    (origins true true (some pr) pos ls).getLast?.map (·.1) = some (pos + vchain pr ls)
  | pos, [], h => absurd rfl h
  | pos, [l], _ => by
      rw [origins_true_true_some_cons]
      simp [origins, vchain]
  | pos, l :: l' :: ls, _ => by
      have hT := origins_true_true_ne (some l) (pos + dxdy true true pr l) l' ls
      rw [origins_true_true_some_cons, getLast?_cons_of_ne _ _ hT]
      have ih := vlast_some l (pos + dxdy true true pr l) (l' :: ls) (List.cons_ne_nil _ _)
      rw [ih]
      simp only [vchain, Option.some.injEq]
      abel

theorem lastOrigin_vertical (x : Letter) (X : List Letter) :
    lastOrigin true true (x :: X) = some ((1, 1) + vchain x X) := by
  unfold lastOrigin
  rw [show startPos true true = (1, 1) from rfl]
  rw [show origins true true none (1, 1) (x :: X) = ((1, 1), x, false) :: origins true true (some x) (1, 1) X from rfl]
  cases X with
  | nil => simp [vchain, origins]
  | cons y Y =>
    rw [getLast?_cons_of_ne _ _ (origins_true_true_ne (some x) (1, 1) y Y)]
    exact vlast_some x (1, 1) (y :: Y) (List.cons_ne_nil _ _)

/-- The chain of a reversed vertical string as a count formula: `−#p` of the predecessors, `#p + 2#q` of the letters. -/
theorem vchain_formula : ∀ (pr : Letter) (ls : List Letter),
    vchain pr ls = (-((pr :: ls).dropLast.count Letter.p : ℤ), (ls.count Letter.p : ℤ) + 2 * (ls.count Letter.q : ℤ))
  | pr, [] => by simp [vchain]
  | pr, l :: rest => by
      have ih := vchain_formula l rest
      rw [vchain, ih, dxdy_true_true]
      have hd : (pr :: l :: rest).dropLast = pr :: (l :: rest).dropLast :=
        List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)
      rw [hd]
      cases pr <;> cases l <;> simp <;> ring_nf

/-! ### Counts -/

theorem sumStep_eq_hIncSum : ∀ L : List Letter, sumStep L = hIncSum L
  | [] => by ext <;> simp [sumStep, hIncSum]
  | l :: L => by
    rw [sumStep, sumStep_eq_hIncSum L]
    cases l <;> ext <;> simp [hIncSum, stepH] <;> omega

/-! ### Clause (b)(i): the forward horizontal string -/

theorem clauseB_forward_last (w : Word) :
    lastOrigin false false (hWordOf w false) = some (almostV₁ (oddBottom w) - (1, 1)) := by
  have hW : hWordOf w false = (quadAt [] w).childP := rfl
  have hhead := ((almost_palindrome_two [] w).1 (by simp)).1
  rw [hW]
  cases hc : (quadAt [] w).childP with
  | nil => rw [hc] at hhead; simp at hhead
  | cons a rest =>
    rw [hc] at hhead
    have ha : a = Letter.q := by simpa using hhead
    subst ha
    rw [lastOrigin_horizontal, sum_oddBottom]
    congr 1
    have hI := hIncSum_childP w
    rw [hc] at hI
    have hs : sumStep (Letter.q :: rest) = hIncSum (Letter.q :: rest) := sumStep_eq_hIncSum _
    rw [hI, sumStep] at hs
    have h11 : stepH Letter.q = (1, 1) := by simp [stepH]
    rw [h11] at hs
    unfold texV1Odd fracOdd
    have h1 := congrArg Prod.fst hs
    have h2 := congrArg Prod.snd hs
    simp only [Prod.fst_add, Prod.snd_add] at h1 h2
    ext <;> simp <;> omega

/-! ### Clause (b)(ii): the reversed vertical string -/

theorem clauseB_vertical_last (w : Word) :
    lastOrigin true true (vWordOf w false).reverse = some (almostV₂ (oddRight w) + (2, -1)) := by
  have hQ := (almost_palindrome_two [] (Standard.swapW w)).1 (by simp)
  obtain ⟨-, -, hqh, hql⟩ := hQ
  unfold Standard.swapW at hqh hql
  have hvw : vWordOf w false = vertWord w := rfl
  rw [hvw]
  have hC := vertWord_lastCorner w
  have hvh : (vertWord w).head? = some .p := by
    unfold vertWord
    rw [List.head?_map, hqh]
    rfl
  have hvl : (vertWord w).getLast? = some .q := by
    unfold vertWord
    rw [List.getLast?_map, hql]
    rfl
  have hne : (vertWord w).reverse ≠ [] := by
    intro h
    have h' : vertWord w = [] := by simpa using h
    rw [h'] at hvl
    simp at hvl
  obtain ⟨a, rest, hA⟩ : ∃ a rest, (vertWord w).reverse = a :: rest := by
    cases h : (vertWord w).reverse with
    | nil => exact absurd h hne
    | cons a rest => exact ⟨a, rest, rfl⟩
  have ha : a = Letter.q := by
    have h1 := List.head?_reverse (l := vertWord w)
    rw [hA, hvl] at h1
    simpa using h1
  have hlast : (a :: rest).getLast? = some .p := by
    rw [← hA, List.getLast?_reverse, hvh]
  subst ha
  have hrne : rest ≠ [] := by
    intro h
    rw [h] at hlast
    simp at hlast
  have hrl : rest.getLast? = some .p := by
    rwa [getLast?_cons_of_ne _ _ hrne] at hlast
  obtain ⟨D, b, hrest⟩ : ∃ D b, rest = D ++ [b] := by
    rcases List.eq_nil_or_concat rest with h | ⟨L, b, h⟩
    · exact absurd h hrne
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  subst hrest
  have hb : b = Letter.p := by simpa using hrl
  subst hb
  rw [hA, lastOrigin_vertical, vchain_formula]
  have hdl : (Letter.q :: (D ++ [Letter.p])).dropLast = Letter.q :: D := by
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    simp
  have hpD : (D ++ [Letter.p]).count Letter.p = D.count Letter.p + 1 := by simp [List.count_append]
  have hqD : (D ++ [Letter.p]).count Letter.q = D.count Letter.q := by simp [List.count_append]
  have hp1 : (vertWord w).count Letter.p = D.count Letter.p + 1 := by
    have hp := (List.reverse_perm (vertWord w)).count_eq Letter.p
    rw [hA] at hp
    rw [← hp]
    simp [List.count_append]
  have hq1 : (vertWord w).count Letter.q = D.count Letter.q + 1 := by
    have hp := (List.reverse_perm (vertWord w)).count_eq Letter.q
    rw [hA] at hp
    rw [← hp]
    simp [List.count_append]
  have hqp : (Letter.q :: D).count Letter.p = D.count Letter.p := by simp
  rw [hdl, hqp, hpD, hqD, sum_oddRight]
  unfold texV2 fracOdd
  rw [hp1, hq1] at hC
  obtain ⟨hC1, hC2⟩ := hC
  congr 1
  ext <;> simp <;> omega

/-! ### Clause (c), horizontal: the reversed horizontal string starts where the reversed vertical string ends -/

/-- The offset of clause (c): the last reversed vertical origin, placed at `c − (1,1)`, minus the lattice vector `v₂`, is
the first origin `startPos false true = (1,−2)` of the reversed horizontal string. -/
theorem clauseC_horizontal (w : Word) :
    (lastOrigin true true (vWordOf w false).reverse).map
      (fun L => L - (1, 1) - almostV₂ (oddRight w)) = some (startPos false true) := by
  rw [clauseB_vertical_last, Option.map_some]
  congr 1
  have key : ∀ a : ℤ × ℤ, a + (2, -1) - (1, 1) - a = startPos false true := by
    intro a
    rw [show startPos false true = (1, -2) from rfl]
    ext <;> simp <;> ring
  exact key _

end FLatticePaper.Tiles.StringCorners
