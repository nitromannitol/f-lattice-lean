import FLatticePaper.Plane.Induction.StrongResidual
import FLatticePaper.Plane.Induction.MatchedPolicy
import FLatticePaper.Plane.Induction.W1Pointers
import FLatticePaper.Plane.Induction.W1ZeroPitch
import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # Task 79 (hagree): the zero-pitch rank of the conjugate policy, its transport to the sheets, and the C policy as a reflection

* `policy_zeroPitch_rank`: for a reduced strong residual, the conjugate's policy from `F2F3_policy` (increments `(−a, c η)`, taken with
  `a = 1`, `c = 2`) has a strict rank with increments `−λ` along `U` and `2ηλ` along `V`, hence EXACTLY periodic under
  `W = 2η U + V` (the zero-pitch rank of `K = P + 2J`). This is the note's hypothesis 2, for the conjugate policy.
* `zTurn_add_W`, `sheetRank_W_periodic`, `sheetRankC_W_periodic`: the parent map `Z` carries the sheet translation `(W₂, −W₁)` to the
  parent translation `W`, so the sheet ranks `r (Z (c − lv))` and `r (Z (centre − c − lv))` are periodic under `(W₂, −W₁)`.
* `sheetPolicyC_of_sheetPolicyA`: with the exchange centre `I + 2 lv`, the C-sheet policy at `(c, i)` is the reflection of the A-sheet
  policy, so an A edge is a C edge whenever its parent edge is black or forced (`OldPolicyData.reflection`).
* `hagree_at_reflected_tie`: at a tie with binary laplacian, the common arrow `pointerOf QA c` is retained by the C policy when the parent
  edge of the pointer is black or forced. A white parent with a non-forced pointer is NOT covered: this is the residual of `hagree`. -/

namespace FLatticePaper.W1Hagree

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1ZeroPitch

/-- **The zero-pitch rank of the conjugate policy** (note hypothesis 2): a quota policy with a strict rank that is exactly periodic under
`W = 2η U + V`, from the reduced strong residual. -/
theorem policy_zeroPitch_rank {u : Word} (R : StrongResidualReduced u) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    ∃ policy : Site → Site → Prop, RetainQuota (standardField u) policy ∧
      ∃ rank : Site → ℤ, (∀ x i, policy x i → rank i < rank x) ∧
        ∀ z, rank (z + (2 * η) • (frameAt u).child.modifiedDeck.kernel +
          (frameAt u).child.modifiedDeck.transverse) = rank z := by
  obtain ⟨policy, hq, -, hrk⟩ := R.F2F3_policy η hη
  have h12 := hrk 1 2 (by norm_num) (by norm_num)
  unfold RankWithIncrements at h12
  obtain ⟨rank, lam, -, hstrict, hU, hV⟩ := h12
  refine ⟨policy, hq, rank, hstrict, fun z => ?_⟩
  have hUs := shift_zsmul (f := rank) (v := (frameAt u).child.modifiedDeck.kernel) (c := -lam)
    (fun w => by linear_combination hU w) (2 * η) z
  have hV' := hV (z + (2 * η) • (frameAt u).child.modifiedDeck.kernel)
  rw [hUs] at hV'
  linear_combination hV'

/-- The parent map `Z x = (−x₂, x₁ − 1)` carries the sheet translation `(W₂, −W₁)` to the parent translation `W`. -/
theorem zTurn_add_W (W x : Site) : zTurn (x + (W.2, -W.1)) = zTurn x + W := by
  unfold zTurn
  ext <;> simp <;> ring

/-- The sheet A rank `r (Z (c − lv))` is periodic under the sheet translation `(W₂, −W₁)`, when `r` is `W`-periodic. -/
theorem sheetRank_W_periodic (r : Site → ℤ) (W : Site) (hW : ∀ z, r (z + W) = r z) (lv c : Site) :
    r (zTurn (c + (W.2, -W.1) - lv)) = r (zTurn (c - lv)) := by
  have e : c + (W.2, -W.1) - lv = (c - lv) + (W.2, -W.1) := by
    ext <;> simp <;> ring
  rw [e, zTurn_add_W, hW]

/-- The sheet C rank `r (Z (centre − c − lv))` is periodic under the sheet translation `(W₂, −W₁)`, when `r` is `W`-periodic. -/
theorem sheetRankC_W_periodic (r : Site → ℤ) (W : Site) (hW : ∀ z, r (z + W) = r z) (lv centre c : Site) :
    r (zTurn (centre - (c + (W.2, -W.1)) - lv)) = r (zTurn (centre - c - lv)) := by
  have e : centre - (c + (W.2, -W.1)) - lv = (centre - c - lv) + (-(W.2), W.1) := by
    ext <;> simp <;> ring
  have hz : ∀ x : Site, zTurn (x + (-(W.2), W.1)) = zTurn x - W := by
    intro x
    unfold zTurn
    ext <;> simp <;> ring
  have hW' : ∀ y : Site, r (y - W) = r y := by
    intro y
    have h1 := hW (y - W)
    rw [sub_add_cancel] at h1
    exact h1.symm
  rw [e, hz, hW']

/-- **The reflection of the matched policy** (task 79): with the exchange centre `I + 2 lv`, the C-sheet policy at `(c, i)` holds
whenever the A-sheet policy holds at `(c, i)` and the parent edge of `(c, i)` is black or forced (`OldPolicyData.reflection`). -/
theorem sheetPolicyC_of_sheetPolicyA {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed η) (lv c i : Site)
    (hroot : laplacian G (zTurn (c - lv)) = -1 ∨
      SquareClauses.ForcedEdge G (fun _ _ => False) (zTurn (c - lv)) (zTurn (i - lv)))
    (h : sheetPolicyA P lv c i) :
    sheetPolicyC P lv (reflectionI + lv + lv) c i := by
  have key : parentPolicy P (reflectionI - (c - lv)) (reflectionI - (i - lv)) :=
    parentPolicy_reflection P (c := c - lv) (i := i - lv) h hroot
  have e : ∀ x : Site, reflectionI + lv + lv - x - lv = reflectionI - (x - lv) := by
    intro x
    unfold reflectionI
    ext <;> simp <;> ring
  unfold sheetPolicyC sheetPolicyA
  rw [e c, e i]
  exact key

/-- **The common arrow at a reflected tie** (task 79, partial hagree): at a tie with binary laplacian, the pointer `pointerOf QA c` of the
A policy is retained by the C policy, provided the parent edge of the pointer is black or forced. The white parent with a non-forced pointer
is the residual of `hagree`. -/
theorem hagree_at_reflected_tie {η : ℤ} {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop}
    (P : OldPolicyData frame G seed η) (F : Field) (lv c : Site)
    (hq : RetainQuota F (sheetPolicyA P lv))
    (hbin : laplacian F c = -1 ∨ laplacian F c = 0)
    (hroot : laplacian G (zTurn (c - lv)) = -1 ∨
      SquareClauses.ForcedEdge G (fun _ _ => False) (zTurn (c - lv))
        (zTurn (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P lv) c - lv))) :
    sheetPolicyC P lv (reflectionI + lv + lv) c (FLatticePaper.W1Pointers.pointerOf (sheetPolicyA P lv) c) :=
  sheetPolicyC_of_sheetPolicyA P lv c _ hroot (FLatticePaper.W1Pointers.pointerOf_retained F _ hq c hbin)

/-- **Uniqueness of forced inputs** (task 79, step 2 of the forcing argument): under a satisfying white selection of `F`, a white site
has at most one forced input, so two forced arrows of `F` at a white coincide (`forced_sound`, the empty clause excluded). -/
theorem forced_input_unique {F : Field} {sel : Site → Site}
    (hsel : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hsq : ∀ a b : ℤ, SquareClauses.SquareClauseSat F sel a b) {c i j : Site}
    (hi : SquareClauses.ForcedEdge F (fun _ _ => False) c i)
    (hj : SquareClauses.ForcedEdge F (fun _ _ => False) c j) : i = j := by
  have h1 := SquareClauses.forced_sound F (fun _ _ => False) sel hsel (fun _ _ h => h.elim) hsq c i hi
  have h2 := SquareClauses.forced_sound F (fun _ _ => False) sel hsel (fun _ _ h => h.elim) hsq c j hj
  exact h1.symm.trans h2

end FLatticePaper.W1Hagree
