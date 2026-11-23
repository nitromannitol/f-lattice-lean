import FLatticePaper.Plane.Induction.W1Constructor

/-! Task 60: the forcing assembly of `W1Forced` from a return structure (W1_CONSTRUCTOR §5–§6).

`W1Forced n d F` asks that every strict-interior white is forced by a derivation `ForcedEdgeIn` whose unit squares lie in the
strict interior. A unit step at a white `c` needs one square `Q ∋ c` in `R`, one rejected input `o = out c` outside `Q`, and, for every
other white corner `c'` of `Q`, the derivation of `c'` at its own pointer `out c'` lying in `Q`. The archive's descending induction
(§5: "descend through the finitely many rank values"; §6: "the quotient bulk DAG has no cycle") supplies exactly these data. This
module proves that the data give the forcing by well-founded induction on the return relation `r c' c` (a white corner `c'` of the
square of `c` is handled before `c`). Nothing here is geometric: the square, the pointer and the return relation are the inputs
that §§3–6 must produce.

`forcing_of_measure` is the case `r c' c = μ c' < μ c` for a natural-valued rank `μ`, and is the form in which the rank of the
§5 descent enters. -/

namespace FLatticePaper.W1Forcing

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.W1

/-- **The forcing assembly.** Given a pointer `out` and, at every strict white `c`, a square `Q ∋ c` inside `R` with rejected input
`out c ∉ Q`, whose other white corners `c'` point into `Q` (`out c'`) and return to `c` in the well-founded relation `r`, every
strict white is forced. -/
theorem forcing_of_wf (n d : ℤ) (F : Field) (out : Site → Site) (r : Site → Site → Prop) (hr : WellFounded r)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → r c' c)) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) := by
  intro c
  induction c using hr.induction with
  | _ c ih =>
    intro hRc hw
    obtain ⟨a, b, hc, hR, hout', hin, hdec⟩ := hsq c hRc hw
    exact ForcedEdgeIn.unit out hR hc hw (hout c hRc hw) hout' hin
      (fun c' hc' hne hw' => ih c' (hdec c' hc' hne hw') (hR c' hc') hw')

/-- The natural-rank form: the return relation is `μ c' < μ c`. -/
theorem forcing_of_measure (n d : ℤ) (F : Field) (out : Site → Site) (μ : Site → ℕ)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → μ c' < μ c)) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_wf n d F out (InvImage (· < ·) μ) (InvImage.wf μ wellFounded_lt) hout hsq

/-- The lexicographic form (§5): the rank of a site is a pair `(leading, rank)`, with the leading component the tie indicator
`1_{Ψ = 0}` and the second component the parent rank of the sheet that is active (A on `Ψ ≥ 0`, C on `Ψ < 0`). A return edge that
drops the leading component (tie to strict) or keeps it and drops the rank decreases the pair lexicographically; the pair order
is well-founded, so the descent gives the forcing. -/
theorem forcing_of_lex (n d : ℤ) (F : Field) (out : Site → Site) (μ : Site → ℕ × ℕ)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → Prod.Lex (· < ·) (· < ·) (μ c') (μ c))) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_wf n d F out (InvImage (Prod.Lex (· < ·) (· < ·)) μ)
    (InvImage.wf μ (WellFounded.prod_lex wellFounded_lt wellFounded_lt)) hout hsq

/-- §6, the finite step: a relation supported on a finite set with no transitive cycle is well-founded (the lift of a cycle of the
bulk graph into the finite strict interior, then acyclicity). -/
theorem wellFounded_of_finite_acyclic {α : Type} (S : Set α) (hS : S.Finite) (r : α → α → Prop)
    (hz : ∀ x y, r x y → x ∈ S ∧ y ∈ S) (hacyc : ∀ x, ¬ Relation.TransGen r x x) : WellFounded r := by
  classical
  haveI : Finite S := hS.to_subtype
  let r' : S → S → Prop := fun a b => Relation.TransGen r a.1 b.1
  haveI : IsTrans S r' := ⟨fun a b c hab hbc => Relation.TransGen.trans hab hbc⟩
  haveI : Std.Irrefl r' := ⟨fun a h => hacyc a.1 h⟩
  have wf' : WellFounded r' := Finite.wellFounded_of_trans_of_irrefl r'
  have hS' : ∀ a : S, Acc r a.1 := by
    intro a
    induction a using wf'.induction with
    | _ a ih =>
      refine Acc.intro a.1 (fun y hy => ?_)
      have hyS := (hz y a.1 hy).1
      exact ih ⟨y, hyS⟩ (Relation.TransGen.single hy)
  refine ⟨fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact hS' ⟨x, hx⟩
  · exact Acc.intro x (fun y hy => absurd (hz y x hy).2 hx)

/-- The forcing assembly with acyclicity in place of a rank: on the finite strict interior, an acyclic return relation gives the
forcing (§6's conclusion, that the bulk DAG has no cycle, is exactly the acyclicity hypothesis). -/
theorem forcing_of_finite_acyclic (n d : ℤ) (F : Field) (out : Site → Site) (r : Site → Site → Prop)
    (hfin : {c : Site | StrictInterior n d c}.Finite)
    (hsupp : ∀ x y, r x y → StrictInterior n d x ∧ StrictInterior n d y)
    (hacyc : ∀ c, ¬ Relation.TransGen r c c)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → r c' c)) :
    ∀ c, StrictInterior n d c → laplacian F c = 0 →
      ForcedEdgeIn F (StrictInterior n d) (fun _ _ => False) c (out c) :=
  forcing_of_wf n d F out r
    (wellFounded_of_finite_acyclic _ hfin r (fun x y h => hsupp x y h) hacyc) hout hsq

/-- **`W1Forced` from a return structure.** -/
theorem W1Forced_of_measure (n d : ℤ) (F : Field) (out : Site → Site) (μ : Site → ℕ)
    (hout : ∀ c, StrictInterior n d c → laplacian F c = 0 → (out c = incomingNeg c ∨ out c = incomingPos c))
    (hsq : ∀ c, StrictInterior n d c → laplacian F c = 0 → ∃ a b : ℤ,
      c ∈ squareCorners a b ∧ (∀ c' ∈ squareCorners a b, StrictInterior n d c') ∧ out c ∉ squareCorners a b ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ out c' ∈ squareCorners a b ∧ (out c' = incomingNeg c' ∨ out c' = incomingPos c'))) ∧
      (∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → μ c' < μ c)) :
    W1Forced n d F :=
  fun z hz hw => ⟨out z, forcing_of_measure n d F out μ hout hsq z hz hw⟩

end FLatticePaper.W1Forcing
