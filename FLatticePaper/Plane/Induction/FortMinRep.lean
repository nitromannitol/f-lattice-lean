import FLatticePaper.Plane.Induction.RestrictedFortShift

/-! # W3 (hno, step 2 assembly): a restricted fort translates to one whose minimal pair is a representative

Step 2 of the Q1 no-fort (translate the set so that its minimum pair is at the fixed pair). The ingredients:

* the minimal grade site of a nonempty restricted fort with a lower bound `level ≤ K` (Mathlib `Int.exists_least_of_bdd`);
* the representative `PeriodDeck.exists_square_representative`: every site has a representative `r` in the finite set
  `residueSquare` with the same class, and `PeriodDeck.classCode_eq_iff` turns the class equality into `site − r ∈ span`
  (for `0 < det`, `modifiedDeck_det_pos`);
* the translate: `RestrictedFortShift.isRestrictedFort_shiftSet` (the restricted fort translated by the span element
  `t = m − r`), and the constant drift `K(z + t) = K z + inc` (`grade_hgrade`), which keeps the minimum at `r`.

`exists_fort_translate_min_rep` is the assembly: a restricted fort, bounded below by `level`, has a translate that is restricted,
contains a representative `r` of `residueSquare`, and has `K r` minimal on the translate. -/

namespace FLatticePaper.FortMinRep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.RestrictedFortShift

/-- The child modified deck has positive determinant (the argument of `permitsQ1_rank`). -/
theorem modifiedDeck_det_pos (frame : ChildFrame) : 0 < frame.child.modifiedDeck.det := by
  obtain ⟨hn1, hnd, -, -, -⟩ := frame.child_facts
  have e : frame.child.modifiedDeck.det = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
      - frame.child.num * frame.child.num := by
    unfold PeriodDeck.det
    rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
    simp only
    ring
  rw [e]
  nlinarith

/-- **The translation to a representative minimum (step 2).** A restricted fort `S` for `permitsQ1` with `level ≤ K` on
`S` (`K = P + roundedSlip`, the grade of the no-fort) has a span translate `shiftSet S t` that is again a restricted fort,
contains a representative `r` of `residueSquare`, and has `K r` minimal over the translate. -/
theorem exists_fort_translate_min_rep (frame : ChildFrame) (F : Field) (η : ℤ)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (hL : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c)
    {S : Set Site} (hres : IsRestrictedFort F (permitsQ1 frame F η) S) (hne : S.Nonempty) (level : ℤ)
    (hlev : ∀ z ∈ S, level ≤ frame.price F z + frame.roundedSlip F η z) :
    ∃ t ∈ frame.child.modifiedDeck.span,
      IsRestrictedFort F (permitsQ1 frame F η) (shiftSet S t) ∧
      ∃ r ∈ frame.child.modifiedDeck.residueSquare, r ∈ shiftSet S t ∧
        ∀ z ∈ shiftSet S t,
          frame.price F r + frame.roundedSlip F η r ≤ frame.price F z + frame.roundedSlip F η z := by
  classical
  -- the minimal grade site of `S`
  obtain ⟨m, hmS, hmin⟩ : ∃ m ∈ S, ∀ z ∈ S,
      frame.price F m + frame.roundedSlip F η m ≤ frame.price F z + frame.roundedSlip F η z := by
    obtain ⟨z0, hz0⟩ := hne
    have hbdd : ∃ b : ℤ, ∀ g : ℤ, (∃ z ∈ S, frame.price F z + frame.roundedSlip F η z = g) → b ≤ g := by
      refine ⟨level, ?_⟩
      rintro g ⟨z, hz, rfl⟩
      exact hlev z hz
    have hinh : ∃ g : ℤ, ∃ z ∈ S, frame.price F z + frame.roundedSlip F η z = g :=
      ⟨_, z0, hz0, rfl⟩
    obtain ⟨lb, ⟨m, hmS, hm⟩, hleast⟩ := Int.exists_least_of_bdd hbdd hinh
    refine ⟨m, hmS, fun z hz => ?_⟩
    rw [hm]
    exact hleast _ ⟨z, hz, rfl⟩
  -- the representative of `m` in `residueSquare`, and the span element `t = m − r`
  have hdet : frame.child.modifiedDeck.det ≠ 0 := ne_of_gt (modifiedDeck_det_pos frame)
  obtain ⟨r, hrSq, hcls⟩ := PeriodDeck.exists_square_representative frame.child.modifiedDeck
    (modifiedDeck_det_pos frame) m
  have ht : m - r ∈ frame.child.modifiedDeck.span :=
    (PeriodDeck.classCode_eq_iff frame.child.modifiedDeck hdet m r).mp hcls
  refine ⟨m - r, ht, ?_⟩
  -- the translate is a restricted fort
  have hEven : EvenSite (m - r) := FreePolicy.span_even frame ht
  obtain ⟨i, j, hij⟩ := ht
  have hLt : ∀ z, laplacian F (z + (m - r)) = laplacian F z := fun z => by
    rw [hij]
    exact hL z i j
  have hPt : ∀ c i', permitsQ1 frame F η (c + (m - r)) (i' + (m - r)) ↔ permitsQ1 frame F η c i' :=
    fun c i' => permitsQ1_shift frame F η hL (m - r) ⟨i, j, hij⟩ c i'
  have hfort : IsRestrictedFort F (permitsQ1 frame F η) (shiftSet S (m - r)) :=
    isRestrictedFort_shiftSet hEven hLt hPt hres
  refine ⟨hfort, r, hrSq, ?_, ?_⟩
  · -- `r + (m − r) = m ∈ S`
    show r + (m - r) ∈ S
    rw [show r + (m - r) = m by abel]
    exact hmS
  · -- the minimum at `r` is preserved by the translate (the drift along the span is a constant)
    obtain ⟨inc, hinc⟩ := grade_hgrade frame F η hPD hSD (m - r) ⟨i, j, hij⟩
    intro z hz
    have hz' : z + (m - r) ∈ S := hz
    have h1 := hmin (z + (m - r)) hz'
    have h2 := hinc z
    have h3 := hinc r
    have hrm : r + (m - r) = m := by abel
    simp only at h1 h2 h3
    rw [hrm] at h3
    linarith

end FLatticePaper.FortMinRep
