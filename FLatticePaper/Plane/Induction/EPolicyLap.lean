import FLatticePaper.Construction.EPolicy
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Construction.StaircaseLaplacian

/-!
# The laplacian of the reciprocal field on the native tile and its deck classes (task 118, W1 base)

The black and white classification of `reciprocalField k` at the native points (`stairEven_laplacian_on_raw`), the native
membership of the raw tile, and the invariance of the laplacian under the deck. Every site has the laplacian of its native
representative (`laplacian_eq_native_rep`).
-/

namespace FLatticePaper.EPolicy

open Classical FLatticePaper FLatticePaper.PureRank FLatticePaper.Construction FLatticePaper.Farey FLatticePaper.Induction

/-- A native point is a point of the raw tile of `stairEven` (both corners included). -/
theorem mem_raw_of_nativeP {d : ℤ} (hd : 3 ≤ d) {p : Pt} (h : NativeP d p) :
    p ∈ (BaseMask.stairEven.raw d).sites := by
  rw [BaseMask.mem_stairEven_raw_iff]
  obtain ⟨x, y⟩ := p
  unfold NativeP at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, Or.inr ⟨h5, h6⟩⟩
  · refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
    unfold BaseMask.StairEvenCorner
    exact Or.inl ⟨h1, h2⟩
  · refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inl ?_⟩
    unfold BaseMask.StairEvenCorner
    exact Or.inr ⟨h1, h2⟩

/-- The laplacian of a field with the stair periods, at a native point. -/
theorem laplacian_native_of_periods {d : ℤ} (hden : BaseMask.stairEven.Valid d) {F : Field}
    (hagree : (BaseMask.stairEven.raw d).Agrees F 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 d) F 0 (stairEvenConstantV d))
    {p : Pt} (hp : NativeP d p) :
    laplacian F p = if EvenSite p then (if p.1 = 1 then -1 else 0)
      else (if 0 < p.2 ∧ p.2 < d + 1 ∧ 1 < p.1 + p.2 ∧ p.1 + p.2 < d + 2 then -1 else 0) :=
  stairEven_laplacian_on_raw hden hagree hperiod p (mem_raw_of_nativeP hden.1 hp)

/-- The laplacian of the reciprocal field at `2k+3`, at a native point. -/
theorem laplacian_reciprocal_native (k : ℕ) {p : Pt} (hp : NativeP (2 * (k : ℤ) + 3) p) :
    laplacian (reciprocalField k) p =
      if EvenSite p then (if p.1 = 1 then -1 else 0)
      else (if 0 < p.2 ∧ p.2 < (2 * (k : ℤ) + 3) + 1 ∧ 1 < p.1 + p.2 ∧ p.1 + p.2 < (2 * (k : ℤ) + 3) + 2
        then -1 else 0) :=
  laplacian_native_of_periods (stairEven_valid_reciprocal k) (reciprocalField_spec k).1 (reciprocalField_spec k).2 hp

/-- The laplacian of the reciprocal field is invariant under the deck: a site has the laplacian of its native representative. -/
theorem laplacian_reciprocal_deck (k : ℕ) (p : Pt) (i j : ℤ) :
    laplacian (reciprocalField k) (p + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) =
      laplacian (reciprocalField k) p :=
  laplacian_add_combine (reciprocalField_spec k).2 p i j

theorem laplacian_reciprocal_rep (k : ℕ) (p : Pt) :
    laplacian (reciprocalField k) p = laplacian (reciprocalField k) (nativeRep (2 * (k : ℤ) + 3) p) := by
  obtain ⟨-, i, j, hij⟩ := nativeRep_spec (stairEven_valid_reciprocal k) p
  have h := laplacian_reciprocal_deck k (nativeRep (2 * (k : ℤ) + 3) p) i j
  rw [← hij] at h
  exact h

end FLatticePaper.EPolicy
