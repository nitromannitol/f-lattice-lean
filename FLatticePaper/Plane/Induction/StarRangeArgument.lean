import FLatticePaper.Plane.Induction.StarRangeProof

/-! The range argument of the archive behind S1 and S2 (task 33, part B).

The archive's inputs, for `D = starDiff F σ`, `σ = shortShift` (even):
* `triple` (STRONG_PRICE section 3): on every full star of a site `e` of `E`, `D` takes values in a window `[c, c+2]`
  with `c` even ("a triple of consecutive integers with EVEN endpoints");
* `base` (STRONG_PRICE section 2, "D+(E) ⊂ {0,1,2} by recurrent M boundary comparison"): the window of a full star of a
  site of `E` is the window at level `0`.

The archive's unit-jump argument (section 3, "difference of two binary Laplacians shows an edge jump of two impossible")
is proved here: `laplacian (starDiff F σ) e = laplacian F e − laplacian F (e + σ)` for even `σ`, so with binary
Laplacians `laplacian (starDiff F σ) e ∈ {−1, 0, 1}`, and a jump `0 — 2` at `e` would force `laplacian (starDiff F σ) e`
to be at least `2` or at most `−2`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The full star of a site: the site and its two inputs. -/
def FullStar (e x : Site) : Prop := x = e ∨ x = incomingNeg e ∨ x = incomingPos e

theorem laplacian_starDiff (F : Field) (σ e : Site) (hσ : EvenSite σ) :
    laplacian (starDiff F σ) e = laplacian F e - laplacian F (e + σ) := by
  unfold laplacian starDiff
  rw [← incomingNeg_add_of_even e σ hσ, ← incomingPos_add_of_even e σ hσ]
  ring

/-- A binary field has binary difference: `laplacian (starDiff F σ) e ∈ {−1, 0, 1}`. -/
theorem laplacian_starDiff_mem (F : Field) (σ e : Site) (hσ : EvenSite σ)
    (hbin : ∀ site, laplacian F site = -1 ∨ laplacian F site = 0) :
    -1 ≤ laplacian (starDiff F σ) e ∧ laplacian (starDiff F σ) e ≤ 1 := by
  rw [laplacian_starDiff F σ e hσ]
  rcases hbin e with h1 | h1 <;> rcases hbin (e + σ) with h2 | h2 <;> rw [h1, h2] <;> constructor <;> norm_num

/-- The local inputs of the range argument for `D = starDiff F σ` on the closed polygon. -/
structure StarArgumentInputs (frame : ChildFrame) (F : Field) : Prop where
  triple : ∀ e ∈ frame.closedPolygon, ∃ c : ℤ, c % 2 = 0 ∧
    ∀ x, FullStar e x → c ≤ starDiff F frame.shortShift x ∧ starDiff F frame.shortShift x ≤ c + 2
  base : ∀ e ∈ frame.closedPolygon, ∀ c : ℤ,
    (∀ x, FullStar e x → c ≤ starDiff F frame.shortShift x ∧ starDiff F frame.shortShift x ≤ c + 2) → c = 0

/-- The range of `D` on the full stars of `E` (hence on `E` and on its inputs), from the triple and the base. -/
theorem star_range_of_argument (frame : ChildFrame) {F : Field} (inputs : StarArgumentInputs frame F)
    {e : Site} (he : e ∈ frame.closedPolygon) (x : Site) (hx : FullStar e x) :
    starDiff F frame.shortShift x = 0 ∨ starDiff F frame.shortShift x = 1 ∨ starDiff F frame.shortShift x = 2 := by
  obtain ⟨c, -, hc⟩ := inputs.triple e he
  have h0 : c = 0 := inputs.base e he c (fun y hy => hc y hy)
  subst h0
  obtain ⟨h1, h2⟩ := hc x hx
  omega

/-- The unit jump on the edges into `E`, from the range on the full stars and the binary difference. -/
theorem unit_jump_of_argument (frame : ChildFrame) {F : Field} (hσ : EvenSite frame.shortShift)
    (hbin : ∀ site, laplacian F site = -1 ∨ laplacian F site = 0)
    (inputs : StarArgumentInputs frame F) :
    ∀ e ∈ frame.closedPolygon, ∀ u, Edge u e →
      -1 ≤ starDiff F frame.shortShift u - starDiff F frame.shortShift e ∧
        starDiff F frame.shortShift u - starDiff F frame.shortShift e ≤ 1 := by
  intro e he u hu
  have hu' : u = incomingNeg e ∨ u = incomingPos e := hu
  have hlap := laplacian_starDiff_mem F frame.shortShift e hσ hbin
  unfold laplacian at hlap
  have hneg := star_range_of_argument frame inputs he (incomingNeg e) (Or.inr (Or.inl rfl))
  have hpos := star_range_of_argument frame inputs he (incomingPos e) (Or.inr (Or.inr rfl))
  have hc := star_range_of_argument frame inputs he e (Or.inl rfl)
  rcases hu' with rfl | rfl <;> rcases hneg with h1 | h1 | h1 <;> rcases hpos with h2 | h2 | h2 <;>
    rcases hc with h3 | h3 | h3 <;> simp only [h1, h2, h3] at hlap ⊢ <;> omega

/-- The short step `shortShift = (2 ε d, 2 ε n)` is even. -/
theorem evenSite_shortShift (frame : ChildFrame) : EvenSite frame.shortShift := by
  unfold EvenSite ChildFrame.shortShift
  simp only
  rw [show 2 * frame.eps * frame.parents.odd.den + 2 * frame.eps * frame.parents.odd.num
      = 2 * (frame.eps * frame.parents.odd.den + frame.eps * frame.parents.odd.num) by ring]
  exact Int.mul_emod_right 2 _

/-- S1 and S2 from the archive's range argument: the triple and the base give the range on `E` and its inputs, and the
binary difference gives the unit jumps; then `starRange_S1S2_of_inputs`. -/
theorem starRange_S1S2_of_argument (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hbin : ∀ site, laplacian F site = -1 ∨ laplacian F site = 0)
    (inputs : StarArgumentInputs frame F) :
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
      NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) :=
  starRange_S1S2_of_inputs frame hper
    { rangeE := fun e he => star_range_of_argument frame inputs he e (Or.inl rfl)
      rangeIn := fun _ he u hu => star_range_of_argument frame inputs he u (Or.inr hu)
      unitJump := unit_jump_of_argument frame (evenSite_shortShift frame) hbin inputs }

end FLatticePaper.Induction
