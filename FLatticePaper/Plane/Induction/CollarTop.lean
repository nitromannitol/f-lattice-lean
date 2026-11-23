import FLatticePaper.Plane.Induction.CollarBottomSquare
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! Task 72 (hcollar, band (a), the top class). The centre reflection `z ↦ R − z`, with `R = centre = U + V + (1, −1) =
(n + 1, 2n + d − 1)`, preserves the strict set, and it maps the free H witness `w + V` of a top centre to a free H point
`R − (w + V)` (grades `t ↦ L − t`, `s ↦ T + 2n − s`). So the top square of `c` is the bottom square of `R − c`. -/

namespace FLatticePaper.CollarTop

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.CollarBottomCases
  FLatticePaper.CollarBottomSquare FLatticePaper.CollarGlue FLatticePaper.AndOrRank

/-- The centre in coordinates. -/
theorem centre_eq (frame : ChildFrame) :
    frame.centre = (frame.child.num + 1, 2 * frame.child.num + frame.child.den - 1) := by
  unfold ChildFrame.centre
  rw [ChildFrame.child_modifiedDeck_kernel, ChildFrame.child_modifiedDeck_transverse]
  refine Prod.ext (by simp) (by simp; ring)

/-- The centre reflection preserves the strict set. -/
theorem strict_reflect (n d : ℤ) (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (z : Site) :
    StrictInterior n d ((n + 1, 2 * n + d - 1) - z) ↔ StrictInterior n d z := by
  have hpar : EvenSite ((n + 1, 2 * n + d - 1) - z) ↔ EvenSite z := by
    unfold EvenSite
    simp only [Prod.fst_sub, Prod.snd_sub]
    omega
  by_cases he : EvenSite z
  · rw [strict_even_iff n d _ (hpar.mpr he), strict_even_iff n d z he]
    simp only [Prod.fst_sub, Prod.snd_sub]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [strict_odd_iff n d _ (fun h => he (hpar.mp h)), strict_odd_iff n d z he]
    simp only [Prod.fst_sub, Prod.snd_sub]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The closed polygon in explicit grades (the disjunction of `mem_closedPolygon_iff`). -/
def EDisj (n d T a b : ℤ) : Prop :=
  ((a + b) % 2 = 0 ∧ 2 - T ≤ n * a - d * b ∧ n * a - d * b ≤ d + n - 2 ∧ 0 ≤ (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T + 2 * n) ∨
    (¬ (a + b) % 2 = 0 ∧ n - T ≤ n * a - d * b ∧ n * a - d * b ≤ d ∧ 2 - d + n ≤ (d + n) * a + (d - n) * b ∧
      (d + n) * a + (d - n) * b ≤ T + d + n - 2)

/-- The H spectrum in explicit grades. -/
def SpecH (n d a b : ℤ) : Prop :=
  ((n * a - d * b) % 2 = 0 ∧ 2 ≤ n * a - d * b ∧ n * a - d * b ≤ d + n - 2) ∨
    ((n * a - d * b) % 2 = 1 ∧ n ≤ n * a - d * b ∧ n * a - d * b ≤ d)

/-- The closed polygon membership in explicit grades. -/
theorem mem_closedPolygon_EDisj (frame : ChildFrame) (z : Site) :
    z ∈ frame.closedPolygon ↔
      EDisj frame.child.num frame.child.den frame.child.periodDenominator z.1 z.2 :=
  frame.mem_closedPolygon_iff z

/-- The grade reflection `w ↦ (d + 1, n − 1) − w` keeps the closed polygon and the H spectrum; the point below is out. -/
theorem reflect_pure (n d T a b : ℤ) (hn0 : 0 < n) (hnd : n + 2 ≤ d) (hnodd : n % 2 = 1) (hdodd : d % 2 = 1)
    (hT : T = d ^ 2 + 2 * d * n - n ^ 2) (hE : EDisj n d T a b) (hS : SpecH n d a b) :
    EDisj n d T (d + 1 - a) (n - 1 - b) ∧ ¬ EDisj n d T (d + 1 - a) (n - 1 - b - 1) ∧
      SpecH n d (d + 1 - a) (n - 1 - b) := by
  have hT0 : 0 ≤ T := by rw [hT]; nlinarith
  have hpt := t_parity n d a b hnodd hdodd
  have ht1 : n * (d + 1 - a) - d * (n - 1 - b) = (d + n) - (n * a - d * b) := by ring
  have ht2 : n * (d + 1 - a) - d * (n - 1 - b - 1) = (d + n) - (n * a - d * b) + d := by ring
  have hs1 : (d + n) * (d + 1 - a) + (d - n) * (n - 1 - b) =
      T + 2 * n - ((d + n) * a + (d - n) * b) := by
    rw [hT]; ring
  have hs2 : (d + n) * (d + 1 - a) + (d - n) * (n - 1 - b - 1) =
      T + 2 * n - ((d + n) * a + (d - n) * b) - (d - n) := by
    rw [hT]; ring
  unfold EDisj SpecH at *
  rw [ht1, hs1, ht2, hs2]
  generalize hτ : n * a - d * b = τ at *
  generalize hσ : (d + n) * a + (d - n) * b = σ at *
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- The free H set is invariant under `w ↦ R − (w + V)`: `t ↦ L − t`, `s ↦ T + 2n − s`. -/
theorem freeH_reflect (frame : ChildFrame) {w : Site} (hw : w ∈ frame.freeH) :
    frame.centre - (w + frame.child.modifiedDeck.transverse) ∈ frame.freeH := by
  obtain ⟨hwE, -, hwsp⟩ := hw
  obtain ⟨hn0, hnd1, hd2, -, hT⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  have hxc : frame.centre - (w + frame.child.modifiedDeck.transverse) =
      (frame.child.den + 1 - w.1, frame.child.num - 1 - w.2) := by
    rw [centre_eq, ChildFrame.child_modifiedDeck_transverse]
    ext <;> simp <;> ring
  have hE : EDisj frame.child.num frame.child.den frame.child.periodDenominator w.1 w.2 :=
    (mem_closedPolygon_EDisj frame w).mp hwE
  have hS : SpecH frame.child.num frame.child.den w.1 w.2 := hwsp
  obtain ⟨h1, h2, h3⟩ := reflect_pure frame.child.num frame.child.den frame.child.periodDenominator w.1 w.2
    hn0 hnd hnodd hdodd hT hE hS
  rw [hxc]
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, h3⟩
  · exact (mem_closedPolygon_EDisj frame _).mpr h1
  · intro hm
    exact h2 ((mem_closedPolygon_EDisj frame _).mp hm)

/-- The centre reflection in the frame's own centre. -/
theorem strict_reflect_centre (frame : ChildFrame) (z : Site) :
    StrictInterior frame.child.num frame.child.den (frame.centre - z) ↔
      StrictInterior frame.child.num frame.child.den z := by
  obtain ⟨-, -, -, -, -⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  rw [centre_eq]
  exact strict_reflect _ _ hnodd hdodd z

/-- A top witness gives a bottom witness for the reflected centre `R − c`. -/
theorem top_bottom_witness (frame : ChildFrame) {c : Site} (hT : TopArc frame c) :
    BottomArc frame (frame.centre - c) := by
  obtain ⟨v, hvA, hvB, hv⟩ := hT
  refine ⟨frame.centre - v, ?_, ?_, ?_⟩
  · have e : (frame.centre - v).1 - (frame.centre - c).1 = c.1 - v.1 := by
      simp only [Prod.fst_sub]
      ring
    rw [e, abs_sub_comm]
    exact hvA
  · have e : (frame.centre - v).2 - (frame.centre - c).2 = c.2 - v.2 := by
      simp only [Prod.snd_sub]
      ring
    rw [e, abs_sub_comm]
    exact hvB
  · have h := freeH_reflect frame hv
    rwa [sub_add_cancel] at h

/-- The square reflection `(x, y) ↦ (R1 − x, R2 − y)` sends the lower-right square of `(a, b)` to the upper-left square
of `(R1 − a, R2 − b)`. -/
theorem square_reflect (R1 R2 a b x y : ℤ) (h : (x, y) ∈ squareCorners a (b - 1)) :
    (R1 - x, R2 - y) ∈ squareCorners (R1 - a - 1) (R2 - b) := by
  simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h ⊢
  omega

/-- **The top class.** A strict top centre `c` with `R − c ≠ (1,1)` has its whole top square strict. -/
theorem top_square_strict (frame : ChildFrame) {c : Site}
    (hcS : StrictInterior frame.child.num frame.child.den c) (hne : frame.centre - c ≠ (1, 1))
    (hT : TopArc frame c) :
    ∀ c' ∈ squareCorners c.1 (c.2 - 1), StrictInterior frame.child.num frame.child.den c' := by
  have hcs' : StrictInterior frame.child.num frame.child.den (frame.centre - c) :=
    (strict_reflect_centre frame c).mpr hcS
  have key := bottom_square_strict frame hcs' hne (top_bottom_witness frame hT)
  intro c' hc'
  obtain ⟨x, y⟩ := c'
  have hmem : frame.centre - (x, y) ∈ squareCorners ((frame.centre - c).1 - 1) (frame.centre - c).2 :=
    square_reflect frame.centre.1 frame.centre.2 c.1 c.2 x y hc'
  exact (strict_reflect_centre frame (x, y)).mp (key _ hmem)

end FLatticePaper.CollarTop
