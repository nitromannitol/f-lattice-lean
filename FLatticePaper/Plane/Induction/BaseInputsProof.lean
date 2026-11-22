import FLatticePaper.Plane.Induction.BaseRange
import FLatticePaper.Plane.Induction.StarRangeArgument
import FLatticePaper.Plane.BellmanRank
import FLatticePaper.Plane.Induction.Strips

/-! Proofs of the inputs of the base range of the S1/S2 window (task 35).

The recurrent comparison principle of the B2 audit (section 1): "Apply recurrent comparison to M=F on E, against each
globally binary shifted/affine competitor. It suffices to check the inequalities on the actual inner boundary of X, which
is contained in the four boundary arcs of E." The general form is the one of EXACT_TAIL_AND_BARRIER: "For any admitted
integer F and finite D, F ≥ B on the incoming exterior boundary implies F ≥ B on D. If not, maximize the positive
integer B − F in D. The maximum set is a fort for B ... Recurrent B excludes that set." -/

namespace FLatticePaper

open Farey

/-- A binary field has no nonempty finite incoming fort: the recurrence used by the comparison. -/
def RecurrentField (field : Field) : Prop :=
  ∀ S : Finset Site, S.Nonempty → ¬ IsIncomingFort field (↑S : Set Site)

/-- The recurrent comparison principle: an admitted binary field `A` dominates a recurrent binary field `B` on a finite
set `D` as soon as it does on the incoming exterior boundary of `D`. -/
theorem recurrent_comparison (A B : Field) (D : Finset Site)
    (hB : ∀ site, laplacian B site = -1 ∨ laplacian B site = 0)
    (hrec : RecurrentField B)
    (hA : ∀ x ∈ D, laplacian A x = -1 ∨ laplacian A x = 0)
    (hbd : ∀ y x, x ∈ D → Edge y x → y ∉ D → B y ≤ A y) :
    ∀ x ∈ D, B x ≤ A x := by
  by_contra hcon
  have hex : ∃ x ∈ D, A x < B x := by
    by_contra hno
    exact hcon (fun x hx => le_of_not_gt fun h => hno ⟨x, hx, h⟩)
  obtain ⟨x, hx, hlt⟩ := hex
  set u : Site → ℤ := fun z => B z - A z with hu
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image D u ⟨x, hx⟩
  have hpos : 0 < u x0 := lt_of_lt_of_le (by simp only [hu]; omega) (hmax x hx)
  -- on the inputs of a point of `D`, `u` is at most the maximum; outside `D` it is nonpositive
  have hout : ∀ y x, x ∈ D → Edge y x → y ∉ D → u y ≤ 0 := fun y x hxD hE hyD => by
    have := hbd y x hxD hE hyD
    simp only [hu]
    omega
  have hin : ∀ y x, x ∈ D → Edge y x → u y ≤ u x0 := fun y x hxD hE => by
    by_cases hyD : y ∈ D
    · exact hmax y hyD
    · have := hout y x hxD hE hyD
      omega
  set M : Finset Site := D.filter (fun z => u z = u x0) with hM
  have hMmem : ∀ z, z ∈ M ↔ z ∈ D ∧ u z = u x0 := fun z => by
    simp only [hM, Finset.mem_filter]
  -- the maximisers form a finite incoming fort for `B`
  have hfort : IsIncomingFort B (↑M : Set Site) := by
    intro z hz
    rw [Finset.mem_coe, hMmem] at hz
    obtain ⟨hzD, hzu⟩ := hz
    have hneg := hin (incomingNeg z) z hzD (Or.inl rfl)
    have hpos' := hin (incomingPos z) z hzD (Or.inr rfl)
    have hsum : (u x0 - u (incomingNeg z)) + (u x0 - u (incomingPos z)) =
        laplacian A z - laplacian B z := by
      unfold laplacian
      simp only [hu] at hzu ⊢
      omega
    have hAz := hA z hzD
    have hBz := hB z
    -- membership of an input of `z` with zero deficit
    have memOf : ∀ y, Edge y z → u y = u x0 → y ∈ (↑M : Set Site) := by
      intro y hE hy
      rw [Finset.mem_coe, hMmem]
      refine ⟨?_, hy⟩
      by_contra hyD
      have := hout y z hzD hE hyD
      omega
    rcases hBz with hBm | hB0
    · left
      refine ⟨hBm, ?_⟩
      rcases hAz with hAm | hA0
      · -- deficits sum to zero: both inputs lie in the maximiser set
        have h1 : u (incomingNeg z) = u x0 := by omega
        exact Or.inl (memOf _ (Or.inl rfl) h1)
      · -- deficits sum to one: one input has zero deficit
        by_cases h1 : u (incomingNeg z) = u x0
        · exact Or.inl (memOf _ (Or.inl rfl) h1)
        · have h2 : u (incomingPos z) = u x0 := by omega
          exact Or.inr (memOf _ (Or.inr rfl) h2)
    · right
      have h1 : u (incomingNeg z) = u x0 := by omega
      have h2 : u (incomingPos z) = u x0 := by omega
      exact ⟨hB0, memOf _ (Or.inl rfl) h1, memOf _ (Or.inr rfl) h2⟩
  exact hrec M ⟨x0, (hMmem x0).mpr ⟨hx0, rfl⟩⟩ hfort

end FLatticePaper

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The short shift lowers the transverse-grade `t` by two (`t(σ) = −2`). -/
theorem ChildFrame.tGrade_add_shortShift (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + frame.shortShift) = frame.tGrade z - 2 := by
  have h := frame.tGrade_shortShift
  unfold ChildFrame.tGrade at h ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination h

/-- The zero strip gives `D = 0` at a site whose `t` and whose shifted `t` both lie in the strip. -/
theorem starDiff_zero_of_zero_strip (frame : ChildFrame) {F M : Field}
    (hS : frame.StripInputs M) (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV) (z : Site)
    (hlo : 3 - frame.child.den ≤ frame.tGrade z) (hhi : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    starDiff F frame.shortShift z = 0 := by
  unfold starDiff
  have h1 := frame.zero_strip hS hagree hper z (by omega) hhi
  have h2 := frame.zero_strip hS hagree hper (z + frame.shortShift)
    (by rw [frame.tGrade_add_shortShift]; omega) (by rw [frame.tGrade_add_shortShift]; omega)
  rw [h1, h2]
  ring

/-- The shifted-`t` strip input of the bottom H arc: its points have `t` in `[3 − d, n + 2d − 1]`, so that the point and its
short shift both lie in the zero strip. -/
structure BottomInputs (frame : ChildFrame) (F : Field) : Prop where
  tRange : ∀ z, PureBottom frame.closedPolygon z →
    3 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1

/-- `bottomZero` of the base inputs, from the zero strip and the `t`-range of the pure bottom arc. -/
theorem bottomZero_of_strip (frame : ChildFrame) {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (bottom : BottomInputs frame F) :
    ∀ z, PureBottom frame.closedPolygon z → starDiff F frame.shortShift z = 0 := by
  intro z hz
  obtain ⟨h1, h2⟩ := bottom.tRange z hz
  exact starDiff_zero_of_zero_strip frame hS hagree hper z h1 h2

/-- The transverse period drift of `D`: `D(z + V) = D(z) + 2`. -/
theorem ChildFrame.starDiff_add_transverse_two (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (z : Site) :
    starDiff F frame.shortShift (z + frame.child.modifiedDeck.transverse) =
      starDiff F frame.shortShift z + 2 := by
  have hgσ : ∀ z, frame.child.transverseGrade (z + frame.shortShift) =
      frame.child.transverseGrade z + frame.child.transverseGrade frame.shortShift := by
    intro z
    unfold Fraction.transverseGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hgσ2 : frame.child.transverseGrade frame.shortShift = 2 := by
    rw [frame.transverseGrade_child, frame.tGrade_shortShift]
    norm_num
  rw [starDiff_add_transverse hper.2 hgσ z, hgσ2]

/-- The inputs of `base` that the strips do not give: the top arc, the V arcs, the boundary cover and the comparison. -/
structure StripBaseInputs (frame : ChildFrame) (F : Field) : Prop where
  topTwo : ∀ z, PureTop frame.closedPolygon z → starDiff F frame.shortShift z = 2
  leftRange : ∀ z, OnVArc frame.closedPolygon z →
    starDiff F frame.shortShift z = 0 ∨ starDiff F frame.shortShift z = 1 ∨ starDiff F frame.shortShift z = 2
  boundaryCover : ∀ z, OnBoundary frame.closedPolygon z →
    PureBottom frame.closedPolygon z ∨ PureTop frame.closedPolygon z ∨ OnVArc frame.closedPolygon z
  comparison : (∀ z, OnBoundary frame.closedPolygon z →
      0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2) →
    ∀ z ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2

/-- The base inputs, with `bottomZero` from the zero strip. -/
theorem baseInputsOfStrips (frame : ChildFrame) {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (bottom : BottomInputs frame F) (rest : StripBaseInputs frame F) : BaseInputs frame F where
  bottomZero := bottomZero_of_strip frame hS hagree hper bottom
  topTwo := rest.topTwo
  leftRange := rest.leftRange
  boundaryCover := rest.boundaryCover
  comparison := rest.comparison

/-- The base range of `D` on the closed polygon, from the strips and the remaining inputs. -/
theorem base_of_strips (frame : ChildFrame) {F M : Field} (hS : frame.StripInputs M)
    (hagree : ∀ y ∈ frame.closedPolygon, F y = M y)
    (hper : HasGeneratorPeriods frame.child F 0 frame.coherentConstantV)
    (bottom : BottomInputs frame F) (rest : StripBaseInputs frame F) :
    ∀ z ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2 :=
  base_of_inputs frame (baseInputsOfStrips frame hS hagree hper bottom rest)

end FLatticePaper.Induction
