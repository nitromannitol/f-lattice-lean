import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.RankFromForts
import FLatticePaper.Plane.Induction.TwosEquiv
import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.Plane.Induction.WeightChange
import FLatticePaper.Plane.Induction.AuxRank

/-! The auxiliary game of Q1 for a sign `η`, `permitsQ1`: black sites keep both inputs; a free white keeps its prescribed input
(`FreePresc`); a nonfree white allows both inputs. (The slip permit of the selected input is proved separately, Q1's last paragraph.)

Proved here: `permitsQ1_permitLocal` (the local hypothesis of the Bellman rank: blacks both, whites one) and
`permitsQ1_shift` (the deck invariance `permits (c + s) (i + s) ↔ permits c i` for every span element `s`). -/

namespace FLatticePaper.AuxRankQ1

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePolicy FLatticePaper.FreeClosure
open FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.AuxRank

/-- The auxiliary game of Q1 for the sign `η`. -/
def permitsQ1 (frame : ChildFrame) (F : Field) (η : ℤ) (c i : Site) : Prop :=
  (laplacian F c = -1 ∧ Edge i c) ∨
    (laplacian F c = 0 ∧ ((freeClosure frame c ∧ FreePresc frame η c i) ∨ (¬ freeClosure frame c ∧ Edge i c)))

/-- **The local hypothesis** of the Bellman rank: a black site keeps both inputs, a white site at least one. -/
theorem permitsQ1_permitLocal (frame : ChildFrame) (F : Field) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    PermitLocal F (permitsQ1 frame F η) := by
  refine ⟨fun c hb => ⟨Or.inl ⟨hb, Or.inl rfl⟩, Or.inl ⟨hb, Or.inr rfl⟩⟩, fun c hw => ?_⟩
  by_cases hcl : freeClosure frame c
  · obtain ⟨i, hi⟩ := freePresc_exists frame η hcl
    have he := freePresc_input frame η hη hi
    have hp : permitsQ1 frame F η c i := Or.inr ⟨hw, Or.inl ⟨hcl, hi⟩⟩
    unfold Edge at he
    rcases he with h | h
    · subst h
      exact Or.inl hp
    · subst h
      exact Or.inr hp
  · exact Or.inl (Or.inr ⟨hw, Or.inr ⟨hcl, Or.inl rfl⟩⟩)

/-- An even shift preserves the edge relation. -/
theorem edge_shift {s : Site} (hs : EvenSite s) (c i : Site) : Edge (i + s) (c + s) ↔ Edge i c := by
  unfold Edge
  rw [FLatticePaper.TwosEquiv.incomingNeg_add_even hs, FLatticePaper.TwosEquiv.incomingPos_add_even hs]
  constructor
  · rintro (h | h)
    · exact Or.inl (FLatticePaper.TwosEquiv.site_add_right_cancel' h)
    · exact Or.inr (FLatticePaper.TwosEquiv.site_add_right_cancel' h)
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

/-- **The deck invariance of `permitsQ1`**: for every span element `s`, `permitsQ1 (c + s) (i + s) ↔ permitsQ1 c i`,
given the Laplacian invariance of the field under the deck. -/
theorem permitsQ1_shift (frame : ChildFrame) (F : Field) (η : ℤ)
    (hL : ∀ (c : Site) (i j : ℤ), laplacian F (c + frame.child.modifiedDeck.combine i j) = laplacian F c)
    (step : Site) (hstep : step ∈ frame.child.modifiedDeck.span) (site input : Site) :
    permitsQ1 frame F η (site + step) (input + step) ↔ permitsQ1 frame F η site input := by
  obtain ⟨i, j, rfl⟩ := hstep
  have hsp : frame.child.modifiedDeck.combine i j ∈ frame.child.modifiedDeck.span := ⟨i, j, rfl⟩
  have hs : EvenSite (frame.child.modifiedDeck.combine i j) := span_even frame hsp
  unfold permitsQ1
  simp only [hL, freeClosure_add_span frame hsp, freePresc_add_span frame η hsp, edge_shift hs]

/-! ### The grade `K = P + J` and the burning rank of the Q1 game -/

/-- The price drifts by `−i` and the rounded slip by `η j` along the deck vector `combine i j`. -/
theorem grade_drift_combine (frame : ChildFrame) (F : Field) (η : ℤ)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (i j : ℤ) (z : Site) :
    frame.price F (z + frame.child.modifiedDeck.combine i j) = frame.price F z + i * -1 + j * 0 ∧
      frame.roundedSlip F η (z + frame.child.modifiedDeck.combine i j) = frame.roundedSlip F η z + η * j := by
  have hP := FLatticePaper.WeightChange.affine_lattice (F := frame.price F) (U := frame.child.modifiedDeck.kernel)
    (V := frame.child.modifiedDeck.transverse) (p := -1) (q := 0) (fun z => (hPD z).1) (fun z => (hPD z).2) z i j
  have hS := FLatticePaper.WeightChange.affine_lattice (F := frame.slip F η) (U := frame.child.modifiedDeck.kernel)
    (V := frame.child.modifiedDeck.transverse) (p := 0) (q := 2 * η) (fun z => (hSD z).1) (fun z => (hSD z).2) z i j
  refine ⟨hP, ?_⟩
  unfold ChildFrame.roundedSlip
  have e : frame.child.modifiedDeck.combine i j = FLatticePaper.WeightChange.latPt frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse i j := rfl
  rw [e]
  rw [hS]
  have e3 : frame.slip F η z + i * 0 + j * (2 * η) + 1 = (frame.slip F η z + 1) + 2 * (η * j) := by ring
  rw [e3]
  generalize η * j = k
  generalize frame.slip F η z = x
  omega

/-- The grade `K = P + J` drifts by an integer along the span. -/
theorem grade_hgrade (frame : ChildFrame) (F : Field) (η : ℤ)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η) :
    ∀ step ∈ frame.child.modifiedDeck.span, ∃ increment : ℤ, ∀ site,
      (fun z => frame.price F z + frame.roundedSlip F η z) (site + step) =
        (fun z => frame.price F z + frame.roundedSlip F η z) site + increment := by
  intro step hstep
  obtain ⟨i, j, rfl⟩ := hstep
  refine ⟨i * -1 + η * j, fun site => ?_⟩
  obtain ⟨h1, h2⟩ := grade_drift_combine frame F η hPD hSD i j site
  simp only [h1, h2]
  ring

/-- **The Q1 burning rank**: the restricted no-fort premise for the Q1 game with the grade `K = P + J` gives an integer rank
`R` with `IsConstrainedBurningRank` for `permitsQ1`. The one named premise is `hno`. -/
theorem permitsQ1_rank (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (hno : RestrictedNoFort F (fun z => frame.price F z + frame.roundedSlip F η z) (permitsQ1 frame F η)) :
    ∃ R : Site → ℤ, IsConstrainedBurningRank F R (permitsQ1 frame F η) := by
  have hpos : 0 < frame.child.modifiedDeck.det := by
    obtain ⟨hn1, hnd, -, -, -⟩ := frame.child_facts
    have e : frame.child.modifiedDeck.det = frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num
        - frame.child.num * frame.child.num := by
      unfold PeriodDeck.det
      rw [frame.child_modifiedDeck_kernel, frame.child_modifiedDeck_transverse]
      simp only
      ring
    rw [e]
    nlinarith
  obtain ⟨scale, remainder, budget, -, -, -, hR⟩ :=
    FLatticePaper.exists_constrainedBurningRank_of_restrictedNoFort (deck := frame.child.modifiedDeck)
      (sites := frame.child.modifiedDeck.residueSquare)
      ((PeriodDeck.covers_iff_square_codes_subset frame.child.modifiedDeck hpos _).mpr (subset_refl _))
      (fun step hstep => span_even frame hstep)
      (fun step hstep site => by
        obtain ⟨i, j, rfl⟩ := hstep
        exact frame.laplacian_add_lattice hP i j site)
      (grade_hgrade frame F η hPD hSD)
      (fun step hstep site input => permitsQ1_shift frame F η
        (fun c i j => frame.laplacian_add_lattice hP i j c) step hstep site input)
      (permitsQ1_permitLocal frame F hη) hP.binary hno
  exact ⟨fun site => scale * (frame.price F site + frame.roundedSlip F η site) + remainder site, hR⟩

/-! ### The square clauses from the burning rank -/

/-- **`squares_gen`, selected-edge form**: strictness is needed at the black corners (both inputs) and at the selected input
of each white corner only. -/
theorem squares_gen_sel (F : Field) (sel : Site → Site) (R : Site → ℤ)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hbk : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → R i < R c)
    (hwh : ∀ c, laplacian F c = 0 → R (sel c) < R c) :
    ∀ a b : ℤ, SquareClauseSat F sel a b := by
  intro a b
  unfold SquareClauseSat
  intro hall
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image (squareCorners a b) R ⟨(a, b), by simp [squareCorners]⟩
  have hk := hall c0 hc0
  unfold keptInside at hk
  by_cases hb : laplacian F c0 = -1
  · rw [if_pos hb] at hk
    rcases hk with hk | hk
    · have h1 := hbk c0 (incomingNeg c0) hb (Or.inl rfl)
      have h2 := hmin _ hk
      linarith
    · have h1 := hbk c0 (incomingPos c0) hb (Or.inr rfl)
      have h2 := hmin _ hk
      linarith
  · rw [if_neg hb] at hk
    have hl : laplacian F c0 = 0 := (hbin c0).resolve_left hb
    have h1 := hwh c0 hl
    have h2 := hmin _ hk
    linarith

/-- **A satisfying selection from the burning rank**: at a white the selected input is the lower one (the one with `permits` and a
decrease, the negative one when both), at a black both inputs decrease. Hence `HasSatSelection` for the field. -/
theorem hasSat_of_constrained {F : Field} {R : Site → ℤ} {P : Site → Site → Prop}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0) (hcon : IsConstrainedBurningRank F R P) :
    HasSatSelection F := by
  classical
  have hcases : ∀ c, (laplacian F c = -1 ∧ (P c (incomingNeg c) ∧ R (incomingNeg c) < R c) ∧
      (P c (incomingPos c) ∧ R (incomingPos c) < R c)) ∨
      (laplacian F c = 0 ∧ ((P c (incomingNeg c) ∧ R (incomingNeg c) < R c) ∨
        (P c (incomingPos c) ∧ R (incomingPos c) < R c))) := fun c => hcon c
  let sel : Site → Site := fun c =>
    if P c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c
  have hsel_in : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c := by
    intro c _
    show (if P c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c) = incomingNeg c ∨
      (if P c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c) = incomingPos c
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hwh : ∀ c, laplacian F c = 0 → R (sel c) < R c := by
    intro c hc
    rcases hcases c with ⟨hb, -⟩ | ⟨-, hn | hp⟩
    · exact absurd (hb.symm.trans hc) (by norm_num)
    · show R (if P c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c) < R c
      rw [if_pos hn]
      exact hn.2
    · show R (if P c (incomingNeg c) ∧ R (incomingNeg c) < R c then incomingNeg c else incomingPos c) < R c
      split_ifs with h
      · exact h.2
      · exact hp.2
  have hbk : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → R i < R c := by
    intro c i hb hi
    rcases hcases c with ⟨-, hn, hp⟩ | ⟨hw, -⟩
    · rcases hi with rfl | rfl
      · exact hn.2
      · exact hp.2
    · exact absurd (hb.symm.trans hw) (by norm_num)
  exact ⟨sel, hsel_in, squares_gen_sel F sel R hbin hbk hwh⟩

/-- **`HasSatSelection` from the Q1 rank**: the satisfying selection of the field comes from the burning rank on `permitsQ1`,
with the restricted no-fort premise `hno` the one named input. -/
theorem hasSat_permitsQ1 (frame : ChildFrame) (F : Field) (hP : frame.Packet F) (η : ℤ) (hη : η = 1 ∨ η = -1)
    (hPD : ∀ z, frame.price F (z + frame.child.modifiedDeck.kernel) = frame.price F z + -1 ∧
      frame.price F (z + frame.child.modifiedDeck.transverse) = frame.price F z + 0)
    (hSD : ∀ z, frame.slip F η (z + frame.child.modifiedDeck.kernel) = frame.slip F η z + 0 ∧
      frame.slip F η (z + frame.child.modifiedDeck.transverse) = frame.slip F η z + 2 * η)
    (hno : RestrictedNoFort F (fun z => frame.price F z + frame.roundedSlip F η z) (permitsQ1 frame F η)) :
    HasSatSelection F := by
  obtain ⟨R, hR⟩ := permitsQ1_rank frame F hP η hη hPD hSD hno
  exact hasSat_of_constrained hP.binary hR

end FLatticePaper.AuxRankQ1
