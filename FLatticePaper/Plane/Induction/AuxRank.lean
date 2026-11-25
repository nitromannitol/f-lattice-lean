import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.BlackPermit
import FLatticePaper.Plane.Induction.ReflectionI

/-! hslip: the auxiliary graph, and the permits of the forced edges (the lead's (b) and (c)).

* (b) Sign −1 by reflection. If `F (I − z) = F z`, then the sign −1 raw slip at `c` against `F(· − σ)` equals the sign +1 raw slip at
  `I − c` against `F(· + σ)`, with the reflected inputs. So a sign −1 permit is a sign +1 permit at the reflected pair
  (`slipPermits_reflect_neg`), and the input relation is reflected (`edge_reflectI`).

* (c) The auxiliary graph (sign +1): blacks keep both inputs; a free white keeps its prescribed input (`FreePresc`); a nonfree white keeps any
  input that is permitted. At each white one input is permitted (`white_permitted_input`, from the slip sum and the unit slip), so the
  auxiliary graph has an input at every white.

* A strict rank `R` on the auxiliary graph gives every square clause for any selection inside the graph (`squares_gen`), so `forced_sound`
  makes every W1-forced literal at a nonfree white equal to that selection. Hence the forced input is a permitted input (`forced_permitted`):
  the forced permit is a corollary of the rank, not a separate fact. -/

namespace FLatticePaper.AuxRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.FreePolicy FLatticePaper.FreeClosure
  FLatticePaper.AndOrRank

/-! ### (b) The sign −1 by reflection -/

/-- The sign −1 increment against `F(· − σ)` is the sign +1 increment at the reflected pair. -/
theorem slipIncrement_reflect_neg {F : Field} (hI : ∀ z, F (reflectionI - z) = F z) (σ c i : Site) :
    slipIncrement F (fun z => F (z + -σ)) c i =
      slipIncrement F (fun z => F (z + σ)) (reflectionI - c) (reflectionI - i) := by
  unfold slipIncrement
  have key : ∀ x : Site, F (reflectionI - x + σ) = F (x + -σ) := fun x => by
    rw [show reflectionI - x + σ = reflectionI - (x + -σ) by abel]
    exact hI _
  simp only
  rw [key i, key c, hI i, hI c]

/-- A sign −1 permit is a sign +1 permit at the reflected pair. -/
theorem slipPermits_reflect_neg {F : Field} (hI : ∀ z, F (reflectionI - z) = F z) (σ c i : Site) :
    slipPermits F (fun z => F (z + -σ)) c i ↔ slipPermits F (fun z => F (z + σ)) (reflectionI - c) (reflectionI - i) := by
  unfold slipPermits
  rw [slipIncrement_reflect_neg hI]

theorem edge_reflect_iff {i c : Site} : Edge i c ↔ Edge (reflectionI - i) (reflectionI - c) := by
  constructor
  · exact edge_reflectI
  · intro h
    have h' := edge_reflectI h
    rwa [sub_sub_cancel, sub_sub_cancel] at h'

/-! ### The squares from a strict rank on a retained relation -/

/-- **Squares from a strict rank.** For a retained relation `P` that keeps both inputs at blacks and the selection at whites, a strict rank
on `P` excludes every square whose corners all keep an input in the square. -/
theorem squares_gen (F : Field) (P : Site → Site → Prop) (sel : Site → Site) (R : Site → ℤ)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → P c i)
    (hsel : ∀ c, laplacian F c = 0 → P c (sel c))
    (hstrict : ∀ c i, P c i → R i < R c) :
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
    · have h1 := hstrict c0 (incomingNeg c0) (hblack c0 (incomingNeg c0) hb (Or.inl rfl))
      have h2 := hmin _ hk
      linarith
    · have h1 := hstrict c0 (incomingPos c0) (hblack c0 (incomingPos c0) hb (Or.inr rfl))
      have h2 := hmin _ hk
      linarith
  · rw [if_neg hb] at hk
    have hl : laplacian F c0 = 0 := (hbin c0).resolve_left hb
    have h1 := hstrict c0 _ (hsel c0 hl)
    have h2 := hmin _ hk
    linarith

/-! ### (c) The white permit and the auxiliary graph (sign +1) -/

/-- **One permitted input at a white.** The two increments of a white centre sum to `−laplacian F (c + σ) ∈ {0, 1}` with unit
increments, so one input has increment `≤ 0`. -/
theorem white_permitted_input {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ))) {c : Site} (hc : laplacian F c = 0) :
    ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ slipPermits F (fun z => F (z + σ)) c i := by
  have hsum := slip_sum_eq F σ c hσ
  have hU1 := hU c (incomingNeg c) (Or.inl rfl)
  have hU2 := hU c (incomingPos c) (Or.inr rfl)
  have hb2 := hbin (c + σ)
  rw [hc] at hsum
  have h : slipIncrement F (fun z => F (z + σ)) c (incomingNeg c) ≤ 0 ∨
      slipIncrement F (fun z => F (z + σ)) c (incomingPos c) ≤ 0 := by
    omega
  rcases h with h | h
  · exact ⟨incomingNeg c, Or.inl rfl, h⟩
  · exact ⟨incomingPos c, Or.inr rfl, h⟩

/-- **The white permit for sign −1, by reflection.** -/
theorem white_permitted_input_neg {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ))) (hI : ∀ z, F (reflectionI - z) = F z) {c : Site}
    (hc : laplacian F c = 0) :
    ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ slipPermits F (fun z => F (z + -σ)) c i := by
  have hcI : laplacian F (reflectionI - c) = 0 := by
    rw [laplacian_reflectI hI c]
    exact hc
  obtain ⟨j, hj, hp⟩ := white_permitted_input hσ hbin hU hcI
  refine ⟨reflectionI - j, ?_, ?_⟩
  · have h2 := edge_reflect_iff.mp (show Edge j (reflectionI - c) from hj)
    rw [sub_sub_cancel] at h2
    exact h2
  · refine (slipPermits_reflect_neg hI σ c (reflectionI - j)).mpr ?_
    rw [sub_sub_cancel]
    exact hp

/-! ### (c) The auxiliary graph (sign +1) and the forced permits -/

/-- The auxiliary graph: blacks keep both inputs; a white in the closure keeps its prescribed input; another white keeps a permitted input. -/
def auxRetained (frame : ChildFrame) (F : Field) (c i : Site) : Prop :=
  (laplacian F c = -1 ∧ Edge i c) ∨
    (laplacian F c = 0 ∧ ((freeClosure frame c ∧ FreePresc frame 1 c i) ∨
      (¬ freeClosure frame c ∧ Edge i c ∧ slipPermits F (fun z => F (z + frame.shortShift)) c i)))

theorem auxRetained_edge {frame : ChildFrame} {F : Field} {c i : Site} (h : auxRetained frame F c i) : Edge i c := by
  unfold auxRetained at h
  rcases h with ⟨-, he⟩ | ⟨-, ⟨hcl, hp⟩ | ⟨-, he, -⟩⟩
  · exact he
  · exact freePresc_input frame 1 (Or.inl rfl) hp
  · exact he

/-- Every white has an input in the auxiliary graph: the prescribed input in the closure, a permitted input otherwise. -/
theorem auxRetained_exists (frame : ChildFrame) {F : Field} (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift))) {c : Site} (hc : laplacian F c = 0) :
    ∃ i, auxRetained frame F c i := by
  by_cases hcl : freeClosure frame c
  · obtain ⟨i, hi⟩ := freePresc_exists frame 1 hcl
    exact ⟨i, Or.inr ⟨hc, Or.inl ⟨hcl, hi⟩⟩⟩
  · obtain ⟨i, hi, hp⟩ := white_permitted_input hσ hbin hU hc
    exact ⟨i, Or.inr ⟨hc, Or.inr ⟨hcl, hi, hp⟩⟩⟩

/-- **The forced permits.** With a strict rank `R` on the auxiliary graph, the W1-forced input at a nonfree white is permitted: every
selection inside the graph satisfies the squares, so `forced_sound` makes the forced literal equal to it. -/
theorem forced_permitted (frame : ChildFrame) {F : Field} (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift)))
    {R : Site → ℤ} (hstrict : ∀ c i, auxRetained frame F c i → R i < R c)
    {c o : Site} (hnc : ¬ freeClosure frame c) (hl : laplacian F c = 0)
    (hf : ForcedEdge F (fun _ _ => False) c o) :
    slipPermits F (fun z => F (z + frame.shortShift)) c o := by
  let sel : Site → Site := fun c => Classical.epsilon (auxRetained frame F c)
  have hsel : ∀ c, laplacian F c = 0 → auxRetained frame F c (sel c) := fun c hc =>
    Classical.epsilon_spec (auxRetained_exists frame hσ hbin hU hc)
  have hblack : ∀ c i, laplacian F c = -1 → (i = incomingNeg c ∨ i = incomingPos c) → auxRetained frame F c i :=
    fun c i hc hi => Or.inl ⟨hc, hi⟩
  have hsq := squares_gen F (auxRetained frame F) sel R hbin hblack hsel hstrict
  have hsi : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c := fun c hc =>
    auxRetained_edge (hsel c hc)
  have hfs := forced_sound F (fun _ _ => False) sel hsi (fun _ _ h => False.elim h) hsq c o hf
  have ho : auxRetained frame F c o := by
    rw [← hfs]
    exact hsel c hl
  unfold auxRetained at ho
  rcases ho with ⟨hb, -⟩ | ⟨-, ⟨hcl, -⟩ | ⟨-, -, hp⟩⟩
  · exact absurd (hl.symm.trans hb) (by norm_num)
  · exact absurd hcl hnc
  · exact hp

/-! ### (a) The black permits, both signs -/

/-- **The black permit, sign +1.** Black even by `black_even_permit`; black odd by the odd-black premise `OddBlackNoRise`. -/
theorem black_permit_plus {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ)))
    (hS2 : NoEvenSlipSaddle F (fun z => F (z + σ)))
    (hOdd : OddBlackNoRise F σ) {c i : Site} (hc : laplacian F c = -1)
    (hi : i = incomingNeg c ∨ i = incomingPos c) :
    slipPermits F (fun z => F (z + σ)) c i := by
  by_cases hpar : (F c - F (c + σ)) % 2 = 1
  · exact hOdd c hc hpar i hi
  · exact black_even_permit hσ hbin hU hS2 hc (by omega) hi

/-- **The black permit, sign −1, by reflection:** a black input of sign −1 is a black input of sign +1 at the reflected centre. -/
theorem black_permit_neg {F : Field} {σ : Site} (hσ : EvenSite σ)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + σ)))
    (hS2 : NoEvenSlipSaddle F (fun z => F (z + σ)))
    (hOdd : OddBlackNoRise F σ) (hI : ∀ z, F (reflectionI - z) = F z) {c i : Site}
    (hc : laplacian F c = -1) (hi : Edge i c) :
    slipPermits F (fun z => F (z + -σ)) c i := by
  have hcI : laplacian F (reflectionI - c) = -1 := by
    rw [laplacian_reflectI hI c]
    exact hc
  have hiI : Edge (reflectionI - i) (reflectionI - c) := edge_reflectI hi
  have hP := black_permit_plus hσ hbin hU hS2 hOdd hcI hiI
  exact (slipPermits_reflect_neg hI σ c i).mpr hP

/-! ### hslip for the sign +1 policy -/

/-- **The permit of the sign +1 policy.** Blacks: `black_permit_plus` (the odd-black premise `hOdd`). Forced nonfree whites: `forced_permitted`
(the aux rank `hstrict`). Free whites: the named premise `hfree` (the prescribed free edges). -/
theorem policy_permit_plus (frame : ChildFrame) {F : Field} (hσ : EvenSite frame.shortShift)
    (hbin : ∀ z, laplacian F z = -1 ∨ laplacian F z = 0)
    (hU : HasUnitSlip F (fun z => F (z + frame.shortShift)))
    (hS2 : NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)))
    (hOdd : OddBlackNoRise F frame.shortShift)
    (hex : ForcedExists frame F)
    {R : Site → ℤ} (hstrict : ∀ c i, auxRetained frame F c i → R i < R c)
    (hfree : ∀ c i, laplacian F c = 0 → freeClosure frame c → FreePresc frame 1 c i →
      slipPermits F (fun z => F (z + frame.shortShift)) c i) :
    ∀ c i, freePolicy frame F 1 c i → slipPermits F (fun z => F (z + frame.shortShift)) c i := by
  intro c i h
  unfold freePolicy at h
  rcases h with ⟨hl, hE⟩ | ⟨hl, ⟨hcl, hp⟩ | ⟨hn, hs⟩⟩
  · exact black_permit_plus hσ hbin hU hS2 hOdd hl hE
  · exact hfree c i hl hcl hp
  · obtain ⟨o, ho⟩ := hex c hn hl
    rw [hs]
    exact forced_permitted frame hσ hbin hU hstrict hn hl (forcedSel_spec ⟨o, ho⟩)

end FLatticePaper.AuxRank
