import FLatticePaper.Plane.Induction.AndOrRank

/-! Task 44: the square clauses and unit propagation (fixes/Q1.md paragraphs 4 and 8; W1_CONSTRUCTOR).

Archive wording, kept verbatim in the definitions below:
* "Even sites take horizontal inputs, odd sites vertical. White means physical Δ=0, black means −1."
* "the clause of a unit square forbids the configuration where every corner's selected/kept inputs stay in the square."
* "A 'private square' on a white root's rejected input has the other three edges directed back to the root."

A black corner keeps both of its inputs; a white corner keeps its selected input. Unit propagation forces a white corner's
selection outside a unit square once its other three corners have their selections forced inside it. -/

namespace FLatticePaper.SquareClauses

open FLatticePaper FLatticePaper.AndOrRank

/-- A corner's selected or kept inputs stay in the square `S`: a black corner keeps both inputs, a white corner keeps its selection. -/
def keptInside (F : Field) (sel : Site → Site) (S : Finset Site) (c : Site) : Prop :=
  if laplacian F c = -1 then incomingNeg c ∈ S ∧ incomingPos c ∈ S else sel c ∈ S

/-- The square clause of the unit square `squareCorners a b` is satisfied by the selection `sel` when the configuration in which
every corner's selected or kept inputs stay in the square does not occur. -/
def SquareClauseSat (F : Field) (sel : Site → Site) (a b : ℤ) : Prop :=
  ¬ ∀ c ∈ squareCorners a b, keptInside F sel (squareCorners a b) c

/-- Unit propagation of the forced whites from a seed set `seed` (empty for the unseeded game). A white corner `c` of a unit square
has its selection forced outside the square, `o`, when each of its other corners is white and has its selection forced inside the
square, through the input `inside c'` of that corner. -/
inductive ForcedEdge (F : Field) (seed : Site → Site → Prop) : Site → Site → Prop
  | seed {c i : Site} : seed c i → ForcedEdge F seed c i
  | unit {a b : ℤ} {c o : Site} (inside : Site → Site) (hc : c ∈ squareCorners a b) (hw : laplacian F c = 0)
      (ho : o = incomingNeg c ∨ o = incomingPos c) (hout : o ∉ squareCorners a b)
      (hin : ∀ c' ∈ squareCorners a b, c' ≠ c →
        inside c' ∈ squareCorners a b ∧ (inside c' = incomingNeg c' ∨ inside c' = incomingPos c') ∧
          laplacian F c' = 0)
      (hforced : ∀ c' ∈ squareCorners a b, c' ≠ c → ForcedEdge F seed c' (inside c')) :
      ForcedEdge F seed c o

/-- **Soundness of unit propagation.** Every selection that is a white input selection and satisfies all square clauses, and
that agrees with the seeds, selects every forced edge. -/
theorem forced_sound (F : Field) (seed : Site → Site → Prop) (sel : Site → Site)
    (hsel : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hseed : ∀ c i, seed c i → sel c = i) (hsq : ∀ a b, SquareClauseSat F sel a b) :
    ∀ c i, ForcedEdge F seed c i → sel c = i := by
  intro c i h
  induction h with
  | seed hs => exact hseed _ _ hs
  | @unit a b c o inside hc hw ho hout hin hforced ih =>
    have hwhite : ∀ c', c' ∈ squareCorners a b → c' ≠ c → sel c' ∈ squareCorners a b := by
      intro c' hc' hne
      rw [ih c' hc' hne]
      exact (hin c' hc' hne).1
    have hkc : ¬ keptInside F sel (squareCorners a b) c := by
      intro hk
      apply hsq a b
      intro c'' hc''
      by_cases hcc : c'' = c
      · rw [hcc]
        exact hk
      · have hw'' := (hin c'' hc'' hcc).2.2
        unfold keptInside
        rw [if_neg (by rw [hw'']; norm_num)]
        exact hwhite c'' hc'' hcc
    have hcS : sel c ∉ squareCorners a b := by
      unfold keptInside at hkc
      rw [if_neg (by rw [hw]; norm_num)] at hkc
      exact hkc
    obtain ⟨t, ht, htin⟩ := square_corner_input a b hc
    have hto : t ≠ o := fun h => hout (h ▸ ht)
    have hsc := hsel c hw
    have hsc_t : sel c ≠ t := fun h => hcS (h ▸ ht)
    rcases hsc with h1 | h1 <;> rcases htin with h2 | h2 <;> rcases ho with h3 | h3 <;>
      first
      | exact h1.trans h3.symm
      | exact absurd (h1.trans h2.symm) hsc_t
      | exact absurd (h2.trans h3.symm) hto

/-- **Unseeded propagation forces nothing.** From the square clauses alone (no seeds) unit propagation derives no forced edge:
each step needs three forced corners, and a finite derivation has a first step, which needs one. The forced whites therefore
come from seeds. -/
theorem forced_unseeded_empty (F : Field) (c i : Site) : ¬ ForcedEdge F (fun _ _ => False) c i := by
  intro h
  induction h with
  | seed hs => exact hs
  | @unit a b c o inside hc hw ho hout hin hforced ih =>
    obtain ⟨c', hc', hne⟩ : ∃ c' ∈ squareCorners a b, c' ≠ c := by
      by_cases h0 : c = (a, b)
      · exact ⟨(a + 1, b), by simp [squareCorners], fun h => by rw [h0] at h; simp at h⟩
      · exact ⟨(a, b), by simp [squareCorners], fun h => h0 h.symm⟩
    exact ih c' hc' hne

/-- **Square clauses from a strict rank.** Let `R` be strict on the black inputs, and let `sel` choose at each white a permitted-
or-not input `sel c` with `R (sel c) + 1 ≤ R c`. Then `sel` satisfies every unit square clause: the minimum corner of the square is
white (a black minimum has both inputs with smaller rank, so one of them is in the square, a contradiction), and its selection
`sel c` leaves the square (a selection inside would have rank at least `R c`). -/
theorem squareClauses_of_strict {F : Field} {R : Field} {sel : Site → Site}
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i + 1 ≤ R c)
    (hsel : ∀ c, laplacian F c = 0 → (sel c = incomingNeg c ∨ sel c = incomingPos c) ∧ R (sel c) + 1 ≤ R c)
    (a b : ℤ) : SquareClauseSat F sel a b := by
  intro hall
  obtain ⟨c, hcS, hmin⟩ := (squareCorners a b).exists_min_image R ⟨(a, b), by simp [squareCorners]⟩
  have hk := hall c hcS
  unfold keptInside at hk
  rcases hbin c with hb | hw
  · rw [if_pos hb] at hk
    obtain ⟨hn, hp⟩ := hk
    have h1 := hblack c hb (incomingNeg c) (Or.inl rfl)
    have h2 := hmin _ hn
    linarith
  · rw [if_neg (by rw [hw]; norm_num)] at hk
    have h1 := (hsel c hw).2
    have h2 := hmin _ hk
    linarith

/-- **Unit propagation is sound on a strict selection.** If `sel` is a strictly decreasing selection (`squareClauses_of_strict`) and
agrees with the seeds, then every W1-forced white selects its forced edge. -/
theorem forced_selected_of_strict {F : Field} {R : Field} {sel : Site → Site} (seed : Site → Site → Prop)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i + 1 ≤ R c)
    (hsel : ∀ c, laplacian F c = 0 → (sel c = incomingNeg c ∨ sel c = incomingPos c) ∧ R (sel c) + 1 ≤ R c)
    (hseed : ∀ c i, seed c i → sel c = i) :
    ∀ c i, ForcedEdge F seed c i → sel c = i :=
  forced_sound F seed sel (fun c hw => (hsel c hw).1)
    hseed (fun a b => squareClauses_of_strict hbin hblack hsel a b)

end FLatticePaper.SquareClauses
