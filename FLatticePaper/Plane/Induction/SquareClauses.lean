import FLatticePaper.Plane.Induction.AndOrRank

/-! Task 44: the square clauses and unit propagation (fixes/Q1.md paragraphs 4 and 8; W1_CONSTRUCTOR).

Archive wording, kept verbatim in the definitions below:
* "Even sites take horizontal inputs, odd sites vertical. White means physical Δ=0, black means −1."
* "A fort contains at least one input at each of its black sites" (Q1 paragraph 1), and "its minimum-rank corner cannot be black:
  one of its two inputs is in the square" (Q1 paragraph 8).
* "the clause of a unit square forbids the configuration where every corner's selected/kept inputs stay in the square."
* "A 'private square' on a white root's rejected input has the other three edges directed back to the root."

A black corner keeps at least one of its inputs in the square; a white corner keeps its selected input. A white corner is forced
to its input outside a unit square when each other corner is black, or white and forced to its input inside the square. -/

namespace FLatticePaper.SquareClauses

open FLatticePaper FLatticePaper.AndOrRank

/-- A corner's selected or kept inputs stay in the square `S`: a black corner keeps at least one input in the square
(`incomingNeg c ∈ S ∨ incomingPos c ∈ S`), a white corner keeps its selected input. -/
def keptInside (F : Field) (sel : Site → Site) (S : Finset Site) (c : Site) : Prop :=
  if laplacian F c = -1 then incomingNeg c ∈ S ∨ incomingPos c ∈ S else sel c ∈ S

/-- The square clause of the unit square `squareCorners a b` is satisfied by the selection `sel` when the configuration in which
every corner's selected or kept inputs stay in the square does not occur. -/
def SquareClauseSat (F : Field) (sel : Site → Site) (a b : ℤ) : Prop :=
  ¬ ∀ c ∈ squareCorners a b, keptInside F sel (squareCorners a b) c

/-- A black corner of a unit square keeps an input in the square (`square_corner_input`). -/
theorem keptInside_of_black {F : Field} {sel : Site → Site} {a b : ℤ} {c : Site} (hc : c ∈ squareCorners a b)
    (hb : laplacian F c = -1) : keptInside F sel (squareCorners a b) c := by
  obtain ⟨i, hi, h⟩ := square_corner_input a b hc
  unfold keptInside
  rw [if_pos hb]
  rcases h with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

/-- Unit propagation of the forced whites from a seed set `seed` (possibly empty). A white corner `c` of a unit square has its
selection forced to the input `o` outside the square when each other corner of the square is black, or white and forced to its
input `inside c'` inside the square. -/
inductive ForcedEdge (F : Field) (seed : Site → Site → Prop) : Site → Site → Prop
  | seed {c i : Site} : seed c i → ForcedEdge F seed c i
  | unit {a b : ℤ} {c o : Site} (inside : Site → Site) (hc : c ∈ squareCorners a b) (hw : laplacian F c = 0)
      (ho : o = incomingNeg c ∨ o = incomingPos c) (hout : o ∉ squareCorners a b)
      (hin : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1 ∨
        (laplacian F c' = 0 ∧ inside c' ∈ squareCorners a b ∧
          (inside c' = incomingNeg c' ∨ inside c' = incomingPos c')))
      (hforced : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = 0 → ForcedEdge F seed c' (inside c')) :
      ForcedEdge F seed c o

/-- **Soundness of unit propagation.** Every selection that is a white input selection, satisfies all square clauses and agrees
with the seeds, selects every forced edge. -/
theorem forced_sound (F : Field) (seed : Site → Site → Prop) (sel : Site → Site)
    (hsel : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c)
    (hseed : ∀ c i, seed c i → sel c = i) (hsq : ∀ a b, SquareClauseSat F sel a b) :
    ∀ c i, ForcedEdge F seed c i → sel c = i := by
  intro c i h
  induction h with
  | seed hs => exact hseed _ _ hs
  | @unit a b c o inside hc hw ho hout hin hforced ih =>
    have hkeptOther : ∀ c', c' ∈ squareCorners a b → c' ≠ c → keptInside F sel (squareCorners a b) c' := by
      intro c' hc' hne
      rcases hin c' hc' hne with hb | ⟨hw', hmem, _⟩
      · exact keptInside_of_black hc' hb
      · unfold keptInside
        rw [if_neg (by rw [hw']; norm_num), ih c' hc' hne hw']
        exact hmem
    have hkc : ¬ keptInside F sel (squareCorners a b) c := by
      intro hk
      apply hsq a b
      intro c'' hc''
      by_cases hcc : c'' = c
      · rw [hcc]
        exact hk
      · exact hkeptOther c'' hc'' hcc
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

/-- **Square clauses from a strict rank.** Let `R` be strict on the black inputs, and let `sel` choose at each white a selection with
`R (sel c) + 1 ≤ R c`. Then `sel` satisfies every unit square clause. The minimum corner `c` of the square cannot be black: a black
corner keeps an input in the square, whose rank is at least `R c` by minimality, while strictness gives it rank below `R c`.
So `c` is white, and its selection, with rank below `R c`, leaves the square. -/
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
    rcases hk with hn | hp
    · have h1 := hblack c hb (incomingNeg c) (Or.inl rfl)
      have h2 := hmin _ hn
      linarith
    · have h1 := hblack c hb (incomingPos c) (Or.inr rfl)
      have h2 := hmin _ hp
      linarith
  · rw [if_neg (by rw [hw]; norm_num)] at hk
    have h1 := (hsel c hw).2
    have h2 := hmin _ hk
    linarith

/-- **Unit propagation is sound on a strict selection.** A strictly decreasing selection (`squareClauses_of_strict`) that agrees with
the seeds selects every W1-forced edge. -/
theorem forced_selected_of_strict {F : Field} {R : Field} {sel : Site → Site} (seed : Site → Site → Prop)
    (hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0)
    (hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i + 1 ≤ R c)
    (hsel : ∀ c, laplacian F c = 0 → (sel c = incomingNeg c ∨ sel c = incomingPos c) ∧ R (sel c) + 1 ≤ R c)
    (hseed : ∀ c i, seed c i → sel c = i) :
    ∀ c i, ForcedEdge F seed c i → sel c = i :=
  forced_sound F seed sel (fun c hw => (hsel c hw).1)
    hseed (fun a b => squareClauses_of_strict hbin hblack hsel a b)

/-- **Unseeded propagation from three black corners.** If the other three corners of a unit square are black, the white corner `c`
is forced to its input `o` outside the square, with no seeds. -/
theorem forced_of_black_others (F : Field) (seed : Site → Site → Prop) {a b : ℤ} {c o : Site}
    (hc : c ∈ squareCorners a b) (hw : laplacian F c = 0)
    (ho : o = incomingNeg c ∨ o = incomingPos c) (hout : o ∉ squareCorners a b)
    (hblack : ∀ c' ∈ squareCorners a b, c' ≠ c → laplacian F c' = -1) :
    ForcedEdge F seed c o :=
  ForcedEdge.unit (fun _ => c) hc hw ho hout (fun c' hc' hne => Or.inl (hblack c' hc' hne))
    (fun c' hc' hne h0 => absurd (hblack c' hc' hne) (by rw [h0]; norm_num))

/-- **A decided example on a standard field.** The standard field of the word `(1,)` (`scripts/permit_local.py`, `standard`) has
the unit square with lower-left corner `(−3, 1)`: its corner `(−3, 1)` is white and its other three corners are black. Its values on
the eight sites that determine the four corner Laplacians are `−2, −3, −1, 0, −4, −7, −3, −3` at `(−3,1), (−4,1), (−2,1), (−2,0),
(−3,2), (−3,3), (−2,2), (−1,2)`. From these values alone, unseeded propagation forces `(−3, 1)` to its outside input `(−4, 1)`. -/
theorem unseeded_forces_standard_window (F : Field) (h1 : F (-3, 1) = -2) (h2 : F (-4, 1) = -3)
    (h3 : F (-2, 1) = -1) (h4 : F (-2, 0) = 0) (h5 : F (-3, 2) = -4) (h6 : F (-3, 3) = -7)
    (h7 : F (-2, 2) = -3) (h8 : F (-1, 2) = -3) :
    ForcedEdge F (fun _ _ => False) (-3, 1) (-4, 1) := by
  have hl1 : laplacian F (-3, 1) = 0 := by
    norm_num [laplacian, incomingNeg, incomingPos, EvenSite, h1, h2, h3]
  have hl2 : laplacian F (-3 + 1, 1) = -1 := by
    norm_num [laplacian, incomingNeg, incomingPos, EvenSite, h3, h4, h7]
  have hl3 : laplacian F (-3, 1 + 1) = -1 := by
    norm_num [laplacian, incomingNeg, incomingPos, EvenSite, h1, h5, h6]
  have hl4 : laplacian F (-3 + 1, 1 + 1) = -1 := by
    norm_num [laplacian, incomingNeg, incomingPos, EvenSite, h5, h7, h8]
  refine forced_of_black_others F _ (a := -3) (b := 1) ?_ hl1 ?_ ?_ ?_
  · simp [squareCorners]
  · norm_num [incomingNeg, incomingPos, EvenSite]
  · norm_num [squareCorners]
  · intro c' hc' hne
    simp only [squareCorners, Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact hl2
    · exact hl3
    · exact hl4

end FLatticePaper.SquareClauses
