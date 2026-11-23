import FLatticePaper.Plane.RestrictedBellmanRank

/-! Task 43, step 2: the AND-OR Bellman rank of `fixes/Q1.md`, paragraphs 7 and 8.

The game is the one of `restrictedInputs`: a black site (laplacian `−1`) reads the maximum of both inputs, a white site
(laplacian `0`) reads the minimum over its permitted inputs. The iteration `R_{j+1} = max(obstacle, 1 + restrictedInputs R_j)`
stabilizes by `exists_restrictedValue_fixed`, with the stopping bound of `restrictedValue_le_of_uniform_escape`. Here the fixed point
is read as a strict rank: it strictly decreases on both black edges and on a permitted edge at each white (paragraph 7), and at
each unit square the minimum corner is white and its selected edge leaves the square (paragraph 8). -/

namespace FLatticePaper.AndOrRank

open Farey FLatticePaper

/-- A black site reads the maximum of its two inputs. -/
theorem restrictedInputs_black {field : Field} {permits : Site → Site → Prop} {value : Field} {site : Site}
    (h : laplacian field site = -1) :
    restrictedInputs field permits value site = max (value (incomingNeg site)) (value (incomingPos site)) := by
  unfold restrictedInputs
  rw [if_pos h]

/-- A white site reads the value of one of its permitted inputs. -/
theorem restrictedInputs_white {field : Field} {permits : Site → Site → Prop} {value : Field} {site : Site}
    (hloc : PermitLocal field permits) (h : laplacian field site = 0) :
    ∃ i, (i = incomingNeg site ∨ i = incomingPos site) ∧ permits site i ∧
      restrictedInputs field permits value site = value i := by
  have hne : ¬ (laplacian field site = -1) := by
    rw [h]
    norm_num
  unfold restrictedInputs
  rw [if_neg hne]
  by_cases hb : permits site (incomingNeg site) ∧ permits site (incomingPos site)
  · rw [if_pos hb]
    rcases le_total (value (incomingNeg site)) (value (incomingPos site)) with hle | hle
    · exact ⟨incomingNeg site, Or.inl rfl, hb.1, by rw [min_eq_left hle]⟩
    · exact ⟨incomingPos site, Or.inr rfl, hb.2, by rw [min_eq_right hle]⟩
  · rw [if_neg hb]
    by_cases hn : permits site (incomingNeg site)
    · rw [if_pos hn]
      exact ⟨incomingNeg site, Or.inl rfl, hn, rfl⟩
    · rw [if_neg hn]
      have hp : permits site (incomingPos site) := by
        rcases hloc.2 site h with h1 | h1
        · exact absurd h1 hn
        · exact h1
      exact ⟨incomingPos site, Or.inr rfl, hp, rfl⟩

/-- **Paragraph 7, strictness.** A fixed point of the restricted iteration is a strict rank on the game: on black edges
`R i + 1 ≤ R c` for both inputs, and at each white some permitted input has `R i + 1 ≤ R c`. -/
theorem andOr_fixed_strict {field obstacle : Field} {permits : Site → Site → Prop} (hloc : PermitLocal field permits)
    {R : Field} (hfix : ∀ site, R site = max (obstacle site) (1 + restrictedInputs field permits R site)) :
    (∀ site, laplacian field site = -1 → ∀ i, (i = incomingNeg site ∨ i = incomingPos site) → R i + 1 ≤ R site) ∧
    (∀ site, laplacian field site = 0 →
      ∃ i, (i = incomingNeg site ∨ i = incomingPos site) ∧ permits site i ∧ R i + 1 ≤ R site) := by
  constructor
  · intro site hb i hi
    have hmax : R i ≤ max (R (incomingNeg site)) (R (incomingPos site)) := by
      rcases hi with h | h
      · rw [h]
        exact le_max_left _ _
      · rw [h]
        exact le_max_right _ _
    have h1 := hfix site
    rw [restrictedInputs_black hb] at h1
    have h2 : 1 + max (R (incomingNeg site)) (R (incomingPos site)) ≤ R site := by
      rw [h1]
      exact le_max_right _ _
    linarith
  · intro site hw
    obtain ⟨i, hi, hp, heq⟩ := restrictedInputs_white (value := R) hloc hw
    refine ⟨i, hi, hp, ?_⟩
    have h1 := hfix site
    rw [heq] at h1
    rw [h1]
    linarith [le_max_right (obstacle site) (1 + R i)]

/-- The four corners of the unit square with lower-left corner `(a, b)`. -/
def squareCorners (a b : ℤ) : Finset Site :=
  {(a, b), (a + 1, b), (a, b + 1), (a + 1, b + 1)}

/-- Every corner of a unit square has one of its two inputs in the square. -/
theorem square_corner_input (a b : ℤ) {c : Site} (hc : c ∈ squareCorners a b) :
    ∃ i ∈ squareCorners a b, i = incomingNeg c ∨ i = incomingPos c := by
  have hc' : c = (a, b) ∨ c = (a + 1, b) ∨ c = (a, b + 1) ∨ c = (a + 1, b + 1) := by
    simpa [squareCorners] using hc
  have key : incomingNeg c ∈ squareCorners a b ∨ incomingPos c ∈ squareCorners a b := by
    obtain ⟨x, y⟩ := c
    rcases hc' with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      unfold incomingNeg incomingPos squareCorners EvenSite <;> split_ifs <;> simp
  rcases key with h | h
  · exact ⟨_, h, Or.inl rfl⟩
  · exact ⟨_, h, Or.inr rfl⟩

/-- **Paragraph 8, the square clauses.** Let `R` be strict in the sense of `andOr_fixed_strict`, and let the selection
`sel` choose, at each white site, a permitted input with `R (sel) + 1 ≤ R` (exists by strictness). Then every unit square
has a corner `c` that is white, whose selected edge is permitted, strictly decreases `R`, and leaves the square. -/
theorem andOr_square_clause {field : Field} {permits : Site → Site → Prop} {R : Field}
    (hbin : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (hblack : ∀ site, laplacian field site = -1 → ∀ i, (i = incomingNeg site ∨ i = incomingPos site) → R i + 1 ≤ R site)
    (hwhite : ∀ site, laplacian field site = 0 →
      ∃ i, (i = incomingNeg site ∨ i = incomingPos site) ∧ permits site i ∧ R i + 1 ≤ R site)
    (a b : ℤ) :
    ∃ c ∈ squareCorners a b, laplacian field c = 0 ∧
      ∃ i, (i = incomingNeg c ∨ i = incomingPos c) ∧ permits c i ∧ R i + 1 ≤ R c ∧ i ∉ squareCorners a b := by
  obtain ⟨c, hcS, hmin⟩ := (squareCorners a b).exists_min_image R ⟨(a, b), by simp [squareCorners]⟩
  have hw : laplacian field c = 0 := by
    rcases hbin c with hb | hw
    · exfalso
      obtain ⟨j, hj, hji⟩ := square_corner_input a b hcS
      have h1 := hblack c hb j hji
      have h2 := hmin j hj
      linarith
    · exact hw
  obtain ⟨i, hi, hp, hR⟩ := hwhite c hw
  refine ⟨c, hcS, hw, i, hi, hp, hR, fun hiS => ?_⟩
  have h2 := hmin i hiS
  linarith

/-- **Paragraph 7, assembled.** Under the deck covering and grade-jump hypotheses of the restricted Bellman theory, a unit grade
`K` (the `grade`) with an escape within `horizon` steps from every site, the iteration `R_{j+1} = max(horizon K, 1 + restrictedInputs
R_j)` has a fixed point `R`, and `R` is a strict rank: it strictly decreases on both black edges and on a permitted edge at each
white. -/
theorem andOr_rank_of_escape {field grade : Field} {permits : Site → Site → Prop} {deck : PeriodDeck} {sites : Finset Site}
    {horizon : ℕ} {bound : ℤ}
    (hcover : deck.Covers sites) (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site, grade (site + step) = grade site + increment)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hloc : PermitLocal field permits)
    (hjump : ∀ site, grade (incomingNeg site) ≤ grade site + bound ∧ grade (incomingPos site) ≤ grade site + bound)
    (hbound : 0 ≤ bound)
    (hescape : ∀ site, RestrictedEscapesWithin field grade permits (grade site) horizon site) :
    ∃ R : Field, (∀ site, R site = max ((horizon : ℤ) * grade site) (1 + restrictedInputs field permits R site)) ∧
      (∀ site, laplacian field site = -1 → ∀ i, (i = incomingNeg site ∨ i = incomingPos site) → R i + 1 ≤ R site) ∧
      (∀ site, laplacian field site = 0 →
        ∃ i, (i = incomingNeg site ∨ i = incomingPos site) ∧ permits site i ∧ R i + 1 ≤ R site) := by
  have hshift : ∀ step ∈ deck.span, ∃ increment : ℤ, ∀ site,
      (fun point => (horizon : ℤ) * grade point) (site + step) =
        (fun point => (horizon : ℤ) * grade point) site + increment := by
    intro step hstep
    obtain ⟨inc, hinc⟩ := hgrade step hstep
    exact ⟨(horizon : ℤ) * inc, fun site => by simp only [hinc]; ring⟩
  have hupper : ∀ m site, restrictedBellmanValue field permits (fun point => (horizon : ℤ) * grade point) m site ≤
      (fun point => (horizon : ℤ) * grade point) site + ((horizon : ℤ) + (horizon : ℤ) ^ 2 * bound) :=
    fun m site => restrictedValue_le_of_uniform_escape hjump hbound hescape m site
  obtain ⟨n, hn⟩ := exists_restrictedValue_fixed hcover heven hcharge hperm hshift
    ((horizon : ℤ) + (horizon : ℤ) ^ 2 * bound) hupper
  have hfix : ∀ site, restrictedBellmanValue field permits (fun point => (horizon : ℤ) * grade point) n site =
      max ((horizon : ℤ) * grade site) (1 + restrictedInputs field permits
        (restrictedBellmanValue field permits (fun point => (horizon : ℤ) * grade point) n) site) := by
    intro site
    exact (congrFun hn site).symm
  obtain ⟨hb, hw⟩ := andOr_fixed_strict (obstacle := fun point => (horizon : ℤ) * grade point) hloc hfix
  exact ⟨_, hfix, hb, hw⟩

end FLatticePaper.AndOrRank
