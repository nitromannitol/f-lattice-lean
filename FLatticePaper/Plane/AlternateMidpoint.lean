import FLatticePaper.Rank
import Mathlib.Data.Prod.Lex

namespace FLatticePaper

/-- A rank whose required decreasing inputs also obey an edge constraint.
The constraint has arguments (center, input). -/
def IsConstrainedBurningRank {α : Type*} [LT α] (field : Field) (rank : Site → α)
    (permits : Site → Site → Prop) : Prop :=
  ∀ center,
    let neg := permits center (incomingNeg center) ∧ rank (incomingNeg center) < rank center
    let pos := permits center (incomingPos center) ∧ rank (incomingPos center) < rank center
    (laplacian field center = -1 ∧ neg ∧ pos) ∨ (laplacian field center = 0 ∧ (neg ∨ pos))

theorem IsConstrainedBurningRank.toIsBurningRank {α : Type*} [LT α]
    {field : Field} {rank : Site → α} {permits : Site → Site → Prop}
    (h : IsConstrainedBurningRank field rank permits) : IsBurningRank field rank := by
  intro center
  rcases h center with ⟨hlap, hn, hp⟩ | ⟨hlap, hn | hp⟩
  · exact Or.inl ⟨hlap, hn.2, hp.2⟩
  · exact Or.inr ⟨hlap, Or.inl hn.2⟩
  · exact Or.inr ⟨hlap, Or.inr hp.2⟩

/-- The alternate midpoint uses ceiling, including at negative heights. -/
def roundedMidpoint (first second : Field) : Field :=
  fun site => first site - (first site - second site) / 2

theorem roundedMidpoint_eq_neg_floor (first second : Field) (site : Site) :
    roundedMidpoint first second site = (- ((-(first site + second site)) / 2)) := by
  unfold roundedMidpoint
  omega

/-- The first component is parity of the height gap, not parity of the physical site. -/
def roundedMidpointRank {α : Type*} (first second : Field) (rank : Site → α) :
    Site → ℤ ×ₗ α :=
  fun site => toLex ((first site - second site) % 2, rank site)

/-- The input increment of the difference of the two sheets. -/
def slipIncrement (first second : Field) (center input : Site) : ℤ :=
  (first input - second input) - (first center - second center)

/-- The two actual input increments of the gap have absolute value at most one. -/
def HasUnitSlip (first second : Field) : Prop :=
  ∀ center input, Edge input center →
    -1 ≤ slipIncrement first second center input ∧ slipIncrement first second center input ≤ 1

/-- At an even gap, the two input increments are not opposite nonzero steps. -/
def NoEvenSlipSaddle (first second : Field) : Prop :=
  ∀ site, (first site - second site) % 2 = 0 →
    let neg := slipIncrement first second site (incomingNeg site)
    let pos := slipIncrement first second site (incomingPos site)
    ¬ ((neg = -1 ∧ pos = 1) ∨ (neg = 1 ∧ pos = -1))

private theorem ediv_sub_ediv (center input : ℤ) :
    input / 2 - center / 2 = (center % 2 + (input - center)) / 2 := by
  rw [show center % 2 + (input - center) = input + (-(center / 2)) * 2 by omega,
    Int.add_mul_ediv_right _ _ (by decide)]
  omega

theorem laplacian_roundedMidpoint (first second : Field) (site : Site) :
    let parity := (first site - second site) % 2
    laplacian (roundedMidpoint first second) site = laplacian first site -
      (parity + slipIncrement first second site (incomingNeg site)) / 2 -
      (parity + slipIncrement first second site (incomingPos site)) / 2 := by
  have hneg := ediv_sub_ediv (first site - second site)
    (first (incomingNeg site) - second (incomingNeg site))
  have hpos := ediv_sub_ediv (first site - second site)
    (first (incomingPos site) - second (incomingPos site))
  dsimp only [laplacian, roundedMidpoint, slipIncrement]
  omega

theorem laplacian_eq_sub_slipIncrements (first second : Field) (site : Site) :
    laplacian second site = laplacian first site -
      slipIncrement first second site (incomingNeg site) -
      slipIncrement first second site (incomingPos site) := by
  unfold laplacian slipIncrement
  omega

private theorem roundedStar
    (parity standardDelta negStep posStep : ℤ) (negLowers posLowers : Prop)
    (hparity : parity = 0 ∨ parity = 1)
    (hneg : -1 ≤ negStep ∧ negStep ≤ 1) (hpos : -1 ≤ posStep ∧ posStep ≤ 1)
    (hnoSaddle : parity = 0 →
      ¬ ((negStep = -1 ∧ posStep = 1) ∨ (negStep = 1 ∧ posStep = -1)))
    (hsecond : standardDelta - negStep - posStep = -1 ∨ standardDelta - negStep - posStep = 0)
    (hchosen : (standardDelta = -1 ∧ (negStep ≤ 0 ∧ negLowers) ∧ (posStep ≤ 0 ∧ posLowers)) ∨
      (standardDelta = 0 ∧ ((negStep ≤ 0 ∧ negLowers) ∨ (posStep ≤ 0 ∧ posLowers)))) :
    let roundedDelta := standardDelta - (parity + negStep) / 2 - (parity + posStep) / 2
    let neg := (parity + negStep) % 2 < parity ∨ (parity + negStep) % 2 = parity ∧ negLowers
    let pos := (parity + posStep) % 2 < parity ∨ (parity + posStep) % 2 = parity ∧ posLowers
    (roundedDelta = -1 ∧ neg ∧ pos) ∨ (roundedDelta = 0 ∧ (neg ∨ pos)) := by
  dsimp only
  have hnegCases : negStep = -1 ∨ negStep = 0 ∨ negStep = 1 := by omega
  have hposCases : posStep = -1 ∨ posStep = 0 ∨ posStep = 1 := by omega
  rcases hparity with rfl | rfl <;>
    rcases hchosen with ⟨rfl, hchosen⟩ | ⟨rfl, hchosen⟩ <;>
    rcases hnegCases with rfl | rfl | rfl <;> rcases hposCases with rfl | rfl | rfl <;> simp_all

/-- Section 9's local-to-plane midpoint calculation. Its hypotheses are the
binary second sheet, the full-star slip bounds and exclusion, and the first
sheet's decreasing choices on which the slip is nonincreasing. -/
theorem isBurningRank_roundedMidpoint {α : Type*} [LT α]
    {first second : Field} {rank : Site → α}
    (hsecond : ∀ site, laplacian second site = -1 ∨ laplacian second site = 0)
    (hstep : HasUnitSlip first second) (hnoSaddle : NoEvenSlipSaddle first second)
    (hr : IsConstrainedBurningRank first rank
      (fun center input => slipIncrement first second center input ≤ 0)) :
    IsBurningRank (roundedMidpoint first second) (roundedMidpointRank first second rank) := by
  intro site
  have parityAt (input : Site) :
      (first input - second input) % 2 =
        ((first site - second site) % 2 + slipIncrement first second site input) % 2 := by
    unfold slipIncrement
    omega
  have hparity : (first site - second site) % 2 = 0 ∨ (first site - second site) % 2 = 1 := by omega
  have hb := hsecond site
  rw [laplacian_eq_sub_slipIncrements first second site] at hb
  simp only [laplacian_roundedMidpoint, roundedMidpointRank, Prod.Lex.toLex_lt_toLex,
    parityAt (incomingNeg site), parityAt (incomingPos site)]
  exact roundedStar _ _ _ _ _ _ hparity
    (hstep site (incomingNeg site) (Or.inl rfl)) (hstep site (incomingPos site) (Or.inr rfl))
    (hnoSaddle site) hb (hr site)

/-- The elementary height identity used when the gap is confined to the
three integer levels centered at the prescribed odd threshold. -/
theorem roundedMidpoint_eq_min_of_slip (first second : Field) (site : Site) (level : ℤ)
    (hlo : 2 * level ≤ first site - second site)
    (hhi : first site - second site ≤ 2 * level + 2) :
    roundedMidpoint first second site =
      min (first site - level) (second site + level + 1) := by
  unfold roundedMidpoint
  by_cases hle : first site - level ≤ second site + level + 1
  · rw [min_eq_left hle]
    omega
  · rw [min_eq_right (by omega : second site + level + 1 ≤ first site - level)]
    omega

end FLatticePaper
