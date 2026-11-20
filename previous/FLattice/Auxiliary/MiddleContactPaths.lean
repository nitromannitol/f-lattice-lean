import FLattice.Auxiliary.MiddleDeficit
import FLattice.Auxiliary.MiddleSpecialValues
import FLattice.Auxiliary.MiddleRank
import FLattice.Auxiliary.FiniteComparison

/-!
# Physical white cycles for the two smallest-branch profiles

The four source cycles are unions of actual signed physical period orbits.
Their native incoming edges and white deficits are proved from the literal
profiles. With a global lower bound, contact propagates along a strictly
decreasing physical rank, contradicting finiteness of the equality set.
These are conditional contact-exclusion helpers, not transport theorems.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MiddleProfile

private def cycleStart (ε : Fin 2) (negative : Bool) : ℤ × ℤ :=
  if negative then (if ε = 0 then (0, 2) else (1, -1)) else (0, 0)

private def referenceShift (ε : Fin 2) (negative : Bool) : ℤ × ℤ :=
  if negative then (2 * (-2 + (ε.val : ℤ)), 2 * (-1 + (ε.val : ℤ))) else (0, 0)

private def reference (ε : Fin 2) (negative : Bool) (z : ℤ × ℤ) : ℤ :=
  profile ε (z.1 + (referenceShift ε negative).1) (z.2 + (referenceShift ε negative).2)

private def cycleOffset (ε : Fin 2) (t : Fin 4) : ℤ × ℤ :=
  if ε = 0 then
    if t = 0 then (0, 0) else if t = 1 then (-1, 0)
    else if t = 2 then (-1, 1) else (-2, 1)
  else
    if t = 0 then (0, 0) else if t = 1 then (0, -1)
    else if t = 2 then (-1, -1) else (-1, -2)

private def cyclePoint (ε : Fin 2) (negative : Bool) (t : Fin 4) (n : ℤ) : ℤ × ℤ :=
  ((cycleStart ε negative).1 + (cycleOffset ε t).1 - 2 * n,
   (cycleStart ε negative).2 + (cycleOffset ε t).2 + (if ε = 0 then 2 else -2) * n)

private def cycleSlot (ε : Fin 2) (t : Fin 4) : Fin 2 :=
  if ε = 0 ∧ (t = 1 ∨ t = 3) then 1 else 0

private def nextPhase (t : Fin 4) : Fin 4 :=
  if t = 0 then 1 else if t = 1 then 2 else if t = 2 then 3 else 0

private def cycleRegion (ε : Fin 2) (negative : Bool) : Set (ℤ × ℤ) :=
  {z | ∃ t : Fin 4, ∃ n : ℤ, z = cyclePoint ε negative t n}

private theorem incomingPoint_add_even (ε : Fin 2) (x y a b : ℤ) (i : Fin 2)
    (hEven : (a + b) % 2 = 0) :
    incomingPoint ε (x + a) (y + b) i =
      ((incomingPoint ε x y i).1 + a, (incomingPoint ε x y i).2 + b) := by
  have hp : (x + a + (y + b) + (ε.val : ℤ)) % 2 =
      (x + y + (ε.val : ℤ)) % 2 := by omega
  unfold incomingPoint
  rw [hp]
  split <;> apply Prod.ext <;> dsimp <;> omega

private theorem deficit_eq_inputs (ε : Fin 2) (x y : ℤ) :
    incomingDeficit ε x y = 2 * profile ε x y -
      profile ε (incomingPoint ε x y 0).1 (incomingPoint ε x y 0).2 -
      profile ε (incomingPoint ε x y 1).1 (incomingPoint ε x y 1).2 := by
  have hSum := incomingPoint_sum ε (fun z => profile ε z.1 z.2) x y
  rw [Fin.sum_univ_two] at hSum
  unfold incomingDeficit
  split_ifs at hSum ⊢ <;> dsimp at hSum <;> omega

private theorem reference_deficit (ε : Fin 2) (negative : Bool) (z : ℤ × ℤ) :
    2 * reference ε negative z - reference ε negative (incomingPoint ε z.1 z.2 0) -
      reference ε negative (incomingPoint ε z.1 z.2 1) =
      incomingDeficit ε (z.1 + (referenceShift ε negative).1)
        (z.2 + (referenceShift ε negative).2) := by
  have hEven : ((referenceShift ε negative).1 + (referenceShift ε negative).2) % 2 = 0 := by
    cases negative
    · rfl
    · change (2 * (-2 + (ε.val : ℤ)) + 2 * (-1 + (ε.val : ℤ))) % 2 = 0
      omega
  rw [deficit_eq_inputs]
  rw [incomingPoint_add_even ε _ _ _ _ 0 hEven, incomingPoint_add_even ε _ _ _ _ 1 hEven]
  rfl

private theorem cycle_point_white (ε : Fin 2) (negative : Bool) (t : Fin 4) (n : ℤ) :
    incomingDeficit ε
      ((cyclePoint ε negative t n).1 + (referenceShift ε negative).1)
      ((cyclePoint ε negative t n).2 + (referenceShift ε negative).2) = 0 := by
  have hPeriod : incomingDeficit ε
      ((cyclePoint ε negative t n).1 + (referenceShift ε negative).1)
      ((cyclePoint ε negative t n).2 + (referenceShift ε negative).2) =
      incomingDeficit ε
        ((cyclePoint ε negative t 0).1 + (referenceShift ε negative).1)
        ((cyclePoint ε negative t 0).2 + (referenceShift ε negative).2) := by
    fin_cases ε
    · have h := incomingDeficit_add_periods 0
        ((cyclePoint 0 negative t 0).1 + (referenceShift 0 negative).1)
        ((cyclePoint 0 negative t 0).2 + (referenceShift 0 negative).2) n (-n)
      convert h using 1
      all_goals dsimp [cyclePoint]
      all_goals congr 1 <;> ring
    · have h := incomingDeficit_add_periods 1
        ((cyclePoint 1 negative t 0).1 + (referenceShift 1 negative).1)
        ((cyclePoint 1 negative t 0).2 + (referenceShift 1 negative).2) (-n) 0
      convert h using 1
      all_goals dsimp [cyclePoint]
      all_goals congr 1 <;> ring
  rw [hPeriod]
  fin_cases ε <;> cases negative <;> fin_cases t <;> decide

private theorem cycle_next (ε : Fin 2) (negative : Bool) (t : Fin 4) (n : ℤ) :
    incomingPoint ε (cyclePoint ε negative t n).1 (cyclePoint ε negative t n).2
        (cycleSlot ε t) =
      cyclePoint ε negative (nextPhase t) (if t = 3 then n + 1 else n) := by
  fin_cases ε <;> cases negative <;> fin_cases t <;>
    norm_num [cyclePoint, cycleStart, cycleOffset, cycleSlot, nextPhase, Fin.ext_iff]
  all_goals
    unfold incomingPoint
    split_ifs <;> apply Prod.ext <;> dsimp <;> omega

private theorem cycle_rank_drop (ε : Fin 2) (negative : Bool) (t : Fin 4) (n : ℤ) :
    physicalRank ε
      (cyclePoint ε negative (nextPhase t) (if t = 3 then n + 1 else n)).1
      (cyclePoint ε negative (nextPhase t) (if t = 3 then n + 1 else n)).2 <
      physicalRank ε (cyclePoint ε negative t n).1 (cyclePoint ε negative t n).2 := by
  fin_cases ε <;> cases negative <;> fin_cases t <;>
    norm_num [cyclePoint, cycleStart, cycleOffset, nextPhase, Fin.ext_iff]
  all_goals norm_num [physicalRank] <;> omega

private theorem no_cycle_contact_of_finite_contacts
    (ε : Fin 2) (negative : Bool) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z, reference ε negative z ≤ h z)
    (hFinite : {z | h z = reference ε negative z}.Finite) :
    ¬∃ z ∈ cycleRegion ε negative, h z = reference ε negative z := by
  apply FLattice.Auxiliary.not_nonempty_of_finite_rank_descent
    {z | z ∈ cycleRegion ε negative ∧ h z = reference ε negative z}
    (fun z => physicalRank ε z.1 z.2)
    (hFinite.subset (fun _ hz => hz.2))
  intro z hz
  obtain ⟨⟨t, n, rfl⟩, hContact⟩ := hz
  let z := cyclePoint ε negative t n
  have hWhite := reference_deficit ε negative z
  rw [cycle_point_white] at hWhite
  have hContact' : h z = reference ε negative z := hContact
  have hSum := incomingPoint_sum ε h z.1 z.2
  rw [Fin.sum_univ_two] at hSum
  have hStar : h (incomingPoint ε z.1 z.2 0) + h (incomingPoint ε z.1 z.2 1) ≤
      2 * h z := by
    rw [hSum]
    exact hSuperharmonic z.1 z.2
  have hLeft := hLower (incomingPoint ε z.1 z.2 0)
  have hRight := hLower (incomingPoint ε z.1 z.2 1)
  have hContacts : ∀ i : Fin 2,
      h (incomingPoint ε z.1 z.2 i) = reference ε negative (incomingPoint ε z.1 z.2 i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi
    · subst i
      omega
    · subst i
      omega
  refine ⟨cyclePoint ε negative (nextPhase t) (if t = 3 then n + 1 else n), ?_,
    cycle_rank_drop ε negative t n⟩
  constructor
  · exact ⟨nextPhase t, (if t = 3 then n + 1 else n), rfl⟩
  · have h := hContacts (cycleSlot ε t)
    dsimp [z] at h
    rwa [cycle_next] at h

/-- For either native parity, contact at the positive cycle start is impossible
under a global profile lower bound and a finite physical equality set. -/
theorem positive_cycle_start_lt_of_finite_contacts
    (ε : Fin 2) (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + (ε.val : ℤ)) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z, profile ε z.1 z.2 ≤ h z)
    (hFinite : {z | h z = profile ε z.1 z.2}.Finite) :
    0 < h (0, 0) := by
  have hNo := no_cycle_contact_of_finite_contacts ε false h hSuperharmonic
    (by simpa [reference, referenceShift] using hLower)
    (by simpa [reference, referenceShift] using hFinite)
  have hBound := hLower (0, 0)
  rw [profile_origin] at hBound
  by_contra hNotPositive
  apply hNo
  refine ⟨(0, 0), ⟨0, 0, ?_⟩, ?_⟩
  · simp [cyclePoint, cycleStart, cycleOffset]
  · simp only [reference, referenceShift, Bool.false_eq_true, ↓reduceIte, add_zero,
      profile_origin]
    omega

/-- The even negative cycle starts at `(0,2)` with reference value `-2`.
Its contact is excluded by the finite equality set for the full shifted profile. -/
theorem negative_even_cycle_start_lt_of_finite_contacts
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z, profile 0 (z.1 - 4) (z.2 - 2) ≤ h z)
    (hFinite : {z | h z = profile 0 (z.1 - 4) (z.2 - 2)}.Finite) :
    -2 < h (0, 2) := by
  have hNo := no_cycle_contact_of_finite_contacts 0 true h
    (by simpa using hSuperharmonic)
    (by simpa [reference, referenceShift, sub_eq_add_neg] using hLower)
    (by simpa [reference, referenceShift, sub_eq_add_neg] using hFinite)
  have hValue : profile 0 (-4) 0 = -2 := by decide
  have hBound := hLower (0, 2)
  norm_num [hValue] at hBound
  by_contra hNotStrict
  apply hNo
  refine ⟨(0, 2), ⟨0, 0, ?_⟩, ?_⟩
  · norm_num [cyclePoint, cycleStart, cycleOffset]
  · norm_num [reference, referenceShift, hValue]
    omega

/-- The odd negative cycle starts at `(1,-1)` with reference value zero.
Its contact is excluded by the finite equality set for the full shifted profile. -/
theorem negative_odd_cycle_start_lt_of_finite_contacts
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hLower : ∀ z, profile 1 (z.1 - 2) z.2 ≤ h z)
    (hFinite : {z | h z = profile 1 (z.1 - 2) z.2}.Finite) :
    0 < h (1, -1) := by
  have hNo := no_cycle_contact_of_finite_contacts 1 true h
    (by simpa using hSuperharmonic)
    (by simpa [reference, referenceShift, sub_eq_add_neg] using hLower)
    (by simpa [reference, referenceShift, sub_eq_add_neg] using hFinite)
  have hValue : profile 1 (-1) (-1) = 0 := by decide
  have hBound := hLower (1, -1)
  norm_num [hValue] at hBound
  by_contra hNotStrict
  apply hNo
  refine ⟨(1, -1), ⟨0, 0, ?_⟩, ?_⟩
  · norm_num [cyclePoint, cycleStart, cycleOffset]
  · norm_num [reference, referenceShift, hValue]
    omega

end FLattice.Auxiliary.MiddleProfile
