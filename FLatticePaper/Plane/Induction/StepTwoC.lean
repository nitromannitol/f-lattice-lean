import FLatticePaper.Plane.Induction.EndpointDeck
import FLatticePaper.Plane.Induction.CutReflect
import FLatticePaper.Plane.Induction.ZoneI1

/-! Task w3, step 2(c): the nominal earlier value steps by `0` or `η`.

With `g i = Dq (vAt i)` (the raw slip at the `i`-th labelled V point of the conjugate) the step is
`g (i + 1) − g i ∈ {0, η}`. This is arithmetic: the period rule `g (i + L') = g i + 2η` (`EndpointDeck.Dq_transverse`) and the raw
row on one period. The row is the named input `RawRow` (E4, the clipped identity at `conjWord word`, whose input is the strictly
earlier trace). The plus row is the minus row reflected through `(1,−1)` (`CutReflect`). The range conditions `1 ≤ r'`,
`r' + 2 ≤ L'` come from the frame's parent bounds and the child identities. -/

namespace FLatticePaper.StepTwoC

open Farey FLatticePaper FLatticePaper.Induction

/-- The raw row on one period, with `r'` the conjugate's own parent sum and `L'` its period. -/
def rowVal (η r L i : ℤ) : ℤ :=
  if η = -1 then (if i = 0 then 0 else if i ≤ r then -1 else -2)
  else (if i ≤ L - r - 2 then 0 else if i ≤ L - 2 then 1 else 2)

/-- The named row (E4): `g` takes the values `rowVal` on one period. -/
def RawRow (g : ℤ → ℤ) (η r L : ℤ) : Prop :=
  ∀ i : ℤ, 0 ≤ i → i < L → g i = rowVal η r L i

/-- **The step on one period.** -/
theorem step_mem (g : ℤ → ℤ) (η r L : ℤ) (hη : η = 1 ∨ η = -1) (hr1 : 1 ≤ r) (hr2 : r + 2 ≤ L)
    (hper : ∀ i, g (i + L) = g i + 2 * η) (hrow : RawRow g η r L) (i : ℤ) :
    g (i + 1) - g i = 0 ∨ g (i + 1) - g i = η := by
  have hL : 0 < L := by omega
  have hmod : ∀ q x : ℤ, g (x + q * L) = g x + 2 * η * q := by
    intro q
    induction q using Int.induction_on with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have e : x + ((k : ℤ) + 1) * L = (x + (k : ℤ) * L) + L := by ring
      rw [e, hper, ih x]
      ring
    | pred k ih =>
      intro x
      have h1 := hper (x + (-(k : ℤ) - 1) * L)
      have e : x + (-(k : ℤ) - 1) * L + L = x + (-(k : ℤ)) * L := by ring
      rw [e, ih x] at h1
      linear_combination (-1 : ℤ) * h1
  obtain ⟨a, b, ha0, haL, hi⟩ : ∃ a b : ℤ, 0 ≤ a ∧ a < L ∧ i = a + b * L :=
    ⟨i % L, i / L, Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL, by
      rw [Int.emod_def]
      ring⟩
  subst hi
  have hg0 : g 0 = 0 := by
    rw [hrow 0 le_rfl (by omega)]
    rcases hη with rfl | rfl
    all_goals simp only [rowVal]
    all_goals norm_num
    all_goals (try split_ifs)
    all_goals omega
  have hgL : g (L - 1) = 2 * η := by
    rw [hrow (L - 1) (by omega) (by omega)]
    rcases hη with rfl | rfl <;> simp only [rowVal] <;> norm_num <;> split_ifs <;> omega
  rcases lt_or_eq_of_le (show a + 1 ≤ L by omega) with hlt | heq
  · -- inside the period
    have e1 : a + b * L + 1 = (a + 1) + b * L := by ring
    rw [e1, hmod b (a + 1), hmod b a]
    have hk : g (a + 1) - g a = 0 ∨ g (a + 1) - g a = η := by
      rw [hrow (a + 1) (by omega) (by omega), hrow a ha0 (by omega)]
      rcases hη with rfl | rfl <;> simp only [rowVal] <;> norm_num <;> split_ifs <;> omega
    rcases hk with hk | hk
    · left
      linear_combination hk
    · right
      linear_combination hk
  · -- the last site of the period steps to the first site of the next one
    have e2 : a + b * L + 1 = 0 + (b + 1) * L := by linear_combination heq
    have ha : a = L - 1 := by omega
    rw [e2, hmod (b + 1) 0, hmod b a]
    have hga : g a = 2 * η := by rw [ha]; exact hgL
    left
    rw [hg0, hga]
    ring

/-- The row arithmetic under the reflection: `rowVal (−1) (L−1−i) + 2 = rowVal 1 i` on one period. -/
theorem rowVal_flip (r L i : ℤ) (hr1 : 1 ≤ r) (hiL : i < L) :
    rowVal (-1) r L (L - 1 - i) + 2 * (-1) * (-1) = rowVal 1 r L i := by
  simp only [rowVal]
  norm_num
  split_ifs <;> omega

/-- **The plus row from the minus row.** `D_+(V_i) = D_−(V_{L'−1−i}) + 2` (`CutReflect`), so the plus row is the minus row
reflected in the period. -/
theorem rawRow_plus (C : ChildFrame) {G : Field} (hP : C.Packet G) (hI : ∀ z, G (reflectionI - z) = G z)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r)
    (hrowM : RawRow (fun i => EndpointDeck.Dq C G (-1) (FreeEnum.vAt C base i)) (-1)
      (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C)) :
    RawRow (fun i => EndpointDeck.Dq C G 1 (FreeEnum.vAt C base i)) 1
      (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C) := by
  obtain ⟨hr1, hr2⟩ : 1 ≤ C.parents.odd.den + C.parents.odd.num ∧
      C.parents.odd.den + C.parents.odd.num + 2 ≤ FreeEnum.period C := by
    have hb := C.valid.odd_bounds
    have he := C.valid.even_bounds
    unfold Fraction.InUnitInterval at hb he
    have hd := ZoneI1.child_den_eq C
    have hn := ZoneI1.child_num_eq C
    unfold FreeEnum.period
    omega
  intro i hi0 hiL
  have e1 := CutReflect.Dq_reflect C hI (FreeEnum.vAt C base i)
  have hrefl := CutReflect.refl_cut C base hbase i
  have e2 : reflectionI - FreeEnum.vAt C base i =
      FreeEnum.vAt C base (FreeEnum.period C - 1 - i) + (-1 : ℤ) • Vdeck C := by
    rw [← hrefl]
    unfold reflectionI
    ext <;> simp <;> ring
  have e3 := EndpointDeck.Dq_smul_transverse C hP (-1) (-1) (FreeEnum.vAt C base (FreeEnum.period C - 1 - i))
  have hm : EndpointDeck.Dq C G (-1) (FreeEnum.vAt C base (FreeEnum.period C - 1 - i)) =
      rowVal (-1) (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C) (FreeEnum.period C - 1 - i) :=
    hrowM _ (by omega) (by omega)
  show EndpointDeck.Dq C G 1 (FreeEnum.vAt C base i) = _
  rw [e1, e2, e3, hm]
  exact rowVal_flip _ _ _ hr1 hiL

/-- **Step 2(c).** For the labelled V points `vAt i` of the frame and the shift `s`, the value `f k = Dq (vAt (k − s))`
steps by `0` or `η` from `k` to `k + 1`. Only the minus row is named (E4); the plus row is `rawRow_plus`. -/
theorem step_two_c (C : ChildFrame) {G : Field} (hP : C.Packet G) (hI : ∀ z, G (reflectionI - z) = G z)
    (η : ℤ) (hη : η = 1 ∨ η = -1)
    (base : ℤ → Site)
    (hbase : ∀ r : ℤ, 0 ≤ r → r < FreeEnum.period C → base r ∈ C.freeV ∧ (base r).2 = r)
    (hrowM : RawRow (fun i => EndpointDeck.Dq C G (-1) (FreeEnum.vAt C base i)) (-1)
      (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C))
    (s k : ℤ) :
    EndpointDeck.Dq C G η (FreeEnum.vAt C base (k + 1 - s)) - EndpointDeck.Dq C G η (FreeEnum.vAt C base (k - s)) = 0 ∨
      EndpointDeck.Dq C G η (FreeEnum.vAt C base (k + 1 - s)) - EndpointDeck.Dq C G η (FreeEnum.vAt C base (k - s)) = η := by
  obtain ⟨hr1, hr2⟩ : 1 ≤ C.parents.odd.den + C.parents.odd.num ∧
      C.parents.odd.den + C.parents.odd.num + 2 ≤ FreeEnum.period C := by
    have hb := C.valid.odd_bounds
    have he := C.valid.even_bounds
    unfold Fraction.InUnitInterval at hb he
    have hd := ZoneI1.child_den_eq C
    have hn := ZoneI1.child_num_eq C
    unfold FreeEnum.period
    omega
  have hper : ∀ i, EndpointDeck.Dq C G η (FreeEnum.vAt C base (i + FreeEnum.period C)) =
      EndpointDeck.Dq C G η (FreeEnum.vAt C base i) + 2 * η := by
    intro i
    have h := EarlierValues.vAt_add_mul_period C base i 1
    rw [one_mul, one_smul] at h
    rw [h]
    exact EndpointDeck.Dq_transverse C hP η _
  have hrow : RawRow (fun i => EndpointDeck.Dq C G η (FreeEnum.vAt C base i)) η
      (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C) := by
    rcases hη with rfl | rfl
    · exact rawRow_plus C hP hI base hbase hrowM
    · exact hrowM
  have e : k + 1 - s = (k - s) + 1 := by ring
  rw [e]
  exact step_mem (fun i => EndpointDeck.Dq C G η (FreeEnum.vAt C base i)) η
    (C.parents.odd.den + C.parents.odd.num) (FreeEnum.period C) hη hr1 hr2 hper hrow (k - s)

end FLatticePaper.StepTwoC
