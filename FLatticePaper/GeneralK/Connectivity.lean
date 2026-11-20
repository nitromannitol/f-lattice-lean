import FLatticePaper.GeneralK.Columns
import Mathlib.Logic.Relation

namespace FLatticePaper.GeneralK

/-- A path following the physical inputs, from a center to its input. -/
abbrev InputReaches (k : ℤ) : Site → Site → Prop :=
  Relation.ReflTransGen (fun center input => input = incomingNeg k center ∨ input = incomingPos k center)

private theorem step_up {k : ℤ} (column row offset : ℤ) (hlo : 0 < offset) (hhi : offset < k) :
    columnSite k column row (offset + 1) = incomingPos k (columnSite k column row offset) := by
  have hphase : ¬ Retained k (columnSite k column row offset) := by
    rw [Retained, columnSite_phase, Int.emod_eq_of_lt hlo.le hhi]
    omega
  rw [incomingPos, if_neg hphase]
  apply Prod.ext
  · rfl
  · dsimp [columnSite]
    ring

private theorem step_down {k : ℤ} (column row offset : ℤ) (hlo : 0 < offset) (hhi : offset < k) :
    columnSite k column row (offset - 1) = incomingNeg k (columnSite k column row offset) := by
  have hphase : ¬ Retained k (columnSite k column row offset) := by
    rw [Retained, columnSite_phase, Int.emod_eq_of_lt hlo.le hhi]
    omega
  rw [incomingNeg, if_neg hphase]
  apply Prod.ext
  · rfl
  · dsimp [columnSite]
    ring

private theorem inputReaches_up {k : ℤ} (column row offset : ℤ) (steps : ℕ)
    (hlo : 0 < offset) (hhi : offset + steps ≤ k) :
    InputReaches k (columnSite k column row offset) (columnSite k column row (offset + steps)) := by
  induction steps with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ steps ih =>
    have hpath := ih (by omega)
    rw [Int.natCast_succ, ← add_assoc]
    exact hpath.tail (Or.inr (step_up column row _ (by omega) (by omega)))

private theorem inputReaches_down {k : ℤ} (column row offset : ℤ) (steps : ℕ)
    (hlo : 0 ≤ offset - steps) (hhi : offset < k) :
    InputReaches k (columnSite k column row offset) (columnSite k column row (offset - steps)) := by
  induction steps with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ steps ih =>
    have hpath := ih (by omega)
    rw [Int.natCast_succ, sub_add_eq_sub_sub]
    exact hpath.tail (Or.inl (step_down column row _ (by omega) (by omega)))

private theorem columnSite_top (k column row : ℤ) :
    columnSite k column row k = columnSite k column (row + 1) 0 := by
  apply Prod.ext
  · rfl
  · dsimp [columnSite]
    ring

private theorem inputReaches_right {k : ℤ} (hk : 2 ≤ k) (column row : ℤ) :
    InputReaches k (columnSite k column row 0) (columnSite k (column + 1) row 0) := by
  have hfirst := Relation.ReflTransGen.single (r := fun center input =>
    input = incomingNeg k center ∨ input = incomingPos k center)
    (Or.inr (incomingPos_columnSite k column row).symm)
  have hrest := inputReaches_down (k := k) (column + 1) row 1 1 (by decide) (by omega)
  exact hfirst.trans hrest

private theorem inputReaches_left {k : ℤ} (hk : 2 ≤ k) (column row : ℤ) :
    InputReaches k (columnSite k column row 0) (columnSite k (column - 1) row 0) := by
  have hfirst := Relation.ReflTransGen.single (r := fun center input =>
    input = incomingNeg k center ∨ input = incomingPos k center)
    (Or.inl (incomingNeg_columnSite k column row).symm)
  have hrest := inputReaches_up (k := k) (column - 1) (row - 1) (k - 1) 1 (by omega) (by omega)
  rw [show k - 1 + ((1 : ℕ) : ℤ) = k by omega, columnSite_top, sub_add_cancel] at hrest
  exact hfirst.trans hrest

private theorem inputReaches_nextRow {k : ℤ} (hk : 2 ≤ k) (column row : ℤ) :
    InputReaches k (columnSite k column row 0) (columnSite k column (row + 1) 0) := by
  have hfirst := Relation.ReflTransGen.single (r := fun center input =>
    input = incomingNeg k center ∨ input = incomingPos k center)
    (Or.inr (incomingPos_columnSite k column row).symm)
  have hrest := inputReaches_up (k := k) (column + 1) row 1 (k - 1).toNat (by decide) (by omega)
  rw [show 1 + ((k - 1).toNat : ℤ) = k by omega, columnSite_top] at hrest
  have hlast := inputReaches_left hk (column + 1) (row + 1)
  rw [add_sub_cancel_right] at hlast
  exact hfirst.trans (hrest.trans hlast)

private theorem inputReaches_prevRow {k : ℤ} (hk : 2 ≤ k) (column row : ℤ) :
    InputReaches k (columnSite k column row 0) (columnSite k column (row - 1) 0) := by
  have hfirst := Relation.ReflTransGen.single (r := fun center input =>
    input = incomingNeg k center ∨ input = incomingPos k center)
    (Or.inl (incomingNeg_columnSite k column row).symm)
  have hrest := inputReaches_down (k := k) (column - 1) (row - 1) (k - 1) (k - 1).toNat (by omega) (by omega)
  rw [show k - 1 - ((k - 1).toNat : ℤ) = 0 by omega] at hrest
  have hlast := inputReaches_right hk (column - 1) (row - 1)
  rw [sub_add_cancel] at hlast
  exact hfirst.trans (hrest.trans hlast)

/-- The full physical graph is connected in the direction of input moves. -/
theorem inputReaches_all {k : ℤ} (hk : 2 ≤ k) (first last : Site) : InputReaches k first last := by
  have hretained (column row nextColumn nextRow : ℤ) :
      InputReaches k (columnSite k column row 0) (columnSite k nextColumn nextRow 0) := by
    have hcolumn : InputReaches k (columnSite k column row 0) (columnSite k nextColumn row 0) :=
      Int.inductionOn' nextColumn column Relation.ReflTransGen.refl
        (fun i _ h => h.trans (inputReaches_right hk i row)) (fun i _ h => h.trans (inputReaches_left hk i row))
    have hrow : InputReaches k (columnSite k nextColumn row 0) (columnSite k nextColumn nextRow 0) :=
      Int.inductionOn' nextRow row Relation.ReflTransGen.refl
        (fun r _ h => h.trans (inputReaches_nextRow hk nextColumn r))
        (fun r _ h => h.trans (inputReaches_prevRow hk nextColumn r))
    exact hcolumn.trans hrow
  let row₁ := (first.1 + first.2) / k
  let off₁ := (first.1 + first.2) % k
  have hoff₁ : 0 ≤ off₁ ∧ off₁ < k := ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hfirst := inputReaches_down (k := k) first.1 row₁ off₁ off₁.toNat (by omega) hoff₁.2
  rw [show off₁ - (off₁.toNat : ℤ) = 0 by omega, columnSite_coordinates] at hfirst
  let row₂ := (last.1 + last.2) / k
  let off₂ := (last.1 + last.2) % k
  have hoff₂ : 0 ≤ off₂ ∧ off₂ < k := ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hlast : columnSite k last.1 row₂ off₂ = last := columnSite_coordinates k last
  rw [← hlast]
  by_cases hoff : off₂ = 0
  · rw [hoff]
    exact hfirst.trans (hretained _ _ _ _)
  · refine hfirst.trans ((hretained first.1 row₁ (last.1 - 1) row₂).trans ?_)
    have hfirstStep := Relation.ReflTransGen.single (r := fun center input =>
      input = incomingNeg k center ∨ input = incomingPos k center)
      (Or.inr (incomingPos_columnSite k (last.1 - 1) row₂).symm)
    rw [sub_add_cancel] at hfirstStep
    have hrest := inputReaches_up (k := k) last.1 row₂ 1 (off₂ - 1).toNat (by decide) (by omega)
    rw [show 1 + ((off₂ - 1).toNat : ℤ) = off₂ by omega] at hrest
    exact hfirstStep.trans hrest

/-- A uniform upper bound at one site propagates along all physical input
paths in a family with pointwise uniform lower bounds. -/
theorem InputReaches.exists_uniform_upper_bound {k : ℤ} {ι : Type*} {fields : ι → Field}
    (hsuper : ∀ i, Superharmonic k (fields i)) (hlower : ∀ site, ∃ lower : ℤ, ∀ i, lower ≤ fields i site)
    {first last : Site} (hpath : InputReaches k first last) (hbase : ∃ upper : ℤ, ∀ i, fields i first ≤ upper) :
    ∃ upper : ℤ, ∀ i, fields i last ≤ upper := by
  induction hpath with
  | refl => exact hbase
  | @tail center input _ hedge ih =>
    obtain ⟨upper, hupper⟩ := ih
    obtain ⟨lowerNeg, hneg⟩ := hlower (incomingNeg k center)
    obtain ⟨lowerPos, hpos⟩ := hlower (incomingPos k center)
    refine ⟨2 * upper - min lowerNeg lowerPos, fun i => ?_⟩
    have hcenter := hupper i
    have hrow := hsuper i center
    unfold laplacian at hrow
    rcases hedge with rfl | rfl
    · have hother := (min_le_right lowerNeg lowerPos).trans (hpos i)
      omega
    · have hother := (min_le_left lowerNeg lowerPos).trans (hneg i)
      omega

end FLatticePaper.GeneralK
