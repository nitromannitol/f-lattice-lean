import FLatticePaper.Graph
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FLatticePaper.GeneralK

/-- A unit spatial step in the physical square grid. -/
inductive AxisStep where
  | right | left | up | down
  deriving DecidableEq

def AxisStep.vector : AxisStep → Site
  | .right => (1, 0)
  | .left => (-1, 0)
  | .up => (0, 1)
  | .down => (0, -1)

/-- The final physical vertex of a finite walk. -/
def walkEnd (start : Site) : List AxisStep → Site
  | [] => start
  | step :: rest => walkEnd (start + step.vector) rest

/-- Every vertex visited by a walk, including both endpoints. -/
def walkVertices (start : Site) : List AxisStep → Finset Site
  | [] => {start}
  | step :: rest => insert start (walkVertices (start + step.vector) rest)

@[simp] theorem start_mem_walkVertices (start : Site) (walk : List AxisStep) : start ∈ walkVertices start walk := by
  cases walk <;> simp [walkVertices]

theorem end_mem_walkVertices (start : Site) (walk : List AxisStep) : walkEnd start walk ∈ walkVertices start walk := by
  induction walk generalizing start with
  | nil => simp [walkEnd, walkVertices]
  | cons step rest ih => exact Finset.mem_insert_of_mem (ih (start + step.vector))

def residueVertex (period : ℕ) (site : Site) : ZMod period × ZMod period := (site.1, site.2)

private def residueIndicator (period : ℕ) (site : Site) (x y : ZMod period) : ℤ :=
  if (x, y) = residueVertex period site then 1 else 0

private theorem residueIndicator_sub_first {period : ℕ} (site : Site) (x y : ZMod period) :
    residueIndicator period site (x - 1) y = residueIndicator period (site + (1, 0)) x y := by
  simp [residueIndicator, residueVertex, sub_eq_iff_eq_add]

private theorem residueIndicator_sub_second {period : ℕ} (site : Site) (x y : ZMod period) :
    residueIndicator period site x (y - 1) = residueIndicator period (site + (0, 1)) x y := by
  simp [residueIndicator, residueVertex, sub_eq_iff_eq_add]

private theorem sum_residueIndicator {period : ℕ} [NeZero period] (site : Site) :
    ∑ x : ZMod period, ∑ y : ZMod period, residueIndicator period site x y = 1 := by
  simp only [residueIndicator, residueVertex, Prod.mk.injEq]
  calc
    _ = ∑ x : ZMod period, (if x = (site.1 : ZMod period) then 1 else (0 : ℤ)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x = (site.1 : ZMod period) <;> simp [h]
    _ = 1 := by simp

private def horizontalStep (period : ℕ) (start : Site) (step : AxisStep) (x y : ZMod period) : ℤ :=
  match step with
  | .right => residueIndicator period start x y
  | .left => -residueIndicator period (start + step.vector) x y
  | .up | .down => 0

private def verticalStep (period : ℕ) (start : Site) (step : AxisStep) (x y : ZMod period) : ℤ :=
  match step with
  | .up => residueIndicator period start x y
  | .down => -residueIndicator period (start + step.vector) x y
  | .left | .right => 0

/-- Net crossings of each rightward edge by a walk projected to the square quotient. -/
def horizontalWalkCount (period : ℕ) (start : Site) (walk : List AxisStep) (x y : ZMod period) : ℤ :=
  match walk with
  | [] => 0
  | step :: rest => horizontalStep period start step x y + horizontalWalkCount period (start + step.vector) rest x y

/-- Net crossings of each upward edge by a walk projected to the square quotient. -/
def verticalWalkCount (period : ℕ) (start : Site) (walk : List AxisStep) (x y : ZMod period) : ℤ :=
  match walk with
  | [] => 0
  | step :: rest => verticalStep period start step x y + verticalWalkCount period (start + step.vector) rest x y

private theorem stepCount_divergence {period : ℕ} (start : Site) (step : AxisStep) (x y : ZMod period) :
    horizontalStep period start step x y - horizontalStep period start step (x - 1) y +
      (verticalStep period start step x y - verticalStep period start step x (y - 1)) =
      residueIndicator period start x y - residueIndicator period (start + step.vector) x y := by
  cases step <;> simp [horizontalStep, verticalStep, AxisStep.vector, residueIndicator_sub_first, residueIndicator_sub_second,
    add_assoc, show ((0 : ℤ), (0 : ℤ)) = (0 : Site) from rfl] <;> omega

theorem walkCount_divergence {period : ℕ} (start : Site) (walk : List AxisStep) (x y : ZMod period) :
    horizontalWalkCount period start walk x y - horizontalWalkCount period start walk (x - 1) y +
      (verticalWalkCount period start walk x y - verticalWalkCount period start walk x (y - 1)) =
      residueIndicator period start x y - residueIndicator period (walkEnd start walk) x y := by
  induction walk generalizing start with
  | nil => simp [horizontalWalkCount, verticalWalkCount, walkEnd]
  | cons step rest ih =>
    simp only [horizontalWalkCount, verticalWalkCount, walkEnd]
    have hstep := stepCount_divergence start step x y
    have hrest := ih (start + step.vector)
    omega

theorem walkCount_divergence_eq_zero {period : ℕ} {start : Site} {walk : List AxisStep}
    (hclosed : residueVertex period (walkEnd start walk) = residueVertex period start) (x y : ZMod period) :
    horizontalWalkCount period start walk x y - horizontalWalkCount period start walk (x - 1) y +
      (verticalWalkCount period start walk x y - verticalWalkCount period start walk x (y - 1)) = 0 := by
  rw [walkCount_divergence]
  simp only [residueIndicator, hclosed, sub_self]

theorem sum_horizontalWalkCount {period : ℕ} [NeZero period] (start : Site) (walk : List AxisStep) :
    ∑ x : ZMod period, ∑ y : ZMod period, horizontalWalkCount period start walk x y =
      (walkEnd start walk).1 - start.1 := by
  induction walk generalizing start with
  | nil => simp [horizontalWalkCount, walkEnd]
  | cons step rest ih =>
    simp only [horizontalWalkCount, Finset.sum_add_distrib, ih, walkEnd]
    cases step <;> simp [horizontalStep, AxisStep.vector, sum_residueIndicator, Finset.sum_neg_distrib] <;> omega

theorem sum_verticalWalkCount {period : ℕ} [NeZero period] (start : Site) (walk : List AxisStep) :
    ∑ x : ZMod period, ∑ y : ZMod period, verticalWalkCount period start walk x y =
      (walkEnd start walk).2 - start.2 := by
  induction walk generalizing start with
  | nil => simp [verticalWalkCount, walkEnd]
  | cons step rest ih =>
    simp only [verticalWalkCount, Finset.sum_add_distrib, ih, walkEnd]
    cases step <;> simp [verticalStep, AxisStep.vector, sum_residueIndicator, Finset.sum_neg_distrib] <;> omega

theorem walkCount_eq_zero_of_not_visited {period : ℕ} (start : Site) (walk : List AxisStep) (x y : ZMod period)
    (hmiss : ∀ site ∈ walkVertices start walk, (x, y) ≠ residueVertex period site) :
    horizontalWalkCount period start walk x y = 0 ∧ verticalWalkCount period start walk x y = 0 := by
  induction walk generalizing start with
  | nil => simp [horizontalWalkCount, verticalWalkCount]
  | cons step rest ih =>
    have hstart := hmiss start (start_mem_walkVertices ..)
    have htail (site : Site) (hmem : site ∈ walkVertices (start + step.vector) rest) :
        (x, y) ≠ residueVertex period site := hmiss site (Finset.mem_insert_of_mem hmem)
    have hnext := htail (start + step.vector) (start_mem_walkVertices ..)
    obtain ⟨hh, hv⟩ := ih (start + step.vector) htail
    simp only [horizontalWalkCount, verticalWalkCount, hh, hv, add_zero]
    cases step <;> simp [horizontalStep, verticalStep, residueIndicator, hstart, hnext]

end FLatticePaper.GeneralK
