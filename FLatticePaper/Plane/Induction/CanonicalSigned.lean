import FLatticePaper.Plane.Induction.S3Canonical
import FLatticePaper.Plane.Induction.OldPolicy

/-! Task 71: the canonical signed policy at a word, and its producing direction to `OldPolicyData`.

`CanonicalSignedPolicy frame F` extends the S3 `CanonicalPolicy` (quota, `P` and `J₊` nonincreasing along the policy, the strict rank,
the prescribed free directions, the raw-slip permit `permitted`) with:

* `sel`, `sel_input`, `white_policy`, `squares`: the W1 selection. At each white the policy keeps exactly the selected input, and the
  selection satisfies every unit square clause (`squareClauses_of_strict` gives the clauses from a strict rank). Q1.md l.38.
* `rawSlipMinus`: the raw slip `D₋(y) = F y − F (y − σ)` does not increase along the policy (Q1.md l.38, sign `−1`). The sign `+1`
  is `permitted`, so it is derived, not assumed.
* `chainNonincreasing`: the chain potential `Φ_η = D_η + P(· + ησ)` does not increase along the policy (Q1.md l.40). Not derived: `P` is
  compared at the shifted edge `(c + ησ, i + ησ)`, and `ησ` need not be in the child's deck span (for `3/5` under `1/2`, `1/1` the short
  shift `(−4, −2)` is not in the span of `(5, 3)` and `(−2, 8)`).
* `reflection`, `westAtException`: reflection about `I` and the prescribed west input at the exceptional vertex when `ε = 1`. Named as
  fields: they come from the symmetric definition and the W1 prescriptions, not from the other fields.

`oldPolicyData_of_canonical` produces `OldPolicyData frame F (fun _ _ => False)`: the retained edges are the policy, and the quota,
`priceNonincreasing`, the two raw-slip signs and `forcedRetained` are derived. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses

/-- The canonical signed policy of a frame: the S3 canonical policy with the W1 selection, the raw-slip sign `−1`, the chain
comparison, the reflection and the exceptional west input. -/
structure CanonicalSignedPolicy (frame : ChildFrame) (F : Field) extends CanonicalPolicy frame F where
  /-- The W1 selection at the whites. -/
  sel : Site → Site
  /-- The selection is an input at each white. -/
  sel_input : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c
  /-- At a white the policy keeps exactly the selected input. -/
  white_policy : ∀ c, laplacian F c = 0 → ∀ i, policy c i ↔ i = sel c
  /-- The selection satisfies every unit square clause. -/
  squares : ∀ a b : ℤ, SquareClauseSat F sel a b
  /-- The raw slip `D₋(y) = F y − F (y − σ)` does not increase along the policy (Q1.md l.38). -/
  rawSlipMinus : NonincreasingAlong (fun y => F y - F (y + (-1 : ℤ) • frame.shortShift)) policy
  /-- The chain potential `Φ_η` does not increase along the policy, for `η = ±1` (Q1.md l.40). -/
  chainNonincreasing : ∀ η : ℤ, (η = 1 ∨ η = -1) → NonincreasingAlong (frame.chainPotential F η) policy
  /-- Reflection about `I`: the policy is carried to itself. -/
  reflection : ∀ c i, policy c i → policy (reflectionI - c) (reflectionI - i)
  /-- The prescribed west input at the exceptional vertex when `ε = 1`. -/
  westAtException : frame.eps = 1 →
    policy (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)
      (incomingNeg (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1))

/-- The primitive price is the cut grade with `A = 1`, `C = 0`, `η = 1`. -/
theorem cutGrade_one_zero_one (frame : ChildFrame) (F : Field) (z : Site) :
    frame.cutGrade F 1 0 1 z = frame.price F z := by
  unfold ChildFrame.cutGrade
  ring

/-- A forced edge of the empty seed sits at a white. -/
theorem laplacian_eq_zero_of_unseeded_forced {F : Field} {c i : Site}
    (h : ForcedEdge F (fun _ _ => False) c i) : laplacian F c = 0 := by
  cases h with
  | seed hs => exact False.elim hs
  | @unit a b c' o inside hc hw ho hout hin hforced => exact hw

/-- Forced white edges are retained: the policy keeps the selected input at a white (`forced_sound`). -/
theorem forcedRetained_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    ∀ c i, ForcedEdge F (fun _ _ => False) c i → C.policy c i := by
  intro c i h
  have hw := laplacian_eq_zero_of_unseeded_forced h
  have hsel : C.sel c = i :=
    forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h' => False.elim h') C.squares c i h
  exact (C.white_policy c hw i).mpr hsel.symm

/-- `P` does not increase along the policy: the price is the cut grade `cutGrade F 1 0 1`. -/
theorem price_nonincreasing_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    NonincreasingAlong (frame.price F) C.policy := by
  intro c i h
  have h1 := C.nonincreasingP c i h
  rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
  exact h1

/-- The raw slip with sign `+1` does not increase along the policy: it is the permit `permitted`. -/
theorem rawSlipPlus_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    NonincreasingAlong (fun y => F y - F (y + (1 : ℤ) • frame.shortShift)) C.policy := by
  intro c i h
  have h1 := C.permitted c i h
  simp only [slipPermits, slipIncrement] at h1
  simp only [one_smul]
  linarith

/-- Both raw-slip signs do not increase along the policy. -/
theorem rawSlip_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → NonincreasingAlong (fun y => F y - F (y + η • frame.shortShift)) C.policy := by
  intro η hη
  rcases hη with rfl | rfl
  · exact rawSlipPlus_of_canonical C
  · exact C.rawSlipMinus

/-- **The producing direction (task 71).** The canonical signed policy at a frame gives an `OldPolicyData` with the empty seed. -/
def oldPolicyData_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    OldPolicyData frame F (fun _ _ => False) where
  retained := C.policy
  quota := C.quota
  priceNonincreasing := price_nonincreasing_of_canonical C
  rawSlipNonincreasing := rawSlip_of_canonical C
  chainNonincreasing := C.chainNonincreasing
  reflection := C.reflection
  forcedRetained := forcedRetained_of_canonical C
  westAtException := C.westAtException

end FLatticePaper.Induction
