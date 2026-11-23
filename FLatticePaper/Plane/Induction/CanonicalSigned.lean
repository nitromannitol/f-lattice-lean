import FLatticePaper.Plane.Induction.S3Canonical
import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.ReflectionI

/-! Task 71: the canonical signed policy at a word, and its producing direction to `OldPolicyData`.

`CanonicalSignedPolicy frame F` extends the S3 `CanonicalPolicy` (quota, `P` and `J₊` nonincreasing along the policy, the strict rank,
the prescribed free directions, the raw-slip permit `permitted`) with:

* `sel`, `sel_input`, `white_policy`, `squares`: the W1 selection. At each white the policy keeps exactly the selected input, and the
  selection satisfies every unit square clause (`squareClauses_of_strict` gives the clauses from a strict rank). Q1.md l.38.
* `permittedMinus`: the minus raw-slip permit (Q13, sign `−1`): each selected input is permitted for `D₋(y) = F y − F (y − σ)`.
  The raw slip `rawSlipMinus` is derived from it, as `rawSlipPlus_of_canonical` derives the sign `+1` from `permitted`.
* `chainNonincreasing`: the chain potential `Φ_η = D_η + P(· + ησ)` does not increase along the policy (Q1.md l.40). Not derived: `P` is
  compared at the shifted edge `(c + ησ, i + ησ)`, and `ησ` need not be in the child's deck span (for `3/5` under `1/2`, `1/1` the short
  shift `(−4, −2)` is not in the span of `(5, 3)` and `(−2, 8)`).
* `reflection`, `westAtException`: reflection about `I` and the prescribed west input at the exceptional vertex when `ε = 1`. Named as
  fields: they come from the symmetric definition and the W1 prescriptions, not from the other fields.

`oldPolicyData_of_canonical` produces `OldPolicyData frame F (fun _ _ => False)`: the retained edges are the policy, and the quota,
`priceNonincreasing`, the two raw-slip signs and `forcedRetained` are derived. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses

/-- The pair of policies of the chain-gap monotonicity (`.work/fields/canonical/strong_bulk/STRONG_PRICE_AND_ALTERNATE_STEP.md` §4).
For the intermediate `g = F(· + ησ)`, the F-policy `P` has `D_η` nonincreasing, and a translated opposite-sign policy gives a
g-policy along which `D_η` is nondecreasing (`translated_rawSlip`: `D_η(z) = −D_{−η}(z + ησ)`). The two-rank lemma of
`TWO_RANK_RAW_PHI_AUDIT.md` then gives the chain-gap monotonicity: `Φ_η` does not increase along `P` (`chainNonincreasing`, the
conclusion of §4, not derived here). The shift `ησ` is not a deck vector, so this is a statement about the pair, not a consequence
of `P` and `D_η` alone. -/
structure ChainPairData (frame : ChildFrame) (F : Field) (η : ℤ) (P : Site → Site → Prop) where
  /-- The opposite-sign policy on `F`: its raw slip `D_{−η}` does not increase along it. The g-policy is `c ↦ opp (c + ησ)`. -/
  opp : Site → Site → Prop
  oppRawSlip : NonincreasingAlong (fun y => F y - F (y + (-η) • frame.shortShift)) opp
  /-- The chain potential `Φ_η = D_η + P(· + ησ)` does not increase along the F-policy `P` (§4). -/
  chainNonincreasing : NonincreasingAlong (frame.chainPotential F η) P

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
  /-- The minus raw-slip permit (Q13): every selected input is permitted for the raw slip `D₋(y) = F y − F (y − σ)` with
the sign `−1` (the analogue of `permitted`). The minus prescription of `S3FreeBoundary` (`prescribedH`, `prescribedV` at `η = −1`)
is its free-site part; `rawSlipMinus` is derived from it. Q13.md l.17, scripts/s3_free_check.py (`η = −1`). -/
  permittedMinus : ∀ c i, policy c i → slipPermits F (fun z => F (z + (-1 : ℤ) • frame.shortShift)) c i
  /-- The chain pair for each sign `η = ±1` (§4 of the strong-bulk note, task 72 (a)). -/
  chainPairs : ∀ η : ℤ, (η = 1 ∨ η = -1) → ChainPairData frame F η policy
  /-- A retained edge is an edge of the graph: the retained input is an input of its centre. -/
  policyEdge : ∀ c i, policy c i → Edge i c
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

/-- The raw slip with sign `−1` does not increase along the policy: it is the minus permit `permittedMinus` (Q13). -/
theorem rawSlipMinus_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    NonincreasingAlong (fun y => F y - F (y + (-1 : ℤ) • frame.shortShift)) C.policy := by
  intro c i h
  have h1 := C.permittedMinus c i h
  simp only [slipPermits, slipIncrement] at h1
  linarith

/-- Both raw-slip signs do not increase along the policy. -/
theorem rawSlip_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → NonincreasingAlong (fun y => F y - F (y + η • frame.shortShift)) C.policy := by
  intro η hη
  rcases hη with rfl | rfl
  · exact rawSlipPlus_of_canonical C
  · exact rawSlipMinus_of_canonical C

/-- The translated g-policy `c ↦ opp (c + ησ)` has `D_η` nondecreasing along it: `D_η(c) = −D_{−η}(c + ησ)` (§4 of the note). -/
theorem translated_rawSlip {frame : ChildFrame} {F : Field} {η : ℤ} {P : Site → Site → Prop}
    (Q : ChainPairData frame F η P) :
    ∀ c i, Q.opp (c + η • frame.shortShift) (i + η • frame.shortShift) →
      F c - F (c + η • frame.shortShift) ≤ F i - F (i + η • frame.shortShift) := by
  intro c i h
  have h1 := Q.oppRawSlip _ _ h
  have e : ∀ x : Site, x + η • frame.shortShift + (-η) • frame.shortShift = x := by
    intro x
    rw [neg_smul]
    simp
  simp only [e] at h1
  linarith

/-- At a white with an unseeded forced edge `z → o`, the retained input is `o`: the policy keeps the selected input, and the selection
agrees with the forced edge (`forced_sound`). -/
theorem forcedWhiteUnique_of_canonical {frame : ChildFrame} {F : Field} (C : CanonicalSignedPolicy frame F) :
    ∀ z i, C.policy z i → laplacian F z = 0 →
      ∀ o, ForcedEdge F (fun _ _ => False) z o → o = i := by
  intro z i h hw o ho
  have hi := (C.white_policy z hw i).mp h
  have hsel : C.sel z = o :=
    forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h' => False.elim h') C.squares z o ho
  exact (hi.trans hsel).symm

/-- The reflection about `I` at the roots of `OldPolicyData.reflection`: a black root (both inputs retained, and `I − c` is black
by the symmetry `F (I − z) = F z`) or a forced-white edge (its reflection is forced, `forced_reflectI`). -/
theorem reflection_of_canonical {frame : ChildFrame} {F : Field} (hF : ∀ z, F (reflectionI - z) = F z)
    (C : CanonicalSignedPolicy frame F) :
    ∀ c i, C.policy c i → (laplacian F c = -1 ∨ ForcedEdge F (fun _ _ => False) c i) →
      C.policy (reflectionI - c) (reflectionI - i) := by
  intro c i h hroot
  rcases hroot with hb | hfe
  · have hbI : laplacian F (reflectionI - c) = -1 := by
      rw [laplacian_reflectI hF]
      exact hb
    have hE := edge_reflectI (C.policyEdge c i h)
    rcases hE with e | e
    · rw [e]
      exact (C.quota.1 (reflectionI - c) hbI).1
    · rw [e]
      exact (C.quota.1 (reflectionI - c) hbI).2
  · exact forcedRetained_of_canonical C _ _ (forced_reflectI hF hfe)

/-- **The producing direction (task 71).** The canonical signed policy at a frame gives an `OldPolicyData` with the empty seed, given
the `I`-symmetry of the field (task 72). -/
def oldPolicyData_of_canonical {frame : ChildFrame} {F : Field} (hF : ∀ z, F (reflectionI - z) = F z)
    (C : CanonicalSignedPolicy frame F) :
    OldPolicyData frame F (fun _ _ => False) where
  retained := C.policy
  quota := C.quota
  priceNonincreasing := price_nonincreasing_of_canonical C
  rawSlipNonincreasing := rawSlip_of_canonical C
  chainNonincreasing := fun η hη => (C.chainPairs η hη).chainNonincreasing
  reflection := reflection_of_canonical hF C
  forcedRetained := forcedRetained_of_canonical C
  forcedWhiteUnique := forcedWhiteUnique_of_canonical C
  westAtException := C.westAtException

end FLatticePaper.Induction
