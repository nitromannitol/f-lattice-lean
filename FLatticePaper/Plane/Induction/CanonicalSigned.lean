import FLatticePaper.Plane.Induction.S3Canonical
import FLatticePaper.Plane.Induction.S3FreeBoundary
import FLatticePaper.Plane.Induction.OldPolicy
import FLatticePaper.Plane.Induction.ReflectionI

/-! Task 71/72: the canonical signed policies, one for each sign `η = ±1` (Q1: the auxiliary game of sign `η` prescribes the
horizontal sign `−1` and the vertical sign `η`), and their producing direction to `OldPolicyData` of the same sign.

`CanonicalSignedPolicy frame F η` extends the S3 `CanonicalPolicy frame F η` (quota, `P` and `J` nonincreasing along the policy, the
strict rank, the free-white uniqueness, the raw-slip permit of sign `η`) with:

* `sel`, `sel_input`, `white_policy`, `squares`: the W1 selection (the unit square clauses);
* `prescribed`: the sign-`η` prescription at the free centres (`PrescribedAt`): at a free H (V) white the selected input is
  `c + prescribedH η c` (`c + prescribedV η c`);
* `policyEdge`, `westAtException`.

`CanonicalSignedGames frame F` is the family of the two signs: `game η` for `η = ±1`, and the chain claim `chainNonincreasing` of
`Φ_η` along `game η` (the open §4 claim, not derived here). `chainPairs_of_games` gives the `ChainPairData` of `game η`, whose opposite
policy is `game (−η)`: its raw slip, quota and price monotonicity are those of the sign `−η` policy.

`oldPolicyData_of_canonical hF G η hη` produces `OldPolicyData frame F (fun _ _ => False) η` from the sign-`η` component. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.SquareClauses

/-- The sign-`η` prescription of the free directions (Q1): at a free H (V) white centre the policy selects exactly the prescribed
input. -/
def PrescribedAt (frame : ChildFrame) (F : Field) (η : ℤ) (P : Site → Site → Prop) : Prop :=
  (∀ c, c ∈ frame.freeH → laplacian F c = 0 → ∀ j, P c j ↔ j = c + frame.prescribedH η c) ∧
  (∀ c, c ∈ frame.freeV → laplacian F c = 0 → ∀ j, P c j ↔ j = c + frame.prescribedV η c)

/-- The chain data of one sign `η`: the opposite policy `opp` (of sign `−η`, translated by `ησ` in the g-policy), its raw slip, quota
and price monotonicity, and the chain potential `Φ_η = D_η + P(· + ησ)` along the F-policy `P`. The g-policy is `c ↦ opp (c + ησ)`
(`translated_rawSlip`: `D_η(z) = −D_{−η}(z + ησ)`). -/
structure ChainPairData (frame : ChildFrame) (F : Field) (η : ℤ) (P : Site → Site → Prop) where
  /-- The opposite-sign policy on `F`: its raw slip `D_{−η}` does not increase along it. The g-policy is `c ↦ opp (c + ησ)`. -/
  opp : Site → Site → Prop
  oppRawSlip : NonincreasingAlong (fun y => F y - F (y + (-η) • frame.shortShift)) opp
  /-- The opposite policy is a genuine quota policy of `F` (black keeps both inputs, white keeps one): the translated g-policy has its
  quota (`TWO_RANK` local step, `hoppQuota`). -/
  oppQuota : RetainQuota F opp
  /-- The price does not increase along the opposite policy: the translated g-policy has `P_shift` nonincreasing (`hoppPrice`). -/
  oppPrice : NonincreasingAlong (frame.price F) opp
  /-- The chain potential `Φ_η = D_η + P(· + ησ)` does not increase along the F-policy `P` (§4). -/
  chainNonincreasing : NonincreasingAlong (frame.chainPotential F η) P

/-- The canonical signed policy of the sign `η` of a frame (Q1: one auxiliary game per sign): the S3 canonical policy of sign `η`, the W1
selection, the sign-`η` prescription, the exceptional west input. -/
structure CanonicalSignedPolicy (frame : ChildFrame) (F : Field) (η : ℤ) extends CanonicalPolicy frame F η where
  /-- The W1 selection at the whites. -/
  sel : Site → Site
  /-- The selection is an input at each white. -/
  sel_input : ∀ c, laplacian F c = 0 → sel c = incomingNeg c ∨ sel c = incomingPos c
  /-- At a white the policy keeps exactly the selected input. -/
  white_policy : ∀ c, laplacian F c = 0 → ∀ i, policy c i ↔ i = sel c
  /-- The selection satisfies every unit square clause. -/
  squares : ∀ a b : ℤ, SquareClauseSat F sel a b
  /-- The sign-`η` prescription at the free centres (Q1): the horizontal sign `−1`, the vertical sign `η`. -/
  prescribed : PrescribedAt frame F η policy
  /-- A retained edge is an edge of the graph: the retained input is an input of its centre. -/
  policyEdge : ∀ c i, policy c i → Edge i c
  /-- The prescribed west input at the exceptional vertex when `ε = 1`. -/
  westAtException : frame.eps = 1 →
    policy (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1)
      (incomingNeg (frame.parents.odd.num - frame.parents.odd.den + 1, frame.parents.odd.den + frame.parents.odd.num - 1))

/-- The two signs of a frame: the canonical signed policies `game η` for `η = ±1`, and the chain claim along each of them. -/
structure CanonicalSignedGames (frame : ChildFrame) (F : Field) where
  /-- The canonical signed policy of the sign `η = ±1`. -/
  game : ∀ η : ℤ, (η = 1 ∨ η = -1) → CanonicalSignedPolicy frame F η
  /-- The chain potential `Φ_η` does not increase along `game η`: the W1 chain theorem `ChainW1.chain_nonincreasing_of_W1`
  (Q24/Q28), whose deck equivariance premises are proved for rank policies in `DeckSelection`. -/
  chainNonincreasing : ∀ η : ℤ, (hη : η = 1 ∨ η = -1) →
    NonincreasingAlong (frame.chainPotential F η) (game η hη).policy

/-- The sign `−η` of a unit sign is a unit sign. -/
theorem neg_unit {η : ℤ} (hη : η = 1 ∨ η = -1) : -η = 1 ∨ -η = -1 := by
  rcases hη with rfl | rfl <;> simp

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
theorem forcedRetained_of_canonical {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η) :
    ∀ c i, ForcedEdge F (fun _ _ => False) c i → C.policy c i := by
  intro c i h
  have hw := laplacian_eq_zero_of_unseeded_forced h
  have hsel : C.sel c = i :=
    forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h' => False.elim h') C.squares c i h
  exact (C.white_policy c hw i).mpr hsel.symm

/-- `P` does not increase along the policy: the price is the cut grade `cutGrade F 1 0 1`. -/
theorem price_nonincreasing_of_canonical {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η) :
    NonincreasingAlong (frame.price F) C.policy := by
  intro c i h
  have h1 := C.nonincreasingP c i h
  rw [cutGrade_one_zero_one, cutGrade_one_zero_one] at h1
  exact h1

/-- The raw slip of the sign `η` does not increase along the policy of the sign `η`: it is the permit `permitted` of the game. -/
theorem rawSlip_of_canonical {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η) :
    NonincreasingAlong (fun y => F y - F (y + η • frame.shortShift)) C.policy := by
  intro c i h
  have h1 := C.permitted c i h
  simp only [slipPermits, slipIncrement] at h1
  linarith

/-- The chain data of the sign `η`: the opposite policy is the sign `−η` game, with its raw slip, quota and price monotonicity. -/
def chainPairs_of_games {frame : ChildFrame} {F : Field} (G : CanonicalSignedGames frame F) (η : ℤ)
    (hη : η = 1 ∨ η = -1) : ChainPairData frame F η (G.game η hη).policy where
  opp := (G.game (-η) (neg_unit hη)).policy
  oppRawSlip := rawSlip_of_canonical (G.game (-η) (neg_unit hη))
  oppQuota := (G.game (-η) (neg_unit hη)).quota
  oppPrice := price_nonincreasing_of_canonical (G.game (-η) (neg_unit hη))
  chainNonincreasing := G.chainNonincreasing η hη

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
theorem forcedWhiteUnique_of_canonical {frame : ChildFrame} {F : Field} {η : ℤ} (C : CanonicalSignedPolicy frame F η) :
    ∀ z i, C.policy z i → laplacian F z = 0 →
      ∀ o, ForcedEdge F (fun _ _ => False) z o → o = i := by
  intro z i h hw o ho
  have hi := (C.white_policy z hw i).mp h
  have hsel : C.sel z = o :=
    forced_sound F (fun _ _ => False) C.sel C.sel_input (fun _ _ h' => False.elim h') C.squares z o ho
  exact (hi.trans hsel).symm

/-- The reflection about `I` at the roots of `OldPolicyData.reflection`: a black root (both inputs retained, and `I − c` is black
by the symmetry `F (I − z) = F z`) or a forced-white edge (its reflection is forced, `forced_reflectI`). -/
theorem reflection_of_canonical {frame : ChildFrame} {F : Field} {η : ℤ} (hF : ∀ z, F (reflectionI - z) = F z)
    (C : CanonicalSignedPolicy frame F η) :
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

/-- **The producing direction (task 71, per sign).** The sign-`η` component of the canonical signed games gives an `OldPolicyData` of
the sign `η` with the empty seed, given the `I`-symmetry of the field (task 72). -/
def oldPolicyData_of_canonical {frame : ChildFrame} {F : Field} (hF : ∀ z, F (reflectionI - z) = F z)
    (G : CanonicalSignedGames frame F) (η : ℤ) (hη : η = 1 ∨ η = -1) :
    OldPolicyData frame F (fun _ _ => False) η where
  retained := (G.game η hη).policy
  quota := (G.game η hη).quota
  priceNonincreasing := price_nonincreasing_of_canonical (G.game η hη)
  rawSlipNonincreasing := rawSlip_of_canonical (G.game η hη)
  chainNonincreasing := G.chainNonincreasing η hη
  reflection := reflection_of_canonical hF (G.game η hη)
  forcedRetained := forcedRetained_of_canonical (G.game η hη)
  forcedWhiteUnique := forcedWhiteUnique_of_canonical (G.game η hη)
  westAtException := (G.game η hη).westAtException

end FLatticePaper.Induction
