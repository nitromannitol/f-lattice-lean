import FLatticePaper.Plane.Induction.RankFromForts

/-! Signed policies (task 38, the I3 policy notions), shared by the strong estimates of the earlier word.

A *retained relation* `retained c i` says that the policy keeps the input `i` of the centre `c` (`incomingNeg c` or
`incomingPos c`, see `FLatticePaper.Edge`). The notions below are the ones the I3 fix uses:

* `RetainQuota field retained`: the quota of a signed policy. A black centre (Laplacian `-1`) retains both inputs, a white
  centre (Laplacian `0`) at least one. This is `PermitLocal` (`retainQuota_iff_permitLocal`).
* `NonincreasingAlong Φ retained`: `Φ i ≤ Φ c` on every retained edge; `NondecreasingAlong Φ retained`: `Φ c ≤ Φ i`.
* `NoCrossStars P`: the two increments of a primitive `P` at a centre do not have opposite nonzero signs.
* `chainReflect R w x = R - w - x` and `ReflectedPolicy R w retained`: the chain mate's policy, pulled back by the
  reflection `ξ ↦ R' − w' − ξ` of the fix (`R`, `w` the reflection centre and relative shift). -/

namespace FLatticePaper

/-- The quota of a signed policy: a black centre retains both inputs, a white centre at least one. -/
def RetainQuota (field : Field) (retained : Site → Site → Prop) : Prop :=
  (∀ c, laplacian field c = -1 → retained c (incomingNeg c) ∧ retained c (incomingPos c)) ∧
  (∀ c, laplacian field c = 0 → retained c (incomingNeg c) ∨ retained c (incomingPos c))

theorem retainQuota_iff_permitLocal (field : Field) (retained : Site → Site → Prop) :
    RetainQuota field retained ↔ PermitLocal field retained :=
  Iff.rfl

/-- `Φ` does not increase along the retained edges: from a centre to a retained input. -/
def NonincreasingAlong (Φ : Site → ℤ) (retained : Site → Site → Prop) : Prop :=
  ∀ c i, retained c i → Φ i ≤ Φ c

/-- `Φ` does not decrease along the retained edges: from a centre to a retained input. -/
def NondecreasingAlong (Φ : Site → ℤ) (retained : Site → Site → Prop) : Prop :=
  ∀ c i, retained c i → Φ c ≤ Φ i

/-- The two increments of a primitive `P` at each centre do not have opposite nonzero signs. -/
def NoCrossStars (P : Site → ℤ) : Prop :=
  ∀ c, ¬ ((0 < P (incomingNeg c) - P c ∧ P (incomingPos c) - P c < 0) ∨
    (P (incomingNeg c) - P c < 0 ∧ 0 < P (incomingPos c) - P c))

/-- The reflection `ξ ↦ R − w − ξ` of the chain mate, with its centre `R` and relative shift `w`. -/
def chainReflect (R w x : Site) : Site :=
  R - w - x

/-- The chain mate's policy, pulled back by the reflection `chainReflect R w`. -/
def ReflectedPolicy (R w : Site) (retained : Site → Site → Prop) : Site → Site → Prop :=
  fun c i => retained (chainReflect R w c) (chainReflect R w i)

end FLatticePaper
