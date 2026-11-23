import FLatticePaper.Plane.Induction.ComparisonTransfer
import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! # Task 102 (1): the K-minimum bridge (fixes/Q1.md, the potentials `P`, `J_η`, `K = P + J_η`)

With `D₊ z = F z − F(z + σ)`, `D₋ z = F z − F(z − σ)`, `J_η = ⌈D_η/2⌉` (`(D + 1)/2` with the floor division) and `P = frame.price F`, the potentials
are `K_η = P + J_η` for the standard field `F = standardField word`. The comparison fields of Q1 are `cmpLowW` (realising `P = c₀ − 1`),
`cmpUpW = F(· + σ)` (realising `D₊ = 0`) and `cmpDownW = F(· − σ) − 2` (realising `D₋ = −2`), each below `F` on the closed polygon.

* `minK_black_input_plus`, `minK_black_input_minus`: at a black minimum of `K_η` on a fort `S` of `F` inside the polygon, some input in `S`
  has the same `K_η` (the rounded slips and `P` do not increase along black edges, `ComparisonTransfer`).
* `contact_cmpUp_of_J0`: at a point of the polygon with `J₊ = 0`, `D₊ = 0`, so `F` meets `cmpUpW`.
* `contact_cmpDown_of_Jm1`: with `J₋ = −1`, `D₋ = −2`, so `F` meets `cmpDownW`.
* `contact_cmpLow_of_P`: with `P = c₀ − 1`, `F` meets `cmpLowW` (`price_eq_low_iff`).

What is not here: the note's passage from a `K`-minimum to a free site at the pair `(c₀, 0)` (Q1 l.13, "this passage must therefore hit a
free site at the same pair"). The lemmas above give the contacts at such a site; the fan lemmas of `FanPropagation` need a parabolic
comparison field (even laplacian `0`), and `cmpUpW`, `cmpDownW` are shifts of `F` without that pattern, so the fan from these contacts is a
separate argument. -/

namespace FLatticePaper.KMinBridge

open Farey FLatticePaper FLatticePaper.Induction

/-- The rounded slip `J₊ = ⌈D₊/2⌉` with `D₊ z = F z − F(z + σ)`. -/
noncomputable def jPlusW (word : Word) (z : Site) : ℤ :=
  (standardField word z - standardField word (z + (frameAt word).shortShift) + 1) / 2

/-- The rounded slip `J₋ = ⌈D₋/2⌉` with `D₋ z = F z − F(z − σ)`. -/
noncomputable def jMinusW (word : Word) (z : Site) : ℤ :=
  (standardField word z - standardField word (z + -(frameAt word).shortShift) + 1) / 2

/-- The potential `K₊ = P + J₊`. -/
noncomputable def kPlusW (word : Word) (z : Site) : ℤ :=
  (frameAt word).price (standardField word) z + jPlusW word z

/-- The potential `K₋ = P + J₋`. -/
noncomputable def kMinusW (word : Word) (z : Site) : ℤ :=
  (frameAt word).price (standardField word) z + jMinusW word z

/-- **Black minimum propagates (sign `+`)**: at a black point of the polygon in the minimum of `K₊` over a fort `S` of `F`, an input in `S`
has the same `K₊`. -/
theorem minK_black_input_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hpk : (frameAt word).Packet (standardField word)) {S : Set Site}
    (hfort : IsIncomingFort (standardField word) S) {z : Site} (hzS : z ∈ S)
    (hzE : z ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) z = -1)
    (hmin : ∀ w ∈ S, kPlusW word z ≤ kPlusW word w) :
    ∃ i : Site, (i = FLatticePaper.incomingNeg z ∨ i = FLatticePaper.incomingPos z) ∧ i ∈ S ∧
      kPlusW word i = kPlusW word z := by
  have hsome : FLatticePaper.incomingNeg z ∈ S ∨ FLatticePaper.incomingPos z ∈ S := by
    rcases hfort z hzS with ⟨_, hs⟩ | ⟨hl0, _⟩
    · exact hs
    · exfalso
      omega
  have key : ∀ i : Site, (i = FLatticePaper.incomingNeg z ∨ i = FLatticePaper.incomingPos z) → i ∈ S →
      ∃ j : Site, (j = FLatticePaper.incomingNeg z ∨ j = FLatticePaper.incomingPos z) ∧ j ∈ S ∧
        kPlusW word j = kPlusW word z := by
    intro i hi hiS
    have hp := price_nonincrease_black h hSE hWord hpk hzE hb hi
    have hj := jplus_nonincrease_black h hSE hpk hzE hb hi
    have hmi := hmin i hiS
    refine ⟨i, hi, hiS, ?_⟩
    unfold kPlusW jPlusW at hmi ⊢
    omega
  rcases hsome with hn | hp'
  · obtain ⟨j, hj, hjS, hjK⟩ := key _ (Or.inl rfl) hn
    exact ⟨j, hj, hjS, hjK⟩
  · obtain ⟨j, hj, hjS, hjK⟩ := key _ (Or.inr rfl) hp'
    exact ⟨j, hj, hjS, hjK⟩

/-- **Black minimum propagates (sign minus)**: the same for `K₋` and the rounded slip `J₋`. -/
theorem minK_black_input_minus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word)
    (hpk : (frameAt word).Packet (standardField word)) {S : Set Site}
    (hfort : IsIncomingFort (standardField word) S) {z : Site} (hzS : z ∈ S)
    (hzE : z ∈ (frameAt word).closedPolygon) (hb : laplacian (standardField word) z = -1)
    (hmin : ∀ w ∈ S, kMinusW word z ≤ kMinusW word w) :
    ∃ i : Site, (i = FLatticePaper.incomingNeg z ∨ i = FLatticePaper.incomingPos z) ∧ i ∈ S ∧
      kMinusW word i = kMinusW word z := by
  have hsome : FLatticePaper.incomingNeg z ∈ S ∨ FLatticePaper.incomingPos z ∈ S := by
    rcases hfort z hzS with ⟨_, hs⟩ | ⟨hl0, _⟩
    · exact hs
    · exfalso
      omega
  have key : ∀ i : Site, (i = FLatticePaper.incomingNeg z ∨ i = FLatticePaper.incomingPos z) → i ∈ S →
      ∃ j : Site, (j = FLatticePaper.incomingNeg z ∨ j = FLatticePaper.incomingPos z) ∧ j ∈ S ∧
        kMinusW word j = kMinusW word z := by
    intro i hi hiS
    have hp := price_nonincrease_black h hSE hWord hpk hzE hb hi
    have hj := jminus_nonincrease_black h hSE hpk hzE hb hi
    have hmi := hmin i hiS
    refine ⟨i, hi, hiS, ?_⟩
    unfold kMinusW jMinusW at hmi ⊢
    omega
  rcases hsome with hn | hp'
  · obtain ⟨j, hj, hjS, hjK⟩ := key _ (Or.inl rfl) hn
    exact ⟨j, hj, hjS, hjK⟩
  · obtain ⟨j, hj, hjS, hjK⟩ := key _ (Or.inr rfl) hp'
    exact ⟨j, hj, hjS, hjK⟩

/-- **The upper contact** (`D₊ = 0`): at a point of the polygon with `J₊ = 0`, `F` meets `cmpUpW`. -/
theorem contact_cmpUp_of_J0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {z : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hJ : jPlusW word z = 0) :
    standardField word z = cmpUpW word z := by
  have hle : cmpUpW word z ≤ standardField word z :=
    isCmp_le_on_E h hSE hWord (Or.inr (Or.inl rfl)) z hz
  have hle2 : standardField word (z + (frameAt word).shortShift) ≤ standardField word z := hle
  unfold jPlusW at hJ
  show standardField word z = standardField word (z + (frameAt word).shortShift)
  omega

/-- **The lower contact of `D₋`** (`D₋ = −2`): with `J₋ = −1` on the polygon, `F` meets `cmpDownW`. -/
theorem contact_cmpDown_of_Jm1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hWord : StrongEstimates word) {z : Site}
    (hz : z ∈ (frameAt word).closedPolygon) (hJ : jMinusW word z = -1) :
    standardField word z = cmpDownW word z := by
  have hle : cmpDownW word z ≤ standardField word z :=
    isCmp_le_on_E h hSE hWord (Or.inr (Or.inr rfl)) z hz
  have hle2 : standardField word (z + -(frameAt word).shortShift) - 2 ≤ standardField word z := hle
  unfold jMinusW at hJ
  show standardField word z = standardField word (z + -(frameAt word).shortShift) - 2
  omega

/-- **The lower contact of `P`** (`P = c₀ − 1`): `F` meets `cmpLowW`. -/
theorem contact_cmpLow_of_P {word : Word} {z : Site}
    (hP : (frameAt word).price (standardField word) z = (frameAt word).cutPrice - 1) :
    standardField word z = cmpLowW word z :=
  (price_eq_low_iff z).mp hP

end FLatticePaper.KMinBridge
