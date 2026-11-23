import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.W1NonfreeHsq
import FLatticePaper.Plane.Induction.PriceH
import FLatticePaper.Plane.Induction.PriceDeck

/-! # The arc monotonicity of `Ψ` and the bottom bound (task 116, steps (b) and the bottom side)

* `arc_ge_one`: a sequence with `Ψ = 1` at index `1` and nondecreasing along the arc from index `1` on is `≥ 1` from index `1` on.
* `psi_arc_W0`, `psi_arc_W1`: the arc sequences `H j` (W0) and `refl (H j)` (W1, `refl z = (d+1−z₁, n−1−z₂)`, so `refl(H₀) = H_last`). The
  monotonicity along the arc is `psi_mono` applied to the retained edges of the inherited policy `P`, i.e. `sheetPolicyA P (sheetShift) (H j) (H (j+1))`
  — the note's canonical V-chain edges. This is the one hypothesis `hret` of the arc (named: the note's canonical edges; the inherited structure
  does not record them as fields, see the report).
* `bottom_W0`, `bottom_W1`: `PriceH`'s arc lemmas with the `Ψ` values above. The phase identities `P = c₀ − E_H` and `E_H = 1 + min(0,Ψ−1)`
  (W0) or `P = c₀ − 1 − E_H(refl z)`, `E_H(refl z) = min(0, Ψ(refl z) − 1)` (W1) are the H-price note's identities, named as hypotheses. -/

namespace FLatticePaper.ArcPsi

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step

/-- The induction along the arc: `Ψ = 1` at index `1`, nondecreasing along the arc from index `1` on, gives `Ψ ≥ 1` from index `1` on. -/
theorem arc_ge_one (Ψ : ℕ → ℤ) (N : ℕ) (h1 : Ψ 1 = 1) (hmono : ∀ j, 1 ≤ j → j + 1 < N → Ψ j ≤ Ψ (j + 1)) :
    ∀ j, 1 ≤ j → j < N → 1 ≤ Ψ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    rw [h1]
  | succ k hk ih =>
    intro hN
    have h2 := ih (by omega)
    have h3 := hmono k hk (by omega)
    omega

/-- The reflection of the child H arc in phase W1: `refl z = U + (1,−1) − z`, `U = (d, n)`; `refl(1,0) = H_last`. -/
def reflH (word : Word) (z : Site) : Site :=
  ((frameAt word).child.den + 1 - z.1, (frameAt word).child.num - 1 - z.2)

/-- **The arc in phase W0**: `Ψ(H_j) ≥ 1` for `1 ≤ j < d`, from `Ψ(H_1) = 1` and the retained arc edges of the inherited policy. -/
theorem psi_arc_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hW0 : (frameAt word).eps = -1) (H : ℕ → Site) (N : ℕ) (hH1 : H 1 = (2, 0))
    (hret : ∀ j, 1 ≤ j → j + 1 < N →
      sheetPolicyA P (frameAt word).sheetShift (H j) (H (j + 1))) :
    ∀ j, 1 ≤ j → j < N → 1 ≤ sheetPsi word (H j) := by
  refine arc_ge_one (fun j => sheetPsi word (H j)) N ?_ ?_
  · show sheetPsi word (H 1) = 1
    rw [hH1]
    exact PsiCalibration.sheetPsi_H1_W0 word h hSE hW0
  · intro j hj hjN
    exact FLatticePaper.W1NonfreeHsq.psi_mono h hSE P (hret j hj hjN)

/-- **The arc in phase W1**: the points `refl (H j)`; `Ψ(refl H_1) = 1` and `Ψ(refl H_0) = Ψ(H_last) = 0`. -/
theorem psi_arc_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hW1 : (frameAt word).eps = 1) (H : ℕ → Site) (N : ℕ) (hH1 : H 1 = (2, 0))
    (hret : ∀ j, 1 ≤ j → j + 1 < N →
      sheetPolicyA P (frameAt word).sheetShift (reflH word (H j)) (reflH word (H (j + 1)))) :
    ∀ j, 1 ≤ j → j < N → 1 ≤ sheetPsi word (reflH word (H j)) := by
  refine arc_ge_one (fun j => sheetPsi word (reflH word (H j))) N ?_ ?_
  · show sheetPsi word (reflH word (H 1)) = 1
    rw [hH1]
    have e : reflH word (2, 0) = ((frameAt word).child.den - 1, (frameAt word).child.num - 1) := by
      unfold reflH
      ext <;> simp
      ring
    rw [e]
    exact PsiCalibration.sheetPsi_hMinus2_W1 word h hSE hW1
  · intro j hj hjN
    exact FLatticePaper.W1NonfreeHsq.psi_mono h hSE P (hret j hj hjN)

/-- **The bottom bound in phase W0.** Given the arc enumeration (`H j` with `H 0 = (1,0)`, `H 1 = (2,0)`, covering the free H trace), the
retained arc edges, and the H-price identities `P = c₀ − E_H`, `E_H = 1 + min(0,Ψ−1)`, the price is at most `c₀` on the free H trace. -/
theorem bottom_W0 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hW0 : (frameAt word).eps = -1) (H : ℕ → Site) (N : ℕ) (hN : 2 ≤ N) (hH0 : H 0 = (1, 0)) (hH1 : H 1 = (2, 0))
    (hret : ∀ j, 1 ≤ j → j + 1 < N → sheetPolicyA P (frameAt word).sheetShift (H j) (H (j + 1)))
    (hmem : ∀ j, j < N → H j ∈ (frameAt word).freeH)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j, j < N ∧ z = H j)
    (EHv : Site → ℤ)
    (hP : ∀ z ∈ (frameAt word).freeH, (frameAt word).price (standardField word) z = (frameAt word).cutPrice - EHv z)
    (hEH : ∀ z ∈ (frameAt word).freeH, EHv z = 1 + min 0 (sheetPsi word z - 1)) :
    ∀ z ∈ (frameAt word).freeH, (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice := by
  have hh0 : (1, 0) ∈ (frameAt word).freeH := by
    rw [← hH0]
    exact hmem 0 (by omega)
  have hΨ : ∀ z ∈ (frameAt word).freeH, z ≠ (1, 0) → 1 ≤ sheetPsi word z := by
    intro z hz hne
    obtain ⟨j, hjN, rfl⟩ := hcover z hz
    rcases Nat.eq_zero_or_pos j with hj0 | hpos
    · subst hj0
      exact absurd hH0 hne
    · exact psi_arc_W0 h hSE P hW0 H N hH1 hret j hpos hjN
  have hΨnn : ∀ z ∈ (frameAt word).freeH, 0 ≤ sheetPsi word z := by
    intro z hz
    by_cases hz0 : z = (1, 0)
    · subst hz0
      rw [PsiCalibration.sheetPsi_H0_W0 word h hSE hW0]
    · have := hΨ z hz hz0
      omega
  exact fun z hz => PriceDeck.hH_of_phaseW0 (frameAt word) (standardField word) EHv (sheetPsi word) (1, 0) hh0 hP hEH
    (PsiCalibration.sheetPsi_H0_W0 word h hSE hW0) hΨ hΨnn z hz

/-- **The bottom bound in phase W1**: the same with the reflection `refl`, `refl(1,0) = H_last`, `Ψ(H_last) = 0`, and the H-price identities
`P = c₀ − 1 − E_H(refl z)`, `E_H(refl z) = min(0, Ψ(refl z) − 1)`. -/
theorem bottom_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hW1 : (frameAt word).eps = 1) (H : ℕ → Site) (N : ℕ) (hN : 2 ≤ N) (hH0 : H 0 = (1, 0)) (hH1 : H 1 = (2, 0))
    (hret : ∀ j, 1 ≤ j → j + 1 < N →
      sheetPolicyA P (frameAt word).sheetShift (reflH word (H j)) (reflH word (H (j + 1))))
    (hmem : ∀ j, j < N → H j ∈ (frameAt word).freeH)
    (hcover : ∀ z ∈ (frameAt word).freeH, ∃ j, j < N ∧ z = H j)
    (EHv : Site → ℤ)
    (hP : ∀ z ∈ (frameAt word).freeH,
      (frameAt word).price (standardField word) z = (frameAt word).cutPrice - 1 - EHv (reflH word z))
    (hEH : ∀ z ∈ (frameAt word).freeH, EHv (reflH word z) = min 0 (sheetPsi word (reflH word z) - 1)) :
    ∀ z ∈ (frameAt word).freeH, (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice := by
  have hh0 : (1, 0) ∈ (frameAt word).freeH := by
    rw [← hH0]
    exact hmem 0 (by omega)
  have hrefl0 : reflH word (1, 0) = ((frameAt word).child.den, (frameAt word).child.num - 1) := by
    unfold reflH
    ext <;> simp
  have hΨ0 : sheetPsi word (reflH word (1, 0)) = 0 := by
    rw [hrefl0]
    exact PsiCalibration.sheetPsi_hLast_W1 word h hSE hW1
  have hΨ : ∀ z ∈ (frameAt word).freeH, z ≠ (1, 0) → 1 ≤ sheetPsi word (reflH word z) := by
    intro z hz hne
    obtain ⟨j, hjN, rfl⟩ := hcover z hz
    rcases Nat.eq_zero_or_pos j with hj0 | hpos
    · subst hj0
      exact absurd hH0 hne
    · exact psi_arc_W1 h hSE P hW1 H N hH1 hret j hpos hjN
  have hΨnn : ∀ z ∈ (frameAt word).freeH, 0 ≤ sheetPsi word (reflH word z) := by
    intro z hz
    by_cases hz0 : z = (1, 0)
    · subst hz0
      rw [hΨ0]
    · have := hΨ z hz hz0
      omega
  exact fun z hz => PriceDeck.hH_of_phaseW1 (frameAt word) (standardField word) EHv (sheetPsi word) (reflH word)
    (1, 0) hh0 hP hEH hΨ0 hΨ hΨnn z hz

end FLatticePaper.ArcPsi
