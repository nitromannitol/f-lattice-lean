import FLatticePaper.Plane.Induction.FreeRows

/-! # The boundary price on the native H arc (task 68, Q13's insertion): the arithmetic of `E_H`

With `a_p = (N, −D)`, `B = D² + 2DN − N²`, `r = D + N` and `c_p = −(B + r)/2`, the boundary input is `E_H(w) = F(w + V_p) − a_p·w − c_p`
on the native H arc. The sheet offers and the transverse increment give, with the earlier H-source theorem (`Ψ = 0` at the initial vertex
for phase W0, at the final vertex for phase W1, and `Ψ ≥ 1` at every other arc vertex):

* `E_H(w) = 1 − W + min(0, Ψ(w) − 1)` on the arc (`W` the phase bit);
* phase W0: `P(z) = c₀ − E_H(z)`; phase W1: `P(z) = c₀ − 1 − E_H(w)` with `w` the reflection of `z`.

This file proves the arithmetic: `P(H_0) = c₀`, `P(H_j) = c₀ − 1` for `j > 0`, and `P ≤ c₀` on the arc, in both phases. The sheet-offer identity,
the `Ψ` values, the phase formulas and the reflection are named inputs. The other boundary sides (the top by zero drift, the native V at `c₀`,
the right V at `c₀ − 1`) are not here: `hbd` of `priceRange_of_conjugate` needs all four traces. -/

namespace FLatticePaper.PriceH

open FLatticePaper

/-- `a_p = (N, −D)`. -/
def aP (D N : ℤ) : Site := (N, -D)

/-- `B = D² + 2DN − N²`. -/
def BP (D N : ℤ) : ℤ := D ^ 2 + 2 * D * N - N ^ 2

/-- `c_p = −(B + r)/2` with `r = D + N`. -/
def cP (D N : ℤ) : ℤ := -((BP D N + (D + N)) / 2)

/-- The boundary input `E_H(w) = F(w + V_p) − a_p·w − c_p` on the native H arc. -/
def EH (F : Site → ℤ) (Vp : Site) (D N : ℤ) (w : Site) : ℤ :=
  F (w + Vp) - ((aP D N).1 * w.1 + (aP D N).2 * w.2) - cP D N

/-- **Phase W0 on the native H arc.** With `P = c₀ − E_H` and `E_H = 1 + min(0, Ψ − 1)`, where `Ψ = 0` at the initial vertex `h₀` and
`Ψ ≥ 1` at every other arc vertex: `P(h₀) = c₀`, `P(z) = c₀ − 1` on the rest of the arc, and `P ≤ c₀` on the arc. -/
theorem price_arc_W0 (P EHv Ψ : Site → ℤ) (c0 : ℤ) (arc : Set Site) (h0 : Site) (hh0 : h0 ∈ arc)
    (hP : ∀ z ∈ arc, P z = c0 - EHv z)
    (hEH : ∀ z ∈ arc, EHv z = 1 + min 0 (Ψ z - 1))
    (hΨ0 : Ψ h0 = 0) (hΨ : ∀ z ∈ arc, z ≠ h0 → 1 ≤ Ψ z) (hΨnn : ∀ z ∈ arc, 0 ≤ Ψ z) :
    P h0 = c0 ∧ (∀ z ∈ arc, z ≠ h0 → P z = c0 - 1) ∧ ∀ z ∈ arc, P z ≤ c0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hP h0 hh0
    have h2 := hEH h0 hh0
    rw [hΨ0] at h2
    rw [h1, h2]
    omega
  · intro z hz hzh
    have h1 := hP z hz
    have h2 := hEH z hz
    have h3 := hΨ z hz hzh
    rw [h1, h2]
    have : min 0 (Ψ z - 1) = 0 := by omega
    rw [this]
    ring
  · intro z hz
    have h1 := hP z hz
    have h2 := hEH z hz
    have h3 := hΨnn z hz
    rw [h1, h2]
    omega

/-- **Phase W1 on the native H arc.** With `P(z) = c₀ − 1 − E_H(w)` at the reflection `w = refl z`, and the arc identity `E_H = min(0, Ψ − 1)`
at the reflected points (the phase bit `W = 1`), where `Ψ = 0` at `refl h₀` and `Ψ ≥ 1` at the other reflected arc vertices: the same three
conclusions as phase W0. -/
theorem price_arc_W1 (P EHv Ψ refl : Site → ℤ) (c0 : ℤ) (arc : Set Site) (h0 : Site) (hh0 : h0 ∈ arc)
    (hP : ∀ z ∈ arc, P z = c0 - 1 - EHv (refl z))
    (hEH : ∀ z ∈ arc, EHv (refl z) = min 0 (Ψ (refl z) - 1))
    (hΨ0 : Ψ (refl h0) = 0) (hΨ : ∀ z ∈ arc, z ≠ h0 → 1 ≤ Ψ (refl z)) (hΨnn : ∀ z ∈ arc, 0 ≤ Ψ (refl z)) :
    P h0 = c0 ∧ (∀ z ∈ arc, z ≠ h0 → P z = c0 - 1) ∧ ∀ z ∈ arc, P z ≤ c0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hP h0 hh0
    have h2 := hEH h0 hh0
    rw [hΨ0] at h2
    rw [h1, h2]
    omega
  · intro z hz hzh
    have h1 := hP z hz
    have h2 := hEH z hz
    have h3 := hΨ z hz hzh
    rw [h1, h2]
    have : min 0 (Ψ (refl z) - 1) = 0 := by omega
    rw [this]
    ring
  · intro z hz
    have h1 := hP z hz
    have h2 := hEH z hz
    have h3 := hΨnn z hz
    rw [h1, h2]
    omega

end FLatticePaper.PriceH
