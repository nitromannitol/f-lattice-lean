import FLatticePaper.Plane.Induction.W1Constructor

/-! # Integrality of the grades on the child lattice

For a child `(n, d)` with `T = d² + 2dn − n²`, `L = d + n`, `c = d − n`, the grades of a site `z = (z₁, z₂)` are
`t = n z₁ − d z₂` and `s = L z₁ + c z₂`, and the inverse relations are `T z₁ = d s + c t` and `T z₂ = n s − L t` (ring identities).
A grade pair `(t, s)` comes from an integer site iff `T` divides both `d s + c t` and `n s − L t`; the quotients are the site. -/

namespace FLatticePaper.Lattice

/-- The two inverse identities of the grade map. -/
theorem inverse_identities (n d z1 z2 : ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) * z1 = d * ((d + n) * z1 + (d - n) * z2) + (d - n) * (n * z1 - d * z2) ∧
    (d ^ 2 + 2 * d * n - n ^ 2) * z2 = n * ((d + n) * z1 + (d - n) * z2) - (d + n) * (n * z1 - d * z2) := by
  constructor <;> ring

/-- **A lattice site has divisible grades**: `T` divides `d s + c t` and `n s − L t` (with the site as the quotients). -/
theorem dvd_of_site (n d z1 z2 : ℤ) :
    (d ^ 2 + 2 * d * n - n ^ 2) ∣ d * ((d + n) * z1 + (d - n) * z2) + (d - n) * (n * z1 - d * z2) ∧
    (d ^ 2 + 2 * d * n - n ^ 2) ∣ n * ((d + n) * z1 + (d - n) * z2) - (d + n) * (n * z1 - d * z2) := by
  obtain ⟨h1, h2⟩ := inverse_identities n d z1 z2
  exact ⟨⟨z1, h1.symm⟩, ⟨z2, h2.symm⟩⟩

/-- **Integrality characterisation.** A grade pair `(t, s)` with `T ≠ 0` and `T` dividing `d s + c t` and `n s − L t` is the grade
pair of an integer site, namely the quotients. -/
theorem site_of_dvd (n d t s : ℤ) (hT : d ^ 2 + 2 * d * n - n ^ 2 ≠ 0)
    (h1 : (d ^ 2 + 2 * d * n - n ^ 2) ∣ d * s + (d - n) * t)
    (h2 : (d ^ 2 + 2 * d * n - n ^ 2) ∣ n * s - (d + n) * t) :
    ∃ z : ℤ × ℤ, n * z.1 - d * z.2 = t ∧ (d + n) * z.1 + (d - n) * z.2 = s := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨(k1, k2), ?_, ?_⟩
  · apply mul_left_cancel₀ hT
    dsimp only
    linear_combination d * hk2 - n * hk1
  · apply mul_left_cancel₀ hT
    dsimp only
    linear_combination -(d + n) * hk1 - (d - n) * hk2

end FLatticePaper.Lattice
