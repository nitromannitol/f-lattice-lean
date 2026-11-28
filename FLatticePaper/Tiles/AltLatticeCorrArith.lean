import FLatticePaper.Tiles.AltLatticeEvenV

/-! # Item (b) of `lemma:weak_alternate_odometer_properties` at the corrected even child (after a `3`): arithmetic

At a word `u 3` the parents are `p₁ = p_u`, `q₁ = 2 p_u + q_u`, so `d_{q₁} > 2 d_{p₁}`. Two copies of `T(p₁)` and a copy of `T(p₁)`
next to one of `T(q₁)` that meet along `v_{q₀,2}` at the other types are then too far apart in the coordinate `s`. -/

namespace FLatticePaper.Tiles.AltLatticeCorrArith

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteInduction (InH)

/-- The parents of `u 3`: `2 d_{p₁} < d_{q₁}`, `2 n_{p₁} ≤ n_{q₁}`, and `q₁ - 2 p₁ = q_u`, with `d_{q_u} ≥ n_{q_u} + 2` or
`q_u = 1/1`. -/
theorem type_three_rel (u : Word) :
    2 * (parentsAt (u ++ [Digit.three])).odd.den < (parentsAt (u ++ [Digit.three])).even.den ∧
      2 * (parentsAt (u ++ [Digit.three])).odd.num ≤ (parentsAt (u ++ [Digit.three])).even.num ∧
      ((parentsAt (u ++ [Digit.three])).even.num - 2 * (parentsAt (u ++ [Digit.three])).odd.num + 2 ≤
          (parentsAt (u ++ [Digit.three])).even.den - 2 * (parentsAt (u ++ [Digit.three])).odd.den ∨
        ((parentsAt (u ++ [Digit.three])).even.num - 2 * (parentsAt (u ++ [Digit.three])).odd.num = 1 ∧
          (parentsAt (u ++ [Digit.three])).even.den - 2 * (parentsAt (u ++ [Digit.three])).odd.den = 1)) := by
  have hv := parentsAt_valid u
  have h1 := hv.odd_bounds
  have h2 := hv.even_bounds
  have hpe := hv.even_parity
  unfold Fraction.InUnitInterval at h1 h2
  unfold Fraction.Even at hpe
  have hdet := H3Data.eps_det (u ++ [Digit.three])
  rw [(HorizontalStep.par_three u).1, (HorizontalStep.par_three u).2] at hdet ⊢
  simp only [Parents.current, Parents.combine] at hdet ⊢
  generalize (parentsAt u).odd.num = n1 at *
  generalize (parentsAt u).odd.den = d1 at *
  generalize (parentsAt u).even.num = nr at *
  generalize (parentsAt u).even.den = dr at *
  have he : n1 * dr - nr * d1 = 1 ∨ n1 * dr - nr * d1 = -1 := by
    split_ifs at hdet
    · left; linarith
    · right; linarith
  refine ⟨by omega, by omega, ?_⟩
  rcases lt_or_eq_of_le h2.2.2 with hlt | heq
  · left; omega
  · right
    subst heq
    have hd : 0 < d1 - n1 := by
      rcases he with he | he <;> nlinarith
    constructor <;> rcases he with he | he <;> nlinarith

theorem pos1_0 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (0)) - (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) - 2 + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (0))) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos2_0 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < 2 * (1 - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2)) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (0) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * (2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (0)) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos1_1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (d2 - n2)) - (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) - 2 + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (d1 - n1))) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos2_1 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < 2 * (1 - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2)) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (d1 - n1) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * (2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (d2 - n2)) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos1_2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (3 * n2 - d2)) - (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) - 2 + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (d1 - n1))) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos2_2 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < 2 * (1 - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2)) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (d1 - n1) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * (2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (3 * n2 - d2)) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos1_3 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (d2 - n2)) - (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) - 2 + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (3 * n1 - d1))) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos2_3 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < 2 * (1 - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2)) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (3 * n1 - d1) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * (2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (d2 - n2)) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos1_4 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (3 * n2 - d2)) - (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) - 2 + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (3 * n1 - d1))) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

theorem pos2_4 (n1 d1 n2 d2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1)) :
    0 < 2 * (1 - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2)) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * (3 * n1 - d1) - (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * (2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (3 * n2 - d2)) := by
  rcases t3 with t3 | ⟨t3a, t3b⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain ⟨f, rfl⟩ : ∃ f : ℕ, n2 = 2 * (1 + (a : ℤ)) + (f : ℤ) := ⟨(n2 - 2 - 2 * a).toNat, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g : ℕ, d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + (f : ℤ) + 2 + 2 * (g : ℤ) :=
      ⟨((d2 - 2 * (2 + a + b) - f - 2) / 2).toNat, by omega⟩
    ring_nf; positivity
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, n1 = 1 + (a : ℤ) := ⟨(n1 - 1).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, d1 = 1 + (a : ℤ) + 1 + (b : ℤ) := ⟨(d1 - 2 - a).toNat, by omega⟩
    obtain rfl : n2 = 2 * (1 + (a : ℤ)) + 1 := by omega
    obtain rfl : d2 = 2 * (1 + (a : ℤ) + 1 + (b : ℤ)) + 1 := by omega
    ring_nf; positivity

set_option maxHeartbeats 400000 in
/-- **`W₁` odd**: no `z` with `z ∈ H_p` and `z + v_{q,2} - v_{q,1} ∈ H_q` at type three. -/
theorem mix3_odd (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1))
    (he : n1 * d2 - n2 * d1 = 1) (hmp : SiteInduction.muOf ⟨n1, d1⟩ = 2)
    (hp : InH ⟨n1, d1⟩ (z1, z2)) (hq : InH ⟨n2, d2⟩ ((z1, z2) + ((n2 - d2) - d2, (n2 + d2) - n2))) : False := by
  have pd : ((((n2 - d2) - d2, (n2 + d2) - n2) : Site).1 + (((n2 - d2) - d2, (n2 + d2) - n2) : Site).2) % 2 = 0 := by
    show ((n2 - d2) - d2 + ((n2 + d2) - n2)) % 2 = 0; omega
  unfold InH at hp hq
  rw [AltLatticeOddW.decide_par_add _ _ pd] at hq
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  rw [hmp] at p4
  simp only [SiteInduction.tCo, SiteInduction.sCo, SiteInduction.tOf, Prod.fst_add, Prod.snd_add] at p1 p2 p3 p4 q1 q2 q3 q4
  have hTp : 0 ≤ (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) := by nlinarith
  have hM : 0 ≤ (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) := by nlinarith
  have iden : (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 + n2) * z1 + (d2 - n2) * z2) =
      -2 * (n1 * d2 - n2 * d1) * (n1 * z1 - d1 * z2) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * ((d1 + n1) * z1 + (d1 - n1) * z2) := by ring
  rw [he] at iden
  rcases Bool.eq_false_or_eq_true (decide ((z1 + z2) % 2 = 0)) with hb | hb <;> rw [hb] at p1 p2 p3 p4 q1 q2 q3 q4 <;>
    simp only [SiteInduction.aOf, SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at p1 p2 p3 p4 q1 q2 q3 q4
  · -- even parity
    have ha : 1 ≤ min (2 * n1) (d1 - n1) := le_min (by omega) (by omega)
    have c1 := mul_le_mul_of_nonneg_left (show (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (0) ≤ (d2 + n2) * z1 + (d2 - n2) * z2 by linarith) hTp
    have c2 := mul_le_mul_of_nonneg_left (show (d1 + n1) * z1 + (d1 - n1) * z2 ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (0) by linarith) hM
    linarith [pos1_0 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, ha]
  · -- odd parity
    rcases le_total (d1 - n1) (3 * n1 - d1) with hl | hl
    · rw [min_eq_left hl] at p3 p4
      rcases le_total (d2 - n2) (3 * n2 - d2) with hm | hm
      · rw [min_eq_left hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (d2 - n2) ≤ (d2 + n2) * z1 + (d2 - n2) * z2 by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show (d1 + n1) * z1 + (d1 - n1) * z2 ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (d1 - n1) by linarith) hM
        linarith [pos1_1 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
      · rw [min_eq_right hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (3 * n2 - d2) ≤ (d2 + n2) * z1 + (d2 - n2) * z2 by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show (d1 + n1) * z1 + (d1 - n1) * z2 ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (d1 - n1) by linarith) hM
        linarith [pos1_2 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
    · rw [min_eq_right hl] at p3 p4
      rcases le_total (d2 - n2) (3 * n2 - d2) with hm | hm
      · rw [min_eq_left hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (d2 - n2) ≤ (d2 + n2) * z1 + (d2 - n2) * z2 by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show (d1 + n1) * z1 + (d1 - n1) * z2 ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (3 * n1 - d1) by linarith) hM
        linarith [pos1_3 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
      · rw [min_eq_right hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + (3 * n2 - d2) ≤ (d2 + n2) * z1 + (d2 - n2) * z2 by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show (d1 + n1) * z1 + (d1 - n1) * z2 ≤ 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + 2 * n1 - (3 * n1 - d1) by linarith) hM
        linarith [pos1_4 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]

set_option maxHeartbeats 400000 in
/-- **`W₁` even**: no `z` with `z ∈ H_p` and `z + v_{q,2} + 2 v_{q,1} - v_{p,1} ∈ H_q` at type three. -/
theorem mix3_even (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (hqe : (n2 + d2) % 2 = 0) (hpo : (n1 + d1) % 2 = 1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (t3 : n2 - 2 * n1 + 2 ≤ d2 - 2 * d1 ∨ (n2 - 2 * n1 = 1 ∧ d2 - 2 * d1 = 1))
    (he : n1 * d2 - n2 * d1 = -1) (hmq : SiteInduction.muOf ⟨n2, d2⟩ = 1)
    (hp : InH ⟨n1, d1⟩ (z1, z2)) (hq : InH ⟨n2, d2⟩ ((z1, z2) + ((n2 - d2) + 2 * d2 - 2 * d1, (n2 + d2) + 2 * n2 - 2 * n1))) : False := by
  have pd : ((((n2 - d2) + 2 * d2 - 2 * d1, (n2 + d2) + 2 * n2 - 2 * n1) : Site).1 + (((n2 - d2) + 2 * d2 - 2 * d1, (n2 + d2) + 2 * n2 - 2 * n1) : Site).2) % 2 = 0 := by
    show ((n2 - d2) + 2 * d2 - 2 * d1 + ((n2 + d2) + 2 * n2 - 2 * n1)) % 2 = 0; omega
  unfold InH at hp hq
  rw [AltLatticeOddW.decide_par_add _ _ pd] at hq
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  rw [hmq] at q4
  simp only [SiteInduction.tCo, SiteInduction.sCo, SiteInduction.tOf, Prod.fst_add, Prod.snd_add] at p1 p2 p3 p4 q1 q2 q3 q4
  have hTp : 0 ≤ (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) := by nlinarith
  have hM : 0 ≤ (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) := by nlinarith
  have iden : (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) * ((d2 + n2) * z1 + (d2 - n2) * z2) =
      -2 * (n1 * d2 - n2 * d1) * (n1 * z1 - d1 * z2) + (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) * ((d1 + n1) * z1 + (d1 - n1) * z2) := by ring
  rw [he] at iden
  rcases Bool.eq_false_or_eq_true (decide ((z1 + z2) % 2 = 0)) with hb | hb <;> rw [hb] at p1 p2 p3 p4 q1 q2 q3 q4 <;>
    simp only [SiteInduction.aOf, SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at p1 p2 p3 p4 q1 q2 q3 q4
  · -- even parity
    have ha : 1 ≤ min (2 * n1) (d1 - n1) := le_min (by omega) (by omega)
    have c1 := mul_le_mul_of_nonneg_left (show (d2 + n2) * z1 + (d2 - n2) * z2 ≤ 2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (0) by linarith) hTp
    have c2 := mul_le_mul_of_nonneg_left (show 0 ≤ (d1 + n1) * z1 + (d1 - n1) * z2 by linarith) hM
    linarith [pos2_0 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, ha]
  · -- odd parity
    rcases le_total (d1 - n1) (3 * n1 - d1) with hl | hl
    · rw [min_eq_left hl] at p3 p4
      rcases le_total (d2 - n2) (3 * n2 - d2) with hm | hm
      · rw [min_eq_left hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 + n2) * z1 + (d2 - n2) * z2 ≤ 2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (d2 - n2) by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show d1 - n1 ≤ (d1 + n1) * z1 + (d1 - n1) * z2 by linarith) hM
        linarith [pos2_1 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
      · rw [min_eq_right hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 + n2) * z1 + (d2 - n2) * z2 ≤ 2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (3 * n2 - d2) by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show d1 - n1 ≤ (d1 + n1) * z1 + (d1 - n1) * z2 by linarith) hM
        linarith [pos2_2 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
    · rw [min_eq_right hl] at p3 p4
      rcases le_total (d2 - n2) (3 * n2 - d2) with hm | hm
      · rw [min_eq_left hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 + n2) * z1 + (d2 - n2) * z2 ≤ 2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (d2 - n2) by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show 3 * n1 - d1 ≤ (d1 + n1) * z1 + (d1 - n1) * z2 by linarith) hM
        linarith [pos2_3 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]
      · rw [min_eq_right hm] at q3 q4
        have c1 := mul_le_mul_of_nonneg_left (show (d2 + n2) * z1 + (d2 - n2) * z2 ≤ 2 * (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) - (d2 ^ 2 + 2 * d2 * n2 - n2 ^ 2) + 2 * n2 - (3 * n2 - d2) by linarith) hTp
        have c2 := mul_le_mul_of_nonneg_left (show 3 * n1 - d1 ≤ (d1 + n1) * z1 + (d1 - n1) * z2 by linarith) hM
        linarith [pos2_4 n1 d1 n2 d2 h1 h2 hqe hpo t1 t2 t3, c1, c2, iden, p1, h1]

set_option maxHeartbeats 400000 in
/-- **Two copies of `T(p₁)` along `B + 2U` (`W₁` even)** cannot both contain a pair at type three: `s_p` moves by `2M > 2T_p + 2n₁ - 2l`. -/
theorem pp3_plus (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (hmp : SiteInduction.muOf ⟨n1, d1⟩ = 2) (hp : InH ⟨n1, d1⟩ (z1, z2)) (hq : InH ⟨n1, d1⟩ ((z1, z2) + (n1 - d1 + 2 * d2, n1 + d1 + 2 * n2))) :
    False := by
  have pd : ((n1 - d1 + 2 * d2, n1 + d1 + 2 * n2) : Site).1 + ((n1 - d1 + 2 * d2, n1 + d1 + 2 * n2) : Site).2 = 2 * (n1 + (d2 + n2)) := by
    show n1 - d1 + 2 * d2 + (n1 + d1 + 2 * n2) = _; ring
  have pd' : (((n1 - d1 + 2 * d2, n1 + d1 + 2 * n2) : Site).1 + ((n1 - d1 + 2 * d2, n1 + d1 + 2 * n2) : Site).2) % 2 = 0 := by rw [pd]; omega
  unfold InH at hp hq
  rw [AltLatticeOddW.decide_par_add _ _ pd'] at hq
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  rw [hmp] at p4 q4
  simp only [SiteInduction.sCo, SiteInduction.tOf, Prod.fst_add, Prod.snd_add] at p3 p4 q3 q4
  have hM : 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + d1 + n1 ≤ (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ d2 - 2 * d1 - 1) (by linarith : (0 : ℤ) ≤ d1 + n1),
      mul_nonneg (by linarith : (0 : ℤ) ≤ n2 - 2 * n1) (by linarith : (0 : ℤ) ≤ d1 - n1)]
  rcases Bool.eq_false_or_eq_true (decide ((z1 + z2) % 2 = 0)) with hb | hb <;> rw [hb] at p3 p4 q3 q4 <;>
    simp only [SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at p3 p4 q3 q4
  · nlinarith
  · have hl : -d1 ≤ min (d1 - n1) (3 * n1 - d1) := le_min (by linarith) (by linarith)
    nlinarith

set_option maxHeartbeats 400000 in
/-- **Two copies of `T(p₁)` along `B - 2U` (`W₁` odd)** cannot both contain a pair at type three: `s_p` moves by `2M > 2T_p + 2n₁ - 2l`. -/
theorem pp3_minus (n1 d1 n2 d2 z1 z2 : ℤ) (h1 : 0 < n1) (h2 : n1 < d1) (t1 : 2 * d1 < d2) (t2 : 2 * n1 ≤ n2)
    (hmp : SiteInduction.muOf ⟨n1, d1⟩ = 2) (hp : InH ⟨n1, d1⟩ (z1, z2)) (hq : InH ⟨n1, d1⟩ ((z1, z2) + (n1 - d1 - 2 * d2, n1 + d1 - 2 * n2))) :
    False := by
  have pd : ((n1 - d1 - 2 * d2, n1 + d1 - 2 * n2) : Site).1 + ((n1 - d1 - 2 * d2, n1 + d1 - 2 * n2) : Site).2 = 2 * (n1 - (d2 + n2)) := by
    show n1 - d1 - 2 * d2 + (n1 + d1 - 2 * n2) = _; ring
  have pd' : (((n1 - d1 - 2 * d2, n1 + d1 - 2 * n2) : Site).1 + ((n1 - d1 - 2 * d2, n1 + d1 - 2 * n2) : Site).2) % 2 = 0 := by rw [pd]; omega
  unfold InH at hp hq
  rw [AltLatticeOddW.decide_par_add _ _ pd'] at hq
  obtain ⟨p1, p2, p3, p4⟩ := hp
  obtain ⟨q1, q2, q3, q4⟩ := hq
  rw [hmp] at p4 q4
  simp only [SiteInduction.sCo, SiteInduction.tOf, Prod.fst_add, Prod.snd_add] at p3 p4 q3 q4
  have hM : 2 * (d1 ^ 2 + 2 * d1 * n1 - n1 ^ 2) + d1 + n1 ≤ (d1 * d2 + d1 * n2 + d2 * n1 - n1 * n2) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ d2 - 2 * d1 - 1) (by linarith : (0 : ℤ) ≤ d1 + n1),
      mul_nonneg (by linarith : (0 : ℤ) ≤ n2 - 2 * n1) (by linarith : (0 : ℤ) ≤ d1 - n1)]
  rcases Bool.eq_false_or_eq_true (decide ((z1 + z2) % 2 = 0)) with hb | hb <;> rw [hb] at p3 p4 q3 q4 <;>
    simp only [SiteInduction.lOf, if_true, if_false, Bool.false_eq_true] at p3 p4 q3 q4
  · nlinarith
  · have hl : -d1 ≤ min (d1 - n1) (3 * n1 - d1) := le_min (by linarith) (by linarith)
    nlinarith

end FLatticePaper.Tiles.AltLatticeCorrArith
