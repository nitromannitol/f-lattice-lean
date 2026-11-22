import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.OddStep
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.WordInduction

/-! The increment law of the odd target along the conjugate lattice (task 49).

The odd output target is `Fp = quarterTurnField (standardField (conjWord w'))`, with `Fp(z) = F(Z z) + harmonicGrid z`,
`Z z = (-z_2, z_1 - 1)`. For a vector `p` with `p_1 + p_2` even, `harmonicGrid` has affine increments along `p`, and for a
generator `u = (-p_2, p_1)` of the period lattice of `F` (the conjugate packet's generator periods) the increment of `F`
along `u` is affine. Transport through `Z` gives the affine increment of `Fp` along `p`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem harmonicGrid_increment_affine (p : Site) (hp : (p.1 + p.2) % 2 = 0) :
    ∃ α β γ : ℤ, ∀ z : Site, harmonicGrid (z + p) - harmonicGrid z = α * z.1 + β * z.2 + γ := by
  obtain ⟨α, hα⟩ : ∃ α : ℤ, p.1 + p.2 = 2 * α := ⟨(p.1 + p.2) / 2, by omega⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, p.1 - p.2 = 2 * β := ⟨(p.1 - p.2) / 2, by omega⟩
  refine ⟨α, β, harmonicGrid p - harmonicGrid 0, fun z => ?_⟩
  have e1 := harmonicGrid_exact (z + p)
  have e2 := harmonicGrid_exact z
  have e3 := harmonicGrid_exact p
  have e0 := harmonicGrid_exact 0
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at e1 e0
  have hpar : (z.1 + p.1 + (z.2 + p.2)) % 2 = (z.1 + z.2) % 2 := by omega
  have key : 4 * (harmonicGrid (z + p) - harmonicGrid z - (α * z.1 + β * z.2 + (harmonicGrid p - harmonicGrid 0))) = 0 := by
    linear_combination e1 - e2 - e3 + e0 + 2 * z.1 * hα + 2 * z.2 * hβ - hpar + hp
  have h := (mul_eq_zero.mp key).resolve_left (by norm_num)
  linarith

theorem quarterTurnField_increment_affine (F : Field) (p : Site) (hp : (p.1 + p.2) % 2 = 0)
    (hF : ∃ a b c : ℤ, ∀ q : Site, F (q + (-p.2, p.1)) - F q = a * q.1 + b * q.2 + c) :
    ∃ α β γ : ℤ, ∀ z : Site,
      quarterTurnField F (z + p) - quarterTurnField F z = α * z.1 + β * z.2 + γ := by
  obtain ⟨a, b, c, hF'⟩ := hF
  obtain ⟨α, β, γ, hh⟩ := harmonicGrid_increment_affine p hp
  refine ⟨b + α, -a + β, -b + c + γ, fun z => ?_⟩
  have hZ : (-(z + p).2, (z + p).1 - 1) = (-z.2, z.1 - 1) + (-p.2, p.1) := by
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  unfold quarterTurnField
  simp only [quarterTurn_site]
  rw [hZ]
  have hq := hF' (-z.2, z.1 - 1)
  have hz := hh z
  linear_combination hq + hz

/-- A generator of the period lattice of a field with the period law, in the form used for the increment. -/
theorem generator_increment_affine (fr : Fraction) (F : Field) (cU cV : ℤ) (hper : HasGeneratorPeriods fr F cU cV)
    (p : Site) (hu : (-p.2, p.1) = fr.modifiedDeck.kernel ∨ (-p.2, p.1) = fr.modifiedDeck.transverse) :
    ∃ a b c : ℤ, ∀ q : Site, F (q + (-p.2, p.1)) - F q = a * q.1 + b * q.2 + c := by
  rcases hu with hu | hu
  · refine ⟨0, 0, cU, fun q => ?_⟩
    rw [hu, hper.1 q]
    ring
  · refine ⟨fr.num, -fr.den, cV, fun q => ?_⟩
    rw [hu, hper.2 q]
    unfold Fraction.transverseGrade
    ring

/-- The lattice vectors of a fraction are even in the sense needed: the dual vectors `(u_2, -u_1)` have even coordinate sum. -/
theorem kernel_dual_even (fr : Fraction) :
    ((fr.modifiedDeck.kernel.2, -fr.modifiedDeck.kernel.1).1 + (fr.modifiedDeck.kernel.2, -fr.modifiedDeck.kernel.1).2) % 2 = 0 := by
  unfold Fraction.modifiedDeck Fraction.periodMultiplicity
  dsimp only
  split_ifs <;> omega

theorem transverse_dual_even (fr : Fraction) :
    ((fr.modifiedDeck.transverse.2, -fr.modifiedDeck.transverse.1).1 +
      (fr.modifiedDeck.transverse.2, -fr.modifiedDeck.transverse.1).2) % 2 = 0 := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck
  dsimp only
  omega

/-- The odd target `Fp = quarterTurnField (standardField (conjWord w'))` has affine increments along the dual of each
generator of the conjugate child lattice, given the conjugate packet's generator periods. -/
theorem odd_target_increment_affine (word : Word)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word))) :
    (∃ a b c : ℤ, ∀ z : Site,
        quarterTurnField (standardField (conjWord word))
            (z + ((frameAt (conjWord word)).child.modifiedDeck.kernel.2,
              -(frameAt (conjWord word)).child.modifiedDeck.kernel.1)) -
          quarterTurnField (standardField (conjWord word)) z = a * z.1 + b * z.2 + c) ∧
    (∃ a b c : ℤ, ∀ z : Site,
        quarterTurnField (standardField (conjWord word))
            (z + ((frameAt (conjWord word)).child.modifiedDeck.transverse.2,
              -(frameAt (conjWord word)).child.modifiedDeck.transverse.1)) -
          quarterTurnField (standardField (conjWord word)) z = a * z.1 + b * z.2 + c) := by
  have hper := hG.periods
  constructor
  · apply quarterTurnField_increment_affine _ _ (kernel_dual_even _)
    apply generator_increment_affine _ _ _ _ hper
    left
    simp
  · apply quarterTurnField_increment_affine _ _ (transverse_dual_even _)
    apply generator_increment_affine _ _ _ _ hper
    right
    simp

end FLatticePaper.Induction
