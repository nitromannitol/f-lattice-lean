import FLatticePaper.Plane.PeriodCocycle
import FLatticePaper.Construction.StaircaseExtension
import FLatticePaper.Construction.AlternateLadderExtension

/-! Task 36 (hbaseTwoId), step 1: the midpoint of the twos base field, in lattice coordinates, has the generator periods of
the explicit ladder alternate.

For `d` even, with `S0` a field with generator periods `(0, cV0)` for `1/d`, the function
`twoH d S0 w = ceil((S0(w + (2,0)) + S0(w + (d,-d)) + dcorr d w) / 2) - w2` has generator periods `(-1, cV0 + 1 - d)`.
(The kernel constant `-1` and transverse constant `cV0 + 1 - d = ladderOddAltConstantV d` are the ones of the explicit
alternate; `twoH` agrees with it on the alternate tile, numerically checked in scripts/twos_uniqueness_check.py.) -/

namespace FLatticePaper.Induction.TwosBaseIdentity

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction

/-- The ceiling of `x / 2`. -/
def halfCeil (x : ℤ) : ℤ := -((-x) / 2)

/-- The affine correction of the twos midpoint in lattice coordinates. -/
def dcorr (d : ℤ) (w : Site) : ℤ := w.1 + (1 - d) * w.2 + d * (d + 1) / 2 - d - 1

/-- The midpoint of `S0` in lattice coordinates. -/
def twoH (d : ℤ) (S0 : Site → ℤ) (w : Site) : ℤ :=
  halfCeil (S0 (w.1 + 2, w.2) + S0 (w.1 + d, w.2 - d) + dcorr d w) - w.2

theorem halfCeil_add_two_mul (x m : ℤ) : halfCeil (x + 2 * m) = halfCeil x + m := by
  unfold halfCeil
  omega

theorem kernel_even (d : ℤ) (hd : d % 2 = 0) : (Fraction.mk 1 d).modifiedDeck.kernel = (2 * d, 2) := by
  have h : (1 + d) % 2 ≠ 0 := by omega
  simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, h]

theorem transverse_eq (d : ℤ) : (Fraction.mk 1 d).modifiedDeck.transverse = (1 - d, 1 + d) := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

theorem transverseGrade_eq (d : ℤ) (p : Site) : (Fraction.mk 1 d).transverseGrade p = d * p.2 - p.1 := by
  simp [Fraction.transverseGrade]

theorem twoH_periods (d : ℤ) (hd : d % 2 = 0) (S0 : Site → ℤ) {cV0 : ℤ}
    (hS0 : HasGeneratorPeriods (Fraction.mk 1 d) S0 0 cV0) :
    HasGeneratorPeriods (Fraction.mk 1 d) (twoH d S0) (-1) (cV0 + 1 - d) := by
  obtain ⟨hK, hV⟩ := hS0
  rw [kernel_even d hd] at hK
  simp only [transverse_eq d, transverseGrade_eq] at hV
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [kernel_even d hd]
    have ka : ∀ p : Site, S0 (p + (2 * d, 2)) = S0 p := fun p => by
      have h := hK p
      rwa [add_zero] at h
    have e1 : S0 ((w + (2 * d, 2)).1 + 2, (w + (2 * d, 2)).2) = S0 (w.1 + 2, w.2) := by
      rw [← ka (w.1 + 2, w.2)]
      exact congrArg S0 (Prod.ext (by simp; try ring)
        (by simp; try ring))
    have e2 : S0 ((w + (2 * d, 2)).1 + d, (w + (2 * d, 2)).2 - d) = S0 (w.1 + d, w.2 - d) := by
      rw [← ka (w.1 + d, w.2 - d)]
      exact congrArg S0 (Prod.ext (by simp; try ring)
        (by simp; try ring))
    have hdc : dcorr d (w + (2 * d, 2)) = dcorr d w + 2 := by
      unfold dcorr
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    have hsnd : (w + (2 * d, 2)).2 = w.2 + 2 := by simp
    unfold twoH
    rw [e1, e2, hdc, hsnd]
    have hX : S0 (w.1 + 2, w.2) + S0 (w.1 + d, w.2 - d) + (dcorr d w + 2) =
        (S0 (w.1 + 2, w.2) + S0 (w.1 + d, w.2 - d) + dcorr d w) + 2 * 1 := by ring
    rw [hX, halfCeil_add_two_mul]
    ring
  · rw [transverse_eq d, transverseGrade_eq]
    have h1 := hV (w.1 + 2, w.2)
    have h2 := hV (w.1 + d, w.2 - d)
    simp only at h1 h2
    have e3 : S0 ((w + (1 - d, 1 + d)).1 + 2, (w + (1 - d, 1 + d)).2) =
        S0 (w.1 + 2, w.2) - (d * w.2 - (w.1 + 2)) + cV0 := by
      rw [← h1]
      exact congrArg S0 (Prod.ext (by simp; try ring)
        (by simp; try ring))
    have e4 : S0 ((w + (1 - d, 1 + d)).1 + d, (w + (1 - d, 1 + d)).2 - d) =
        S0 (w.1 + d, w.2 - d) - (d * (w.2 - d) - (w.1 + d)) + cV0 := by
      rw [← h2]
      exact congrArg S0 (Prod.ext (by simp; try ring)
        (by simp; try ring))
    have hdc : dcorr d (w + (1 - d, 1 + d)) = dcorr d w + (2 - d - d ^ 2) := by
      unfold dcorr
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    unfold twoH
    rw [e3, e4, hdc]
    have hsnd : (w + (1 - d, 1 + d)).2 = w.2 + (1 + d) := by simp
    rw [hsnd]
    have hX : S0 (w.1 + 2, w.2) - (d * w.2 - (w.1 + 2)) + cV0 +
        (S0 (w.1 + d, w.2 - d) - (d * (w.2 - d) - (w.1 + d)) + cV0) +
          (dcorr d w + (2 - d - d ^ 2)) =
        (S0 (w.1 + 2, w.2) + S0 (w.1 + d, w.2 - d) + dcorr d w) +
          2 * (-(d * w.2 - w.1) + 2 + cV0) := by ring
    rw [hX, halfCeil_add_two_mul]
    ring

end FLatticePaper.Induction.TwosBaseIdentity
