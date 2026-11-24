import FLatticePaper.Plane.Induction.TwosSlipForm

/-! Task 118, the transverse and lattice steps of the twos slip `D(z) = F(z) − F(z + σ)` at `2^(k+1)`.

`D(z + V) = D(z) + 2` for the transverse period `V = (−2, 4k+8)` (`twosSlip_add_V`), and `D(z + U) = D(z)` for the
kernel (`twosSlip_add_U`, in `TwosSlipForm`). Along the lattice `D(a + iU + jV) = D(a) + 2j` (`twosSlip_lattice`). -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The transverse shift: `D(a + V) = D(a) + 2`, `V = (−2, 4k+8)`. -/
theorem twosSlip_add_V (k : ℕ) (a : Site) :
    twosSlip k (a + (-2, 4 * (k : ℤ) + 8)) = twosSlip k a + 2 := by
  have hP := twos_standardField_hasPeriods k
  have h1 := period_transverse_apply hP a
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at h1
  have h2 := period_transverse_apply hP (a + (frameAt (List.replicate (k + 1) Digit.two)).shortShift)
  rw [twos_transverse_explicit, twos_transverseGrade_explicit, ladderEvenConstantV_eq] at h2
  unfold twosSlip
  rw [show a + (-2, 4 * (k : ℤ) + 8) + (frameAt (List.replicate (k + 1) Digit.two)).shortShift =
      a + (frameAt (List.replicate (k + 1) Digit.two)).shortShift + (-2, 4 * (k : ℤ) + 8) by abel, h2, h1]
  rw [twos_shortShift_explicit]
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The kernel lattice shifts: `D(a + iU) = D(a)`. -/
theorem twosSlip_shiftU (k : ℕ) (i : ℤ) : ∀ a : Site,
    twosSlip k (a + (i * (2 * (k : ℤ) + 5), i * (2 * (k : ℤ) + 3))) = twosSlip k a := by
  induction i using Int.induction_on with
  | zero => intro a; simp only [zero_mul, Prod.mk_zero_zero, add_zero]
  | succ n ih =>
    intro a
    have e : a + (((n : ℤ) + 1) * (2 * (k : ℤ) + 5), ((n : ℤ) + 1) * (2 * (k : ℤ) + 3)) =
        (a + ((n : ℤ) * (2 * (k : ℤ) + 5), (n : ℤ) * (2 * (k : ℤ) + 3))) + (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [e, twosSlip_add_U, ih a]
  | pred n ih =>
    intro a
    have h := twosSlip_add_U k (a + ((-(n : ℤ) - 1) * (2 * (k : ℤ) + 5), (-(n : ℤ) - 1) * (2 * (k : ℤ) + 3)))
    have e : a + ((-(n : ℤ) - 1) * (2 * (k : ℤ) + 5), (-(n : ℤ) - 1) * (2 * (k : ℤ) + 3)) +
        (2 * (k : ℤ) + 5, 2 * (k : ℤ) + 3) = a + ((-(n : ℤ)) * (2 * (k : ℤ) + 5), (-(n : ℤ)) * (2 * (k : ℤ) + 3)) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [e, ih a] at h
    exact h.symm

/-- The transverse lattice shifts: `D(a + jV) = D(a) + 2j`. -/
theorem twosSlip_shiftV (k : ℕ) (j : ℤ) : ∀ a : Site,
    twosSlip k (a + (j * (-2), j * (4 * (k : ℤ) + 8))) = twosSlip k a + 2 * j := by
  induction j using Int.induction_on with
  | zero => intro a; simp only [zero_mul, mul_zero, Prod.mk_zero_zero, add_zero]
  | succ n ih =>
    intro a
    have e : a + (((n : ℤ) + 1) * (-2), ((n : ℤ) + 1) * (4 * (k : ℤ) + 8)) =
        (a + ((n : ℤ) * (-2), (n : ℤ) * (4 * (k : ℤ) + 8))) + (-2, 4 * (k : ℤ) + 8) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [e, twosSlip_add_V, ih a]
    ring
  | pred n ih =>
    intro a
    have h := twosSlip_add_V k (a + ((-(n : ℤ) - 1) * (-2), (-(n : ℤ) - 1) * (4 * (k : ℤ) + 8)))
    have e : a + ((-(n : ℤ) - 1) * (-2), (-(n : ℤ) - 1) * (4 * (k : ℤ) + 8)) + (-2, 4 * (k : ℤ) + 8) =
        a + ((-(n : ℤ)) * (-2), (-(n : ℤ)) * (4 * (k : ℤ) + 8)) :=
      Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
    rw [e, ih a] at h
    linarith

/-- The lattice law: `D(a + iU + jV) = D(a) + 2j`. -/
theorem twosSlip_lattice (k : ℕ) (a : Site) (i j : ℤ) :
    twosSlip k (a + (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) =
      twosSlip k a + 2 * j := by
  have e : a + (i * (2 * (k : ℤ) + 5) + j * (-2), i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) =
      (a + (j * (-2), j * (4 * (k : ℤ) + 8))) + (i * (2 * (k : ℤ) + 5), i * (2 * (k : ℤ) + 3)) :=
    Prod.ext (by simp only [Prod.fst_add]; ring) (by simp only [Prod.snd_add]; ring)
  rw [e, twosSlip_shiftU, twosSlip_shiftV]

end FLatticePaper.Induction
