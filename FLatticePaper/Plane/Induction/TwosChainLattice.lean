import FLatticePaper.Plane.Induction.TwosChainMono
import FLatticePaper.Plane.Induction.TwosPriceMono
import FLatticePaper.Plane.Induction.TwosSlipLattice

/-! The chain potential of sign `+1` along the period lattice: `Φ(z + iU + jV) = Φ(z) − i + 2j`, with the kernel
`U = (2k+5, 2k+3)` and the transverse `V = (−2, 4k+8)`. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

theorem twosChain_lattice (k : ℕ) (x y i j : ℤ) :
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1
      (x + (i * (2 * (k : ℤ) + 5) + j * (-2)), y + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) =
    (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1
      (x, y) - i + 2 * j := by
  rw [chainP_eq, chainP_eq]
  have hS : twosSlip k (x + (i * (2 * (k : ℤ) + 5) + j * (-2)), y + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8))) =
      twosSlip k (x, y) + 2 * j := twosSlip_lattice k (x, y) i j
  have hP : twosP k (x + (i * (2 * (k : ℤ) + 5) + j * (-2)) + 1,
      y + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) + 1) = twosP k (x + 1, y + 1) - i := by
    have e : (x + (i * (2 * (k : ℤ) + 5) + j * (-2)) + 1,
        y + (i * (2 * (k : ℤ) + 3) + j * (4 * (k : ℤ) + 8)) + 1) =
        ((x + 1 + i * (2 * (k : ℤ) + 5)) + j * (-2), (y + 1 + i * (2 * (k : ℤ) + 3)) + j * (4 * (k : ℤ) + 8)) :=
      Prod.ext (by ring) (by ring)
    rw [e, twosP_V_int k j, twosP_U_int k i]
  dsimp only
  rw [hS, hP]
  ring

end FLatticePaper.TwosEPolicy
