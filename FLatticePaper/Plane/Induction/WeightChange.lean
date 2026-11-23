import FLatticePaper.Graph
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Task 42: the weight change on a fixed graph (fix Q4-I3, "External facts").

A deck basis `U, V` with determinant `D ≠ 0` generates the lattice `L = {i U + j V}` (the deck). A relation `retained c i` lists
the retained inputs of a site. Suppose two deck-affine functions `P, J` (increments `(−1, 0)` and `(0, η)`) do not increase along
retained edges, and one old strict rank `r0` (increments `lam0 (−a0)`, `lam0 (c0 η)`) strictly decreases along them. Then for all
integers `a, c > 0` there is a rank with increments `lam (−a, c η)`, `lam > 0`, strictly decreasing along the retained edges.

Construction. The lift `w` (integer, with increments `(−a, c η)`) is `w z = ⌊(A z₁ + B z₂)/D⌋`. The walk value `M (w e − w z) + n` of a
retained walk of length `n` from `z` to `e`, with `M = lam0 (a0 + c0)`, is bounded: `n ≤ r0 z − r0 e` along a walk, so the value is at most
`g e − g z` with `g = M w − r0`; and `g` is bounded above on the sites `e` with `P e ≤ P z`, `J e ≤ J z`, by the monotonicity of `g`
along `U` and `V` (its increments have the right signs). The rank is `M w + R`, where `R z` is the supremum of the walk values from `z`. -/

namespace FLatticePaper.WeightChange

open FLatticePaper

/-- The deck point `i U + j V`. -/
def latPt (U V : Site) (i j : ℤ) : Site := (i * U.1 + j * V.1, i * U.2 + j * V.2)

/-- The determinant of the deck basis. -/
def detUV (U V : Site) : ℤ := U.1 * V.2 - U.2 * V.1

theorem latPt_zero (U V : Site) : latPt U V 0 0 = (0, 0) := by
  unfold latPt
  simp

theorem latPt_succ_fst (U V : Site) (n : ℤ) : latPt U V (n + 1) 0 = latPt U V n 0 + U := by
  unfold latPt
  ext <;> simp <;> ring

theorem latPt_succ_snd (U V : Site) (n : ℤ) : latPt U V 0 (n + 1) = latPt U V 0 n + V := by
  unfold latPt
  ext <;> simp <;> ring

theorem latPt_split (U V : Site) (i j : ℤ) : latPt U V i j = latPt U V i 0 + latPt U V 0 j := by
  unfold latPt
  ext <;> simp

/-- Adding the zero site does nothing. -/
theorem site_add_zero' (z : Site) : z + (0 : Site) = z := by
  ext <;> simp

/-- An affine sequence: `F (z + T n) = F z + n c` when `T` steps by `step` and `F` increases by `c` along `step`. -/
theorem affine_seq {F : Site → ℤ} {step : Site} {c : ℤ} (hstep : ∀ z, F (z + step) = F z + c)
    (T : ℤ → Site) (hT0 : T 0 = 0) (hTs : ∀ n, T (n + 1) = T n + step) (z : Site) (n : ℤ) :
    F (z + T n) = F z + n * c := by
  refine Int.induction_on n ?_ ?_ ?_
  · rw [hT0, site_add_zero', zero_mul, add_zero]
  · intro k ih
    have key : z + T ((k : ℤ) + 1) = (z + T k) + step := by
      rw [hTs]
      ext <;> simp <;> ring
    rw [key, hstep, ih]
    ring
  · intro k ih
    have h1 := hstep (z + T (-(k : ℤ) - 1))
    have h2 := hTs (-(k : ℤ) - 1)
    have e : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [e] at h2
    have h3 : z + T (-(k : ℤ)) = (z + T (-(k : ℤ) - 1)) + step := by
      rw [h2]
      ext <;> simp <;> ring
    have ih' : F (z + T (-(k : ℤ) - 1) + step) = F z + (-(k : ℤ)) * c := by
      rw [← h3]
      exact ih
    linear_combination ih' - h1

/-- A function with increments `p` along `U` and `q` along `V` has increment `i p + j q` along the deck point `i U + j V`. -/
theorem affine_lattice {F : Site → ℤ} {U V : Site} {p q : ℤ} (hU : ∀ z, F (z + U) = F z + p)
    (hV : ∀ z, F (z + V) = F z + q) (z : Site) (i j : ℤ) :
    F (z + latPt U V i j) = F z + i * p + j * q := by
  have hsplit' : z + latPt U V i j = (z + latPt U V i 0) + latPt U V 0 j := by
    rw [latPt_split]
    ext <;> simp <;> ring
  rw [hsplit']
  have hA : F (z + latPt U V i 0) = F z + i * p :=
    affine_seq hU (fun n => latPt U V n 0) (latPt_zero U V) (latPt_succ_fst U V) z i
  have hB : F (z + latPt U V i 0 + latPt U V 0 j) = F (z + latPt U V i 0) + j * q :=
    affine_seq hV (fun n => latPt U V 0 n) (latPt_zero U V) (latPt_succ_snd U V) (z + latPt U V i 0) j
  rw [hB, hA]

/-- The deck point of the determinant: `D x = i U + j V` with explicit integers. -/
theorem detUV_mul_lat (U V : Site) (x1 x2 : ℤ) :
    latPt U V (x1 * V.2 - x2 * V.1) (U.1 * x2 - U.2 * x1) = (detUV U V * x1, detUV U V * x2) := by
  unfold latPt detUV
  ext <;> simp <;> ring

end FLatticePaper.WeightChange
