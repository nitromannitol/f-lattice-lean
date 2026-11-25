import FLatticePaper.Graph
import FLatticePaper.Plane.Induction.QuadraticCap
import FLatticePaper.Plane.Induction.ChildFrame

/-! The binary-centre step of the all-slope cap (ALL_SLOPE_STEP, the recursion `A_k ≥ 2A_(k−1) − 1 − B_(k−2)`).

A binary centre has laplacian `−1` or `0`, so `2F(c) ≤ F(incomingNeg c) + F(incomingPos c) + 1`: the centre is the ceiling of the mean of
its two inputs. At an even input `N` of an odd centre `c` (with `S = incomingNeg c` and `N = incomingPos c`), the eastern input `E` of `N`
bounds `F N` from above (`2F N ≤ F W + F E + 1` with the western input `W`, and `F W ≤ F E` by the same-sheet monotonicity). Hence
`F E ≥ F N ≥ 2F c − 1 − F S`. -/

namespace FLatticePaper.CapRecursion

open FLatticePaper

theorem incomingNeg_of_odd' (v : Site) (h : ¬ EvenSite v) : incomingNeg v = (v.1, v.2 - 1) := by
  unfold incomingNeg
  rw [if_neg h]

theorem incomingPos_of_odd' (v : Site) (h : ¬ EvenSite v) : incomingPos v = (v.1, v.2 + 1) := by
  unfold incomingPos
  rw [if_neg h]

theorem incomingNeg_of_even' (v : Site) (h : EvenSite v) : incomingNeg v = (v.1 - 1, v.2) := by
  unfold incomingNeg
  rw [if_pos h]

theorem incomingPos_of_even' (v : Site) (h : EvenSite v) : incomingPos v = (v.1 + 1, v.2) := by
  unfold incomingPos
  rw [if_pos h]

/-- A binary centre is the ceiling of the mean of its two inputs (one side of it). -/
theorem binary_upper (F : Field) {c : Site} (hl : laplacian F c = -1 ∨ laplacian F c = 0) :
    2 * F c ≤ F (incomingNeg c) + F (incomingPos c) + 1 := by
  unfold laplacian at hl
  omega

/-- **The odd-centre step.** `F E ≥ 2 F c − 1 − F S` for an odd centre `c` with south input `S` and even north input `N`, whose
western input `W` has no greater height than the eastern input `E`. -/
theorem odd_centre_step (F : Field) {c S N W E : Site} (hS : S = incomingNeg c) (hN : N = incomingPos c)
    (hW : W = incomingNeg N) (hE : E = incomingPos N)
    (hlc : laplacian F c = -1 ∨ laplacian F c = 0) (hlN : laplacian F N = -1 ∨ laplacian F N = 0)
    (hmono : F W ≤ F E) :
    2 * F c - 1 - F S ≤ F E := by
  have h1 := binary_upper F hlN
  have h2 := binary_upper F hlc
  rw [← hW, ← hE] at h1
  rw [← hS, ← hN] at h2
  have hNE : F N ≤ F E := by omega
  omega

/-- **The diagonal recursion.** Along the ray of odd centres `c_n = (p+n+1, q+n+1)` (with `p + q` odd) the recursion holds:
`2F(c_(n+1)) − 1 − F(south of c_(n+1)) ≤ F(c_(n+2))`, from the binary centres and the western monotonicity. -/
theorem diag_recursion (F : Field) (p q : ℤ) (hpq : (p + q) % 2 = 1)
    (hbin : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0)
    (n : ℤ) (hm : F (p + n, q + (n + 2)) ≤ F (p + (n + 2), q + (n + 2))) :
    2 * F (p + (n + 1), q + (n + 1)) - 1 - F (p + (n + 1), q + n) ≤ F (p + (n + 2), q + (n + 2)) := by
  have hc : ¬ EvenSite (p + (n + 1), q + (n + 1)) := by
    unfold EvenSite
    simp only
    omega
  have hS : (p + (n + 1), q + n) = incomingNeg (p + (n + 1), q + (n + 1)) := by
    rw [incomingNeg_of_odd' _ hc]
    exact Prod.ext rfl (by ring)
  have hN : (p + (n + 1), q + (n + 2)) = incomingPos (p + (n + 1), q + (n + 1)) := by
    rw [incomingPos_of_odd' _ hc]
    exact Prod.ext rfl (by ring)
  have hNe : EvenSite (p + (n + 1), q + (n + 2)) := by
    unfold EvenSite
    simp only
    omega
  have hW : (p + n, q + (n + 2)) = incomingNeg (p + (n + 1), q + (n + 2)) := by
    rw [incomingNeg_of_even' _ hNe]
    exact Prod.ext (by ring) rfl
  have hE : (p + (n + 2), q + (n + 2)) = incomingPos (p + (n + 1), q + (n + 2)) := by
    rw [incomingPos_of_even' _ hNe]
    exact Prod.ext (by ring) rfl
  exact odd_centre_step F hS hN hW hE (hbin _) (hbin _) hm

/-- The diagonal recursion in the index form of `QuadraticCap.cap_with_anchors`: `A k = F(p+k, q+k)`, `B j = F(p+j+1, q+j)`. -/
theorem diag_hrec (F : Field) (p q : ℤ) (hpq : (p + q) % 2 = 1)
    (hbin : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0) (J : ℕ)
    (hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2))) :
    ∀ k : ℕ, 2 ≤ k → k ≤ J + 2 →
      2 * F (p + ((k - 1 : ℕ) : ℤ), q + ((k - 1 : ℕ) : ℤ)) - 1 - F (p + ((k - 2 : ℕ) : ℤ) + 1, q + ((k - 2 : ℕ) : ℤ)) ≤
        F (p + (k : ℤ), q + (k : ℤ)) := by
  intro k hk hkJ
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
  have h1 : n + 2 - 1 = n + 1 := by omega
  have h2 : n + 2 - 2 = n := by omega
  rw [h1, h2]
  have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have e2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  rw [e1, e2]
  have key := diag_recursion F p q hpq hbin (n : ℤ) (hmono n (by omega))
  have hB : p + (n : ℤ) + 1 = p + ((n : ℤ) + 1) := by ring
  rw [hB]
  linarith [key]

/-- **The local cap on the diagonal ray** (ALL_SLOPE_STEP, the uniform quadratic cap): with the zero-strip bounds `A_0, A_1 ≥ 0`, the
even harmonic anchors `B_j ≤ m(j)` for `j ≤ J`, and the odd anchors `m(k) ≤ A_k` for `J + 2 < k ≤ K`, the ray satisfies `m(k) ≤ A_k`
for all `k ≤ K`. The recursion is `diag_hrec`; the strips and anchors are the named inputs. -/
theorem diag_cap (F : Field) (p q : ℤ) (hpq : (p + q) % 2 = 1)
    (hbin : ∀ x : Site, laplacian F x = -1 ∨ laplacian F x = 0)
    (J K : ℕ)
    (hmono : ∀ n : ℕ, n ≤ J → F (p + (n : ℤ), q + ((n : ℤ) + 2)) ≤ F (p + ((n : ℤ) + 2), q + ((n : ℤ) + 2)))
    (hA0 : 0 ≤ F (p, q)) (hA1 : 0 ≤ F (p + 1, q + 1))
    (hB : ∀ j : ℕ, j ≤ J → F (p + (j : ℤ) + 1, q + (j : ℤ)) ≤ FLatticePaper.QuadraticCap.capMin j)
    (hanchor : ∀ k : ℕ, J + 2 < k → k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ))) :
    ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ F (p + (k : ℤ), q + (k : ℤ)) := by
  have hA0' : 0 ≤ F (p + ((0 : ℕ) : ℤ), q + ((0 : ℕ) : ℤ)) := by simpa using hA0
  have hA1' : 0 ≤ F (p + ((1 : ℕ) : ℤ), q + ((1 : ℕ) : ℤ)) := by
    have : (p + ((1 : ℕ) : ℤ), q + ((1 : ℕ) : ℤ)) = (p + 1, q + 1) := by push_cast; rfl
    rw [this]
    exact hA1
  exact FLatticePaper.QuadraticCap.cap_with_anchors (fun k : ℕ => F (p + (k : ℤ), q + (k : ℤ)))
    (fun j : ℕ => F (p + (j : ℤ) + 1, q + (j : ℤ))) J K hA0' hA1' hB
    (fun k hk hkJ => diag_hrec F p q hpq hbin J hmono k hk hkJ) hanchor

/-- **The even harmonic anchor.** The harmonic grid at `(1−j, j−1)` is the parabola `m(j) = capMin j`: its parity term vanishes, and the
numerator is `−2j(j−1)`. This is the anchor value `h0 = m(j)` of ALL_SLOPE_STEP, with no hypothesis. -/
theorem harmonicGrid_anchor (j : ℤ) :
    FLatticePaper.Induction.harmonicGrid (1 - j, j - 1) = QuadraticCap.capMin j := by
  unfold FLatticePaper.Induction.harmonicGrid QuadraticCap.capMin
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self j
  have e : (1 - j) ^ 2 + 2 * (1 - j) * (j - 1) - (j - 1) ^ 2 - 2 * (j - 1) - ((1 - j) + (j - 1)) % 2 =
      -2 * (j * (j - 1)) := by
    have h0 : ((1 - j) + (j - 1)) % 2 = 0 := by omega
    rw [h0]
    ring
  rw [e, ht]
  omega

/-- **The odd harmonic anchor.** The harmonic grid at `(2−k, k−1)` (odd, parity term `1`) is `m(k) = capMin k`. -/
theorem harmonicGrid_anchor_odd (k : ℤ) :
    FLatticePaper.Induction.harmonicGrid (2 - k, k - 1) = QuadraticCap.capMin k := by
  unfold FLatticePaper.Induction.harmonicGrid QuadraticCap.capMin
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self k
  have e : (2 - k) ^ 2 + 2 * (2 - k) * (k - 1) - (k - 1) ^ 2 - 2 * (k - 1) - ((2 - k) + (k - 1)) % 2 =
      -2 * (k * (k - 1)) := by
    have h1 : ((2 - k) + (k - 1)) % 2 = 1 := by omega
    rw [h1]
    ring
  rw [e, ht]
  omega

end FLatticePaper.CapRecursion
