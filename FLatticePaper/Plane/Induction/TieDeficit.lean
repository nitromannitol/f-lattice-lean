import Mathlib.Tactic
import FLatticePaper.Graph

/-! # Deficits at a tie of the sheet minimum (Q15 deficit sums, Q16 one-edge retention)

For sheet fields `A`, `C` on the sites and `M = min(A, C)` (pointwise), the deficit of `A` over `M` on the two inputs of a
site `c` with `M c = A c` is `ΔA − ΔM` (`laplacian`). At a white tie with both parents white the deficits vanish, so both inputs
are ties (`tie_inputs`). At a black minimum with a white `A`, the other input has `Ψ = C − A = −1` (`other_gap`), so the
`A` policy, which keeps `Ψ` nondecreasing on its retained edges, cannot keep it, and retains the target (`one_edge_retained`). -/

namespace FLatticePaper.TieDeficit

open FLatticePaper

/-- The pointwise minimum of two sheet fields. -/
def minF (A C : Site → ℤ) : Site → ℤ := fun z => min (A z) (C z)

/-- The deficit identity: with `M c = A c`, the sum of the deficits of `A` over `M` on the two inputs is `ΔA − ΔM`. -/
theorem deficit_sum (A M : Site → ℤ) (c : Site) (hMc : M c = A c) :
    (A (incomingNeg c) - M (incomingNeg c)) + (A (incomingPos c) - M (incomingPos c)) =
      laplacian A c - laplacian M c := by
  unfold laplacian
  linarith

/-- Two nonnegative integers with zero sum are zero. -/
theorem zero_of_nonneg_sum (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 ∧ b = 0 := by
  constructor <;> linarith

/-- **Q15, deficit sums at a white tie.** If `A` and `C` are white at `c` (`ΔA = ΔC = 0`), the sheet minimum is white at `c`
(`ΔM = 0`), and `A c = C c`, then both inputs of `c` are ties: `A = C` there. -/
theorem tie_inputs (A C : Site → ℤ) (c : Site) (hA : laplacian A c = 0) (hC : laplacian C c = 0)
    (hM : laplacian (minF A C) c = 0) (htie : C c = A c) :
    A (incomingNeg c) = C (incomingNeg c) ∧ A (incomingPos c) = C (incomingPos c) := by
  have hMA : minF A C c = A c := by unfold minF; rw [htie, min_self]
  have hMC : minF A C c = C c := by unfold minF; rw [htie, min_self]
  have dA := deficit_sum A (minF A C) c hMA
  have dC := deficit_sum C (minF A C) c hMC
  rw [hA, hM] at dA
  rw [hC, hM] at dC
  have nA1 : 0 ≤ A (incomingNeg c) - minF A C (incomingNeg c) := by
    unfold minF; have := min_le_left (A (incomingNeg c)) (C (incomingNeg c)); linarith
  have nA2 : 0 ≤ A (incomingPos c) - minF A C (incomingPos c) := by
    unfold minF; have := min_le_left (A (incomingPos c)) (C (incomingPos c)); linarith
  have nC1 : 0 ≤ C (incomingNeg c) - minF A C (incomingNeg c) := by
    unfold minF; have := min_le_right (A (incomingNeg c)) (C (incomingNeg c)); linarith
  have nC2 : 0 ≤ C (incomingPos c) - minF A C (incomingPos c) := by
    unfold minF; have := min_le_right (A (incomingPos c)) (C (incomingPos c)); linarith
  obtain ⟨a1, a2⟩ := zero_of_nonneg_sum _ _ nA1 nA2 (by linarith)
  obtain ⟨c1, c2⟩ := zero_of_nonneg_sum _ _ nC1 nC2 (by linarith)
  constructor <;> linarith

/-- **Q16, the other input of a black minimum.** If `M = min(A, C)` is black at `c` (`ΔM = −1`), `A` is white at `c`, `A c = C c`,
and the input `i` is an `A`-contact (`M i = A i`), then the other input `j` has `Ψ j = C j − A j = −1`. -/
theorem other_gap (A C : Site → ℤ) (c : Site) (hA : laplacian A c = 0) (hM : laplacian (minF A C) c = -1)
    (htie : C c = A c) (i j : Site) (hij : (i = incomingNeg c ∧ j = incomingPos c) ∨
      (i = incomingPos c ∧ j = incomingNeg c)) (hMi : minF A C i = A i) :
    C j - A j = -1 := by
  have hMA : minF A C c = A c := by unfold minF; rw [htie, min_self]
  have dA := deficit_sum A (minF A C) c hMA
  rw [hA, hM] at dA
  have hsumj : (A j - minF A C j) = 1 := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hi0 : A (incomingNeg c) - minF A C (incomingNeg c) = 0 := by rw [hMi]; ring
      linarith
    · have hi0 : A (incomingPos c) - minF A C (incomingPos c) = 0 := by rw [hMi]; ring
      linarith
  unfold minF at hsumj
  omega


/-- **Q16, the one-edge retention in the `C` orientation.** Let `c` be a tie (`C c = A c`) with `M = min(A, C)` black at `c`, and
let the `C` policy `QC` satisfy the quota at `c` (black keeps both inputs, white keeps one) and the monotonicity
`QC c j → C j − A j ≤ C c − A c`. If `z` is an input of `c` with `M z = C z`, then `QC c z`. -/
theorem one_edge_C (A C : Site → ℤ) (QC : Site → Site → Prop) (c z : Site)
    (hquotaB : laplacian C c = -1 → QC c (incomingNeg c) ∧ QC c (incomingPos c))
    (hquotaW : laplacian C c = 0 → QC c (incomingNeg c) ∨ QC c (incomingPos c))
    (hmono : ∀ j, QC c j → C j - A j ≤ C c - A c)
    (hbin : laplacian C c = -1 ∨ laplacian C c = 0)
    (hM : laplacian (minF A C) c = -1) (htie : C c = A c)
    (hz : z = incomingNeg c ∨ z = incomingPos c) (hMz : minF A C z = C z) :
    QC c z := by
  have hMC : minF A C c = C c := by unfold minF; rw [htie, min_self]
  have dC := deficit_sum C (minF A C) c hMC
  rw [hM] at dC
  rcases hbin with hb | hb
  · obtain ⟨h1, h2⟩ := hquotaB hb
    rcases hz with rfl | rfl
    · exact h1
    · exact h2
  · rw [hb] at dC
    rcases hz with rfl | rfl
    · -- `z = incomingNeg c`: the other input `incomingPos c` has `Ψ = 1`
      have hother : ¬ QC c (incomingPos c) := by
        intro hQ
        have hz0 : C (incomingNeg c) - minF A C (incomingNeg c) = 0 := by rw [hMz]; ring
        have hgap : minF A C (incomingPos c) = C (incomingPos c) - 1 := by linarith
        have hm := hmono _ hQ
        unfold minF at hgap
        omega
      rcases hquotaW hb with h | h
      · exact h
      · exact absurd h hother
    · -- `z = incomingPos c`: the other input `incomingNeg c` has `Ψ = 1`
      have hother : ¬ QC c (incomingNeg c) := by
        intro hQ
        have hz0 : C (incomingPos c) - minF A C (incomingPos c) = 0 := by rw [hMz]; ring
        have hgap : minF A C (incomingNeg c) = C (incomingNeg c) - 1 := by linarith
        have hm := hmono _ hQ
        unfold minF at hgap
        omega
      rcases hquotaW hb with h | h
      · exact absurd h hother
      · exact h

end FLatticePaper.TieDeficit
