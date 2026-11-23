import FLatticePaper.Plane.Induction.TwoRank

/-! Task 72 / Q20: the minimum admission of the two-rank argument (`TWO_RANK_RAW_PHI_AUDIT.md`, "Exact hypotheses and minimum
admission"). For binary fields `F`, `g` and an integer `k`, the minimum `m = min(F, g + k)` has Laplacian `0` or `−1` at each centre,
given the local quota and monotonicity of `D = F − g`: a black `F` centre has `D` nonincreasing at both inputs, a black `g` centre has
`D` nondecreasing at both inputs. The arithmetic core is `min_lap_local`; the field statement is `laplacian_min_local`. -/

namespace FLatticePaper.MinAdmission

open FLatticePaper

/-- The arithmetic core: six binary values at a centre `c` and its inputs `a`, `b`, with the quotas and the monotonicity of `D`. -/
theorem min_lap_local (fa fc fb ga gc gb k : ℤ)
    (hfa : fa = 0 ∨ fa = 1) (hfb : fb = 0 ∨ fb = 1)
    (hga : ga = 0 ∨ ga = 1) (hgb : gb = 0 ∨ gb = 1)
    (hlF : fa + fb - 2 * fc = -1 ∨ fa + fb - 2 * fc = 0)
    (hlG : ga + gb - 2 * gc = -1 ∨ ga + gb - 2 * gc = 0)
    (hFb : fa + fb - 2 * fc = -1 → fa - ga ≤ fc - gc ∧ fb - gb ≤ fc - gc)
    (hGb : ga + gb - 2 * gc = -1 → fc - gc ≤ fa - ga ∧ fc - gc ≤ fb - gb) :
    min fa (ga + k) + min fb (gb + k) - 2 * min fc (gc + k) = -1 ∨
      min fa (ga + k) + min fb (gb + k) - 2 * min fc (gc + k) = 0 := by
  omega

/-- **The minimum admission, pointwise.** For binary fields `F`, `G` and an integer `k`, the Laplacian of `min(F, G + k)` at `c` is `0` or
`−1`, given the quotas of `F` and `G` at `c` and the monotonicity of `D = F − G` at the inputs of `c`. -/
theorem laplacian_min_local (F G : Site → ℤ) (k : ℤ) (c : Site)
    (hF : ∀ x, F x = 0 ∨ F x = 1) (hG : ∀ x, G x = 0 ∨ G x = 1)
    (hlF : laplacian F c = -1 ∨ laplacian F c = 0) (hlG : laplacian G c = -1 ∨ laplacian G c = 0)
    (hFb : laplacian F c = -1 → F (incomingNeg c) - G (incomingNeg c) ≤ F c - G c ∧
      F (incomingPos c) - G (incomingPos c) ≤ F c - G c)
    (hGb : laplacian G c = -1 → F c - G c ≤ F (incomingNeg c) - G (incomingNeg c) ∧
      F c - G c ≤ F (incomingPos c) - G (incomingPos c)) :
    laplacian (fun x => min (F x) (G x + k)) c = -1 ∨ laplacian (fun x => min (F x) (G x + k)) c = 0 := by
  have hlF' : F (incomingNeg c) + F (incomingPos c) - 2 * F c = -1 ∨
      F (incomingNeg c) + F (incomingPos c) - 2 * F c = 0 := by
    unfold laplacian at hlF; omega
  have hlG' : G (incomingNeg c) + G (incomingPos c) - 2 * G c = -1 ∨
      G (incomingNeg c) + G (incomingPos c) - 2 * G c = 0 := by
    unfold laplacian at hlG; omega
  have hFb' : F (incomingNeg c) + F (incomingPos c) - 2 * F c = -1 →
      F (incomingNeg c) - G (incomingNeg c) ≤ F c - G c ∧ F (incomingPos c) - G (incomingPos c) ≤ F c - G c := by
    intro h'
    have h1 : laplacian F c = -1 := by unfold laplacian; omega
    obtain ⟨h2, h3⟩ := hFb h1
    exact ⟨h2, h3⟩
  have hGb' : G (incomingNeg c) + G (incomingPos c) - 2 * G c = -1 →
      F c - G c ≤ F (incomingNeg c) - G (incomingNeg c) ∧ F c - G c ≤ F (incomingPos c) - G (incomingPos c) := by
    intro h'
    have h1 : laplacian G c = -1 := by unfold laplacian; omega
    obtain ⟨h2, h3⟩ := hGb h1
    exact ⟨h2, h3⟩
  have h := min_lap_local (F (incomingNeg c)) (F c) (F (incomingPos c)) (G (incomingNeg c)) (G c) (G (incomingPos c)) k
    (hF _) (hF _) (hG _) (hG _) hlF' hlG' hFb' hGb'
  unfold laplacian
  dsimp only
  omega

end FLatticePaper.MinAdmission
