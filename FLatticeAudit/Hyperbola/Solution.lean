import FLatticePaper.MainTheorems

/-!
# Solution: the hyperbola

Proves the statement of `FLatticeAudit/Hyperbola/Challenge.lean` from the repository's `hyperbola_of_odometersTheorem`.
-/

namespace FLatticeAudit

open FLatticePaper

theorem hyperbola :
    ∀ (h : OdometersTheorem) (t : ℝ), 0 ≤ t → t ≤ 1 →
      symmetricCircleMatrix t (1 - t) (-Real.sqrt (t ^ 2 + (1 - t) ^ 2)) ∈ frontier symmetricGrowthSet :=
  fun h t ht hu => hyperbola_of_odometersTheorem h t ht hu

end FLatticeAudit
