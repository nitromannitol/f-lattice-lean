import Mathlib.Tactic

/-! # The square step of the Q15 pointer argument (pure combinatorics)

At a root `z` of a unit square with corners `z, q0, q1, q2` (`Sq w` means `w` is one of the four corners), let `R` be the retention
relation of the reflected policy and `ρ` the reflection of the square. The square clause says that some corner of the reflected
square keeps no input inside it. If the root keeps its rejected input `q0` and every other corner keeps an input inside the square,
the clause is violated; so the root does not keep `q0`. -/

namespace FLatticePaper.TieSquare

/-- **The square step.** Let `Sq` be the four corners of a unit square with root `z`, and let `R' w i` be the reflected retention
(`R' w i` says the reflected policy keeps `i` at `w`). If the square clause holds (some corner keeps no input in the square) and every
corner other than `z` keeps an input in the square, then the root does not keep its rejected input `q0`. -/
theorem square_out {Site : Type} (Sq : Site → Prop) (R' : Site → Site → Prop) (z q0 : Site)
    (hSq : Sq z) (hq0 : Sq q0)
    (hclause : ∃ w, Sq w ∧ ∀ i, Sq i → ¬ R' w i)
    (hcorner : ∀ w, Sq w → w ≠ z → ∃ i, Sq i ∧ R' w i) :
    ¬ R' z q0 := by
  intro h
  obtain ⟨w, hw, hno⟩ := hclause
  by_cases hwz : w = z
  · subst hwz
    exact hno q0 hq0 h
  · obtain ⟨i, hi, hRi⟩ := hcorner w hw hwz
    exact hno i hi hRi

end FLatticePaper.TieSquare
