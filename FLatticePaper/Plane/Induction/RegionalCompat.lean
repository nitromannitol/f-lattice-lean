import FLatticePaper.Plane.Induction.W1Constructor
import FLatticePaper.Plane.Induction.AndOrRank
import FLatticePaper.Plane.Induction.FanCompat

/-! # Regional compatibility of forced edges (Q32 he1, the source §A)

A region `S` with a relation `C` (the region's chosen arrows) and a rank `r` strictly decreasing along `C`:
black sites of `S` keep both inputs, white sites of `S` keep some input, and every `C`-target inside the strict interior `R`
lies in `S`. Then a forced edge out of a white site of `S`, derived by `ForcedEdgeIn` inside `R`, is a `C`-arrow.

Proof: suppose the forced output `o` is not the `C`-target `u` of the centre `c`. Then `u` is the in-square input of `c`.
Let `T` be the square corners lying in `S`. Each member of `T` has a `C`-successor in `T` of strictly smaller rank (the induction
hypothesis at whites, the black rule at blacks), contradicting a minimum of `r` on `T`. -/

namespace FLatticePaper.RegionalCompat

open FLatticePaper FLatticePaper.W1 FLatticePaper.AndOrRank FLatticePaper.FanCompat

theorem regional_forced {F : Field} {R S : Site → Prop} {C : Site → Site → Prop} {r : Site → ℤ}
    (hr : ∀ x u, C x u → r u < r x)
    (hS : ∀ x u, S x → C x u → R u → S u)
    (hblack : ∀ x, S x → laplacian F x = -1 → ∀ u, (u = incomingNeg x ∨ u = incomingPos x) → C x u)
    (hwhite : ∀ x, S x → laplacian F x = 0 → ∃ u, C x u ∧ (u = incomingNeg x ∨ u = incomingPos x))
    {x o : Site} (h : ForcedEdgeIn F R (fun _ _ => False) x o) : S x → C x o := by
  induction h with
  | seed hs => exact fun _ => (hs : False).elim
  | @unit a b c o' inside hR hc hw ho hout hin hforced ih =>
    intro hx
    classical
    by_contra hne
    obtain ⟨u, hCu, hu⟩ := hwhite c hx hw
    have hsq := square_one_input a b hc
    have hor : incomingNeg c ∈ squareCorners a b ∨ incomingPos c ∈ squareCorners a b := by
      by_cases h1 : incomingNeg c ∈ squareCorners a b
      · exact Or.inl h1
      · exact Or.inr (by
          by_contra h2
          exact h1 (hsq.mpr h2))
    have hne' : u ≠ o' := fun h' => hne (h' ▸ hCu)
    have huS : u ∈ squareCorners a b := by
      by_contra hnot
      rcases hu with hu | hu <;> rcases ho with ho | ho
      · exact hne' (hu.trans ho.symm)
      · subst hu
        subst ho
        exact hnot (hor.resolve_right hout)
      · subst hu
        subst ho
        exact hnot (hor.resolve_left hout)
      · exact hne' (hu.trans ho.symm)
    set T := (squareCorners a b).filter (fun c' => S c') with hT
    have hcT : c ∈ T := Finset.mem_filter.mpr ⟨hc, hx⟩
    have key : ∀ c' ∈ T, ∃ i ∈ T, r i < r c' := by
      intro c' hc'T
      obtain ⟨hc', hS'⟩ := Finset.mem_filter.mp hc'T
      by_cases hcc : c' = c
      · subst hcc
        refine ⟨u, Finset.mem_filter.mpr ⟨huS, hS c' u hx hCu (hR u huS)⟩, hr c' u hCu⟩
      · rcases hin c' hc' hcc with hb | ⟨hw', hin', hinp⟩
        · obtain ⟨i, hi, hiin⟩ := square_corner_input a b hc'
          have hCi : C c' i := hblack c' hS' hb i hiin
          exact ⟨i, Finset.mem_filter.mpr ⟨hi, hS c' i hS' hCi (hR i hi)⟩, hr c' i hCi⟩
        · have hCi : C c' (inside c') := ih c' hc' hcc hw' hS'
          exact ⟨inside c', Finset.mem_filter.mpr ⟨hin', hS c' (inside c') hS' hCi (hR _ hin')⟩,
            hr c' (inside c') hCi⟩
    obtain ⟨m, hmT, hmin⟩ := Finset.exists_min_image T r ⟨c, hcT⟩
    obtain ⟨i, hiT, hri⟩ := key m hmT
    have := hmin i hiT
    linarith

end FLatticePaper.RegionalCompat
