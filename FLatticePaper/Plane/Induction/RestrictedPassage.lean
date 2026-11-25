import FLatticePaper.Plane.Induction.AuxRankQ1
import FLatticePaper.Plane.Induction.RankFromForts

/-! # hno step 1: the restricted passage stays in the fort, along inputs where K does not increase

For a restricted fort `S` for `permitsQ1` (`IsRestrictedFort`), every site `z ∈ S` has an input `u ∈ S` such that `K u ≤ K z`, under
the monotonicity of `K = P + J_η` on the passage edges (Q1 para 9 and 13):
* black sites (`laplacian = −1`): both inputs are permitted, and `K` does not increase to either input (numerically 17624/17624);
* free white sites (`freeClosure`): the prescribed input `FreePresc` is the only permitted input, and `K` does not increase to it
  (numerically 956/956 on free V white sites);
* nonfree white sites: both inputs are in `S`, and only the unit-forced input is monotone (numerically 13768/13768 on the forced
  edges; both inputs are not monotone in general).

The three monotonicity facts are named inputs (Part I's lower-contact transfer for `P` and `J_η`, Q1 para 13). The statement below
packages the restricted clauses of `IsRestrictedFort` with them. -/

namespace FLatticePaper.RestrictedPassage

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1

/-- **The restricted successor.** In a restricted fort for `permitsQ1`, every site has an input in the fort along which `K` does
not increase, given the named monotonicity inputs on black sites, free white sites and nonfree white sites. -/
theorem restricted_successor {frame : ChildFrame} {F : Field} {η : ℤ} {S : Set Site}
    (hS : IsRestrictedFort F (permitsQ1 frame F η) S) (K : Site → ℤ)
    (hBlack : ∀ z u : Site, laplacian F z = -1 → Edge u z → K u ≤ K z)
    (hFree : ∀ z : Site, laplacian F z = 0 → FreeClosure.freeClosure frame z →
      ∃ p : Site, Edge p z ∧ FreePolicy.FreePresc frame η z p ∧ K p ≤ K z)
    (hNonfree : ∀ z : Site, laplacian F z = 0 → ¬ FreeClosure.freeClosure frame z → ∃ u : Site, Edge u z ∧ K u ≤ K z)
    (z : Site) (hz : z ∈ S) :
    ∃ u ∈ S, Edge u z ∧ K u ≤ K z := by
  rcases hS z hz with ⟨hlap, hA⟩ | ⟨hlap, hA, hB⟩
  · -- black: both inputs are permitted, so an input in the fort exists, and it is monotone
    have hpN : permitsQ1 frame F η z (incomingNeg z) := Or.inl ⟨hlap, Or.inl rfl⟩
    have hpP : permitsQ1 frame F η z (incomingPos z) := Or.inl ⟨hlap, Or.inr rfl⟩
    rcases hA with (h1 | h1) | (h1 | h1)
    · exact ⟨incomingNeg z, h1, Or.inl rfl, hBlack _ _ hlap (Or.inl rfl)⟩
    · exact absurd hpN h1
    · exact ⟨incomingPos z, h1, Or.inr rfl, hBlack _ _ hlap (Or.inr rfl)⟩
    · exact absurd hpP h1
  · -- a white site: a permitted input lies in the fort
    have hin : ∀ i : Site, Edge i z → permitsQ1 frame F η z i → i ∈ S := by
      intro i hi hp
      rcases (show i = incomingNeg z ∨ i = incomingPos z from hi) with h | h
      · subst h
        rcases hA with h1 | h1
        · exact h1
        · exact absurd hp h1
      · subst h
        rcases hB with h1 | h1
        · exact h1
        · exact absurd hp h1
    by_cases hfc : FreeClosure.freeClosure frame z
    · -- a free white: the prescribed input is permitted, hence in the fort, and monotone
      obtain ⟨p, hpE, hpr, hpK⟩ := hFree z hlap hfc
      exact ⟨p, hin p hpE (Or.inr ⟨hlap, Or.inl ⟨hfc, hpr⟩⟩), hpE, hpK⟩
    · -- a nonfree white: both inputs are permitted, hence in the fort; the unit-forced input is monotone
      obtain ⟨u, hu, hK⟩ := hNonfree z hlap hfc
      exact ⟨u, hin u hu (Or.inr ⟨hlap, Or.inr ⟨hfc, hu⟩⟩), hu, hK⟩

/-- One K-nonincreasing step inside the fort: from `z` to an input `u ∈ S` with `K u ≤ K z`. -/
def KStep (S : Set Site) (K : Site → ℤ) (z u : Site) : Prop :=
  u ∈ S ∧ Edge u z ∧ K u ≤ K z

/-- A passage from `r` to `e` along `KStep` never raises `K`: `K e ≤ K r`. -/
theorem K_le_of_reach {S : Set Site} {K : Site → ℤ} {r e : Site}
    (h : Relation.ReflTransGen (KStep S K) r e) : K e ≤ K r := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans hbc.2.2 ih

/-- **hmin from a passage (hno step 3, the Q1 minimum argument).** If `K r` is minimal over the fort `S` and the row entry `e` is
reached from `r` by a `K`-nonincreasing passage inside `S`, then `e` is `K`-minimal over `S`. This is the `hmin` input of
`FreeRows.free_row_empty_inS`. -/
theorem hmin_of_reach {S : Set Site} {K : Site → ℤ} {r : Site} (hrmin : ∀ w ∈ S, K r ≤ K w)
    {e : Site} (he : Relation.ReflTransGen (KStep S K) r e) : ∀ w ∈ S, K e ≤ K w :=
  fun w hw => le_trans (K_le_of_reach he) (hrmin w hw)

end FLatticePaper.RestrictedPassage
