import FLatticePaper.Plane.BellmanRank
import FLatticePaper.Plane.Induction.FreeRows

/-! # Deck covariance of the fort (the removal rows are translated by `U`)

If `F` is `U`-periodic and translation by `U` preserves parity, then `incomingNeg` and `incomingPos` commute with the translation by `U`,
the laplacian is `U`-invariant, and the translate `{z | z − U ∈ S}` of an incoming fort `S` is an incoming fort. This lets the fan of a row
entry `H_i − U` run from `H_i` in the translated fort: an exit `w` of that fan lies in the translate, so `w − U ∈ S` (an earlier entry). -/

namespace FLatticePaper.RowCovariance

open FLatticePaper

theorem incomingNeg_add_U {U z : Site} (h : EvenSite (z + U) ↔ EvenSite z) :
    incomingNeg (z + U) = incomingNeg z + U := by
  unfold incomingNeg
  by_cases hz : EvenSite z
  · rw [if_pos hz, if_pos (h.mpr hz)]
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · rw [if_neg hz, if_neg (fun h' => hz (h.mp h'))]
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

theorem incomingPos_add_U {U z : Site} (h : EvenSite (z + U) ↔ EvenSite z) :
    incomingPos (z + U) = incomingPos z + U := by
  unfold incomingPos
  by_cases hz : EvenSite z
  · rw [if_pos hz, if_pos (h.mpr hz)]
    exact Prod.ext (by simp only [Prod.fst_add]; omega) (by simp only [Prod.snd_add])
  · rw [if_neg hz, if_neg (fun h' => hz (h.mp h'))]
    exact Prod.ext (by simp only [Prod.fst_add]) (by simp only [Prod.snd_add]; omega)

/-- **Deck covariance of an incoming fort.** If `F (z + U) = F z` for all `z` and translation by `U` preserves parity, the translate
`{z | z − U ∈ S}` of an incoming fort `S` is an incoming fort. -/
theorem isIncomingFort_translate (F : Field) (S : Set Site) (U : Site) (hU : ∀ z, F (z + U) = F z)
    (hpar : ∀ z, EvenSite (z + U) ↔ EvenSite z) (hS : IsIncomingFort F S) :
    IsIncomingFort F {z | z - U ∈ S} := by
  intro site hsite
  have hs : site - U ∈ S := hsite
  have hnU : incomingNeg site = incomingNeg (site - U) + U := by
    have := incomingNeg_add_U (U := U) (z := site - U) (hpar (site - U))
    rwa [sub_add_cancel] at this
  have hpU : incomingPos site = incomingPos (site - U) + U := by
    have := incomingPos_add_U (U := U) (z := site - U) (hpar (site - U))
    rwa [sub_add_cancel] at this
  have hn : incomingNeg site - U = incomingNeg (site - U) := by
    rw [hnU, add_sub_cancel_right]
  have hp : incomingPos site - U = incomingPos (site - U) := by
    rw [hpU, add_sub_cancel_right]
  have hFsite : F site = F (site - U) := by
    have := hU (site - U)
    rwa [sub_add_cancel] at this
  have hFn : F (incomingNeg site) = F (incomingNeg (site - U)) := by
    rw [hnU, hU]
  have hFp : F (incomingPos site) = F (incomingPos (site - U)) := by
    rw [hpU, hU]
  have hlap : laplacian F site = laplacian F (site - U) := by
    unfold laplacian
    rw [hFn, hFp, hFsite]
  rcases hS (site - U) hs with ⟨hl, hin⟩ | ⟨hl, h1, h2⟩
  · refine Or.inl ⟨hlap.trans hl, ?_⟩
    rcases hin with h | h
    · exact Or.inl (show incomingNeg site - U ∈ S by rw [hn]; exact h)
    · exact Or.inr (show incomingPos site - U ∈ S by rw [hp]; exact h)
  · refine Or.inr ⟨hlap.trans hl, ?_, ?_⟩
    · exact show incomingNeg site - U ∈ S by rw [hn]; exact h1
    · exact show incomingPos site - U ∈ S by rw [hp]; exact h2

end FLatticePaper.RowCovariance
