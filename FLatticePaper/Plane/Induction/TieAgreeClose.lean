import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.W1MFinal
import FLatticePaper.Plane.Induction.FreeRoutes
import FLatticePaper.Plane.Induction.W1NonfreeHsqC
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.W1Pointers

/-! # `TieAgreeHyp` from the W1 route (Q15, the restricted form)

At an M-white tie `x` (`Ψ x = 0`, `ΔM x = 0`) the parent points `zTurn (x − lv)` (A) and `zTurn (centre − x − lv)` (C) are white in the
conjugate field. The free-root square `ParentSquareOut` at the A root comes from the W1 route (`FreeRoutes.hfree_assembled`), the
nonfree one from `parentSquare_nonfree` inside `hagree_M_tie_of_inherited`. The pointer equality `C retains the A pointer`
(`hagree_M_tie_of_inherited`) and the exact selection at white parent points (`white_policy` of the canonical game) give the iff:
both sides say "`y` is the A pointer". No input beyond the route facts of `hfree_assembled` is used. -/

namespace FLatticePaper.TieAgreeClose

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1Pointers
open FLatticePaper.W1HagreeNonfree FLatticePaper.W1SheetSquare

/-- `zTurn` is injective. -/
theorem zTurn_eq_iff (a b : Site) : zTurn a = zTurn b ↔ a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [zTurn, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · rintro ⟨h1, h2⟩
    omega

/-- **The A pointer is retained at a white A root.** The pointer `pointerOf (sheetQ Q lv) x` is an input of `x` that the policy retains
at the parent point `zTurn (x − lv)`, given that this point is white (quota). -/
theorem pointer_retained {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (P : OldPolicyData frame G seed η) (lv x : Site) (hlv : EvenSite lv) (hA : laplacian G (zTurn (x - lv)) = 0) :
    P.retained (zTurn (x - lv)) (zTurn (pointerOf (sheetQ P.retained lv) x - lv)) := by
  unfold pointerOf
  split_ifs with h
  · exact h
  · have hq := P.quota.2 (zTurn (x - lv)) hA
    have hnb := zTurn_neighbors x lv hlv
    unfold sheetQ at h
    by_cases hx : EvenSite x
    · obtain ⟨e1, e2⟩ := hnb.1 hx
      rw [e1] at h
      rw [e2]
      rcases hq with hq | hq
      · exact absurd hq h
      · exact hq
    · obtain ⟨o1, o2⟩ := hnb.2 hx
      rw [o1] at h
      rw [o2]
      rcases hq with hq | hq
      · exact hq
      · exact absurd hq h

/-- **The restricted `TieAgreeHyp` from the W1 route.** For the witness `P` of the canonical game `Gm` (with `P.retained` its policy)
and the route facts of `FreeRoutes.hfree_assembled`, the A and C policies agree on every input of an M-white tie. -/
theorem tieAgreeHyp_of_routes {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hs : seed = fun _ _ => False)
    (hW1 : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (Gm : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
    (hW : P.retained = (Gm.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (Rg : FreeRoutes.RouteGenuine (Gm.game (frameAt word).eps (frameAt word).eps_unit))
    (δ : ℤ) (hδη : (frameAt word).eps = -δ) (hδ : δ = 1 ∨ δ = -1)
    (hX3 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      (z.1, z.2 - δ) ∈ (frameAt (conjWord word)).freeV ∧
        laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0)
    (hX1 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2)))
    (hX2 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2 - δ)))
    (hcanon : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 →
      P.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ)) :
    FLatticePaper.CollarChain.TieAgreeHyp word P := by
  have hfreeOut : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 → ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquare P.retained (zTurn (c - (frameAt word).sheetShift)) := by
    intro c hT hM hnf
    have h0 : 0 ≤ sheetPsi word c := by
      unfold sheetPsi
      rw [hT, sub_self]
    have hlap := FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE h0 hM
    exact FLatticePaper.W1NonfreeHsqC.parentSquare_of_out
      (FreeRoutes.hfree_assembled hδη hδ hSE.packet hW1 Gm (frameAt word).eps_unit P.toOldPolicyWitness hW Rg
        hX3 hX1 hX2 hcanon hnf hlap)
  have hag := FLatticePaper.W1MFinal.hagree_M_tie_of_inherited word hw hSE P hs hW1 hfreeOut
  have hwhite : ∀ p : Site, laplacian (standardField (conjWord word)) p = 0 → ∀ i : Site,
      P.retained p i ↔ i = (Gm.game (frameAt word).eps (frameAt word).eps_unit).sel p := by
    intro p hp i
    rw [hW]
    exact (Gm.game (frameAt word).eps (frameAt word).eps_unit).white_policy p hp i
  intro x hψ hM y
  have hT : (frameAt word).sheetC (FqW word) x = (frameAt word).sheetA (FqW word) x := by
    unfold sheetPsi at hψ
    linarith
  have hA : laplacian (standardField (conjWord word)) (zTurn (x - (frameAt word).sheetShift)) = 0 :=
    FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE hψ.ge hM
  have hψC : 0 ≤ sheetPsi word ((frameAt word).centre - x) := by
    rw [FLatticePaper.W1NonfreeHsqC.psi_reflect hw hSE x, hψ]
    norm_num
  have hMC : laplacian (MW word) ((frameAt word).centre - x) = 0 := by
    rw [FLatticePaper.W1NonfreeHsqC.lap_MW_reflect hw hSE x]
    exact hM
  have hC : laplacian (standardField (conjWord word))
      (zTurn ((frameAt word).centre - x - (frameAt word).sheetShift)) = 0 :=
    FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hw hSE hψC hMC
  have hpt : P.retained (zTurn (x - (frameAt word).sheetShift))
      (zTurn (pointerOf (sheetQ P.retained (frameAt word).sheetShift) x - (frameAt word).sheetShift)) :=
    pointer_retained P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift x (frameAt word).evenSite_sheetShift hA
  have hagx : P.retained (zTurn ((frameAt word).centre - x - (frameAt word).sheetShift))
      (zTurn ((frameAt word).centre - pointerOf (sheetQ P.retained (frameAt word).sheetShift) x -
        (frameAt word).sheetShift)) := hag x hT hM
  have hselA := (hwhite _ hA _).mp hpt
  have hselC := (hwhite _ hC _).mp hagx
  show P.retained (zTurn (x - (frameAt word).sheetShift)) (zTurn (y - (frameAt word).sheetShift)) ↔
    P.retained (zTurn ((frameAt word).centre - x - (frameAt word).sheetShift))
      (zTurn ((frameAt word).centre - y - (frameAt word).sheetShift))
  rw [hwhite _ hA, hwhite _ hC, ← hselA, ← hselC, zTurn_eq_iff, zTurn_eq_iff]
  simp only [sub_left_inj, sub_right_inj]

end FLatticePaper.TieAgreeClose
