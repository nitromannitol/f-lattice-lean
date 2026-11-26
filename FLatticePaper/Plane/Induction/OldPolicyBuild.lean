import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.F2F3Pure
import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.PrivateSquare

/-! # The ranked old policy of a canonical game with a deck rank

`OldPolicyRanked frame F (fun _ _ => False) η` from the canonical signed games `G` of `frame` and a rank `R` of their sign-`η` policy
with the deck increments `(cU, cV)` (`GamesWithRank`). The data is `oldPolicyData_of_canonical`; the rank is `R`, with the strict
decrease along retained edges; the rank increments `(−1, η)` come from `EPolicy.rankWithIncrements_of_strict_hull`, with the price
`P = cutGrade 1 0 1` (drift `−1` along the kernel, `0` along the transverse vector) and the rounded slip `J = cutGrade 0 1 η` (drift
`0`, `η`), both monotone along retained edges by the canonical policy's own fields.

The field `strictForced` comes from the conjugate's `W1Forced` (`strictForced_of_W1Forced`), `privateSquare` is proved
(`PrivateSquare`), and `freeInputForced` is an input (numerically checked, not proved). -/

namespace FLatticePaper.OldPolicyBuild

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1Witness FLatticePaper.W1Phase FLatticePaper.SquareClauses
open FLatticePaper.W1 FLatticePaper.AndOrRank

/-- **The strict forcing of the earlier field.** A forced non-seed white in the strict interior is forced by a strict-interior derivation:
the conjugate's `W1Forced` gives one, with some output `o`, and the forced output is unique at a white (`forcedWhiteUnique`, since the
forced input is retained), so `o` is the forced input. -/
theorem strictForced_of_W1Forced {frame : ChildFrame} {G : Field} {η : ℤ} (D : OldPolicyData frame G (fun _ _ => False) η)
    (hW : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G) :
    ∀ c i, FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c →
      ForcedEdge G (fun _ _ => False) c i → ¬ (fun _ _ => False) c i →
      FLatticePaper.W1.ForcedEdgeIn G (FLatticePaper.W1.StrictInterior frame.child.num frame.child.den)
        (fun _ _ => False) c i := by
  intro c i hcS hF hns
  have hw : laplacian G c = 0 := by
    cases hF with
    | seed hs => exact absurd hs hns
    | @unit _ _ _ _ _ _ hw _ _ _ _ => exact hw
  obtain ⟨o, ho⟩ := hW c hcS hw
  have hu := D.forcedWhiteUnique c i (D.forcedRetained c i hF) hw o (FLatticePaper.W1.forcedEdgeIn_forced ho)
  rw [hu] at ho
  exact ho

/-- The rank increments `(−1, η)` of the sign-`η` policy of a canonical game, from its deck rank. -/
theorem rankIncr_of_games {frame : ChildFrame} {F : Field} (hP : frame.Packet F) (G : CanonicalSignedGames frame F)
    (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) (cU cV : ℤ)
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cV)
    (hR : ∀ x i, (G.game η hη).policy x i → R i < R x) :
    RankWithIncrements (G.game η hη).policy frame.child.modifiedDeck.kernel frame.child.modifiedDeck.transverse (-1) η := by
  have h := EPolicy.rankWithIncrements_of_strict_hull (retained := (G.game η hη).policy)
    (U := frame.child.modifiedDeck.kernel) (V := frame.child.modifiedDeck.transverse) (η := η) hη
    (P := frame.cutGrade F 1 0 1) (J := frame.cutGrade F 0 1 η)
    (fun z => frame.cutGrade_kernel F hP.periods 1 0 1 z)
    (fun z => by rw [frame.cutGrade_transverse F hP.periods 1 0 1 z]; ring)
    (fun z => by rw [frame.cutGrade_kernel F hP.periods 0 1 η z, sub_zero])
    (fun z => by rw [frame.cutGrade_transverse F hP.periods 0 1 η z, one_mul])
    (fun x y h => ⟨(G.game η hη).nonincreasingP x y h, (G.game η hη).nonincreasingJ x y h⟩)
    hRU hRV hR 1 1 one_pos one_pos
  rw [one_mul] at h
  exact h

/-- **The ranked old policy of a canonical game with a deck rank**: the canonical data, the rank `R` with its strict decrease and
the increments `(−1, η)`, and the two forcing fields as inputs. -/
def oldPolicyRanked_of_games {frame : ChildFrame} {F : Field} (hP : frame.Packet F)
    (hF : ∀ z, F (FLatticePaper.Induction.reflectionI - z) = F z) (G : CanonicalSignedGames frame F)
    (η : ℤ) (hη : η = 1 ∨ η = -1) (R : Site → ℤ) (cU cV : ℤ)
    (hRU : ∀ z, R (z + frame.child.modifiedDeck.kernel) = R z + cU)
    (hRV : ∀ z, R (z + frame.child.modifiedDeck.transverse) = R z + cV)
    (hR : ∀ x i, (G.game η hη).policy x i → R i < R x)
    (hW : FLatticePaper.W1.W1Forced frame.child.num frame.child.den F)
    (hFI : ∀ c i o, ForcedEdge F (fun _ _ => False) c i → laplacian F c = 0 →
      (o = incomingNeg c ∨ o = incomingPos c) → o ∈ frame.freeH ∪ frame.freeV → laplacian F o = 0 → o = i) :
    OldPolicyRanked frame F (fun _ _ => False) η where
  toOldPolicyWitness :=
    { toOldPolicyData := oldPolicyData_of_canonical hF G η hη
      strictForced := strictForced_of_W1Forced (oldPolicyData_of_canonical hF G η hη) hW
      freeInputForced := hFI
      privateSquare := fun _ _ hF' hns _ =>
        PrivateSquare.private_square_of_forced (oldPolicyData_of_canonical hF G η hη).quota
          (oldPolicyData_of_canonical hF G η hη).forcedRetained hF' hns }
  rank := R
  rank_decr := hR
  rankIncr := rankIncr_of_games hP G η hη R cU cV hRU hRV hR

end FLatticePaper.OldPolicyBuild
