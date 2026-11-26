import FLatticePaper.Plane.Induction.ForcedPlusStrict
import FLatticePaper.Plane.Induction.NegFromPlus
import FLatticePaper.Plane.Induction.FreePermitted
import FLatticePaper.Plane.Induction.DeckForced
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.Sheets

/-! # The forced raw-slip permit on every nonfree forced white (both signs)

For a nonfree white `c` (laplacian `0`, `¬ freeClosure c`) with a forced input `o`, the sign +1 permit reduces to the strictly interior
case (`ForcedPlusStrict.plus_forced_strict`) by a span translate `c + t ∈ E` (`closedPolygon_covers`); the translate keeps the edge forced
(`forcedEdge_add`), the nonfree condition (`span`), and the permit (`FreePermitted.slip_le_of_translate`). The sign −1 permit is the
sign +1 permit at the reflected edge (`NegFromPlus.slip_minus_white_of_plus`). -/

namespace FLatticePaper.ForcedPermitAll

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- **The sign +1 permit on every nonfree forced white.** -/
theorem plus_forced_all {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hsheet : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 → ∀ o : Site,
        ForcedEdge (standardField word) (fun _ _ => False) c o →
        o = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
          (FLatticePaper.W1Step.sheetPsi word) c)
    (hsat : FLatticePaper.Induction.HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hrise : FLatticePaper.W4Reduction.NoRiseForced P.toOldPolicyWitness.toOldPolicyData) :
    ∀ c o : Site, laplacian (standardField word) c = 0 →
      ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      (frameAt word).slip (standardField word) 1 o ≤ (frameAt word).slip (standardField word) 1 c := by
  intro c o hlap hnf hf
  have hPk : (frameAt word).Packet (standardField word) := hW.packet
  obtain ⟨y, hy, i, j, hcy⟩ := (frameAt word).closedPolygon_covers c
  have hneg : (frameAt word).child.modifiedDeck.combine (-i) (-j) =
      -(frameAt word).child.modifiedDeck.combine i j := by
    unfold PeriodDeck.combine
    ext <;> simp <;> ring
  have ht : (frameAt word).child.modifiedDeck.combine (-i) (-j) ∈ (frameAt word).child.modifiedDeck.span :=
    ⟨-i, -j, rfl⟩
  have hct : y = c + (frameAt word).child.modifiedDeck.combine (-i) (-j) := by
    rw [hneg, hcy]
    abel
  have hev : EvenSite ((frameAt word).child.modifiedDeck.combine (-i) (-j)) :=
    ((Fraction.mem_modifiedDeck_iff (frameAt word).child _).mp ht).2
  have hL : ∀ z, laplacian (standardField word) (z + (frameAt word).child.modifiedDeck.combine (-i) (-j)) =
      laplacian (standardField word) z := fun z =>
    laplacian_span_inv (frameAt word) (standardField word) hPk ht z
  have hlapy : laplacian (standardField word) y = 0 := by
    rw [hct, hL c]
    exact hlap
  have hnfy : ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) y := by
    rintro ⟨s, hs, hm⟩
    apply hnf
    refine ⟨(frameAt word).child.modifiedDeck.combine (-i) (-j) + s, FLatticePaper.Induction.span_add_mem ht hs, ?_⟩
    have e : c + ((frameAt word).child.modifiedDeck.combine (-i) (-j) + s) = y + s := by
      rw [hct]
      abel
    rw [e]
    exact hm
  have hfy : ForcedEdge (standardField word) (fun _ _ => False) y
      (o + (frameAt word).child.modifiedDeck.combine (-i) (-j)) := by
    have hh := forcedEdge_add (standardField word) hev hL hf
    rw [← hct] at hh
    exact hh
  have hSI : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den y :=
    FLatticePaper.TransferW1.nonfree_strictInterior (frameAt word) hy
      (fun s hs hm => hnfy ⟨s, hs, hm⟩)
  have hA := ForcedPlusStrict.plus_forced_strict h hW hSE P hsheet hsat hW1 hrise hSI hy hlapy hnfy hfy
  exact FLatticePaper.FreePermitted.slip_le_of_translate (c := c) (i := o) (c' := y)
    (i' := o + (frameAt word).child.modifiedDeck.combine (-i) (-j))
    (t := (frameAt word).child.modifiedDeck.combine (-i) (-j)) hW 1 ht hct rfl hA

/-- **The forced raw-slip permit, both signs.** For a nonfree white `c` with laplacian `0` and a forced input `o`, the permit
`D_η(o) ≤ D_η(c)` holds for `η = ±1` (the form of `hforced`). -/
theorem forced_slip_permit {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    (hsheet : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (standardField word) c = 0 → ∀ o : Site,
        ForcedEdge (standardField word) (fun _ _ => False) c o →
        o = FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
          (FLatticePaper.W1Step.sheetPsi word) c)
    (hsat : FLatticePaper.Induction.HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hrise : FLatticePaper.W4Reduction.NoRiseForced P.toOldPolicyWitness.toOldPolicyData) :
    ∀ η : ℤ, (η = 1 ∨ η = -1) → ∀ c o : Site,
      ¬ FLatticePaper.FreeClosure.freeClosure (frameAt word) c →
      laplacian (standardField word) c = 0 →
      ForcedEdge (standardField word) (fun _ _ => False) c o →
      slipPermits (standardField word) (fun z => standardField word (z + η • (frameAt word).shortShift)) c o := by
  intro η hη c o hnf hlap hf
  have hPk : (frameAt word).Packet (standardField word) := hW.packet
  have hplus := plus_forced_all h hW hSE P hsheet hsat hW1 hrise
  apply (FreePermitted.slipPermits_iff_slip η c o).mpr
  rcases hη with rfl | rfl
  · exact hplus c o hlap hnf hf
  · exact FLatticePaper.NegFromPlus.slip_minus_white_of_plus h hPk
      (fun c' o' hf' hl' hn' => hplus c' o' hl' hn' hf') hf hlap hnf

end FLatticePaper.ForcedPermitAll
