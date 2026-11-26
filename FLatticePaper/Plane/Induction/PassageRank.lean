import FLatticePaper.Plane.Induction.FreeSchedule
import FLatticePaper.Plane.Induction.W1MRank
import FLatticePaper.Plane.Induction.ForcedArrows
import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.Seams
import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TransferSat
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.FreeClosure
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.EndpointDeck

/-! # The acyclic passage (Q36, reading (a)): a natural-number rank of the nonfree passage

The passage of `FreeSchedule.plus_passage_free` / `minus_passage_free` moves along `PassageStep n d F`: a black site to one of its
inputs, a white site to a W1-forced input inside the strict interior `E° = StrictInterior n d` (the forced edges supplied by `W1At`).
A nonfree site of the closed polygon is strict-interior, so every step is an edge inside `E°`:

* `M` (the sheet minimum, `F = M` on the closed polygon) has a global burning rank `R`, which strictly decreases along every black
  edge (both inputs) and along every forced white edge (the selected input, `burning_sel`, `TransferSat.forced_sound_R`, with the
  forced edge transported from `F` to `M` by `W1Bridge.forcedEdgeIn_congr`);
* the counting rank `ρ z = #{u ∈ E° | R u < R z}` (`nat_rank_of_key`) decreases along every such step.

No Protected Web hypothesis is needed: the passage only uses forced edges inside `E°`. -/

namespace FLatticePaper.PassageRank

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.KMinBridge FLatticePaper.FreeSchedule

/-! ## Abstract counting rank -/

/-- **A counting rank.** If the representative map `rep` lands in a finite set `T` on nonfree sites and every nonfree passage step
strictly lowers `R (rep ·)`, then the number of points of `T` strictly below `R (rep z)` is a `ℕ`-rank strictly decreasing along the
steps. -/
theorem nat_rank_of_key {β : Type*} [LinearOrder β] (T : Set Site) (hT : T.Finite) (R : Site → β)
    (rep : Site → Site) (nf : Site → Prop) (G : Site → Site → Prop)
    (hrep : ∀ z, nf z → rep z ∈ T)
    (hdec : ∀ z o, nf z → nf o → G z o → R (rep o) < R (rep z)) :
    ∃ ρ : Site → ℕ, ∀ z o, nf z → nf o → G z o → ρ o < ρ z := by
  refine ⟨fun z => {u | u ∈ T ∧ R u < R (rep z)}.ncard, fun z o hz ho hG => ?_⟩
  have hlt : R (rep o) < R (rep z) := hdec z o hz ho hG
  have hsub : {u | u ∈ T ∧ R u < R (rep o)} ⊂ {u | u ∈ T ∧ R u < R (rep z)} := by
    refine Set.ssubset_iff_subset_ne.2 ⟨fun u hu => ⟨hu.1, lt_trans hu.2 hlt⟩, fun heq => ?_⟩
    have hmem : rep o ∈ {u | u ∈ T ∧ R u < R (rep z)} := ⟨hrep o ho, hlt⟩
    rw [← heq] at hmem
    exact lt_irrefl _ hmem.2
  exact Set.ncard_lt_ncard hsub (hT.subset fun u hu => hu.1)

/-! ## A satisfying selection of a burning rank -/

/-- **The selection of a burning rank.** A global strict AND-OR rank of `F` gives a selection that is an input of each white site and
strictly lowers `R` there, and satisfies every square clause. -/
theorem burning_sel {β : Type*} [LinearOrder β] {F : Field} {R : Site → β} (h : IsBurningRank F R) :
    ∃ sel : Site → Site, (∀ c, laplacian F c = 0 → (sel c = incomingNeg c ∨ sel c = incomingPos c) ∧ R (sel c) < R c) ∧
      ∀ a b, SquareClauseSat F sel a b := by
  have hbin : ∀ c, laplacian F c = -1 ∨ laplacian F c = 0 := by
    intro c
    rcases h c with ⟨hl, -, -⟩ | ⟨hl, -⟩
    · exact Or.inl hl
    · exact Or.inr hl
  have hblack : ∀ c, laplacian F c = -1 → ∀ i, (i = incomingNeg c ∨ i = incomingPos c) → R i < R c := by
    intro c hc i hi
    rcases h c with ⟨-, hn, hp⟩ | ⟨hl, -⟩
    · rcases hi with rfl | rfl
      · exact hn
      · exact hp
    · exact absurd (hl.symm.trans hc) (by norm_num)
  have hwhite : ∀ c, ∃ i, laplacian F c = 0 → (i = incomingNeg c ∨ i = incomingPos c) ∧ R i < R c := by
    intro c
    rcases h c with ⟨hl, hn, hp⟩ | ⟨hl, hn | hp⟩
    · exact ⟨incomingNeg c, fun h0 => absurd (h0.symm.trans hl) (by norm_num)⟩
    · exact ⟨incomingNeg c, fun _ => ⟨Or.inl rfl, hn⟩⟩
    · exact ⟨incomingPos c, fun _ => ⟨Or.inr rfl, hp⟩⟩
  choose sel hsel using hwhite
  exact ⟨sel, hsel, fun a b => W1MRank.squareClauses_of_burning hbin hblack hsel a b⟩

/-- Nonfreeness is invariant under deck translates. -/
theorem nonfree_add_span (frame : ChildFrame) {z v : Site} (hz : Nonfree frame z)
    (hv : v ∈ frame.child.modifiedDeck.span) : Nonfree frame (z + v) := by
  intro w hw hfree
  apply hz (v + w) (FreeClosure.span_add hv hw)
  rw [← add_assoc]
  exact hfree

/-! ## The rank of the passage -/

/-- **The passage rank (Q36).** For the sheet minimum `M` with a global burning rank `R`, and `F = M` on the closed polygon, a nonfree
passage step between nonfree points of the closed polygon strictly lowers `R`: a black step to an input by `IsBurningRank`, a white
step along a W1-forced edge of the strict interior by `forcedEdgeIn_congr` and `TransferSat.forced_sound_R` (the selection of `M`
is the forced input). The counting rank of `nat_rank_of_key` then decreases along every such step. No translates are needed:
a nonfree point of the closed polygon is strict-interior (`TransferW1.nonfree_strictInterior`). -/
theorem passage_rank {β : Type*} [LinearOrder β] (frame : ChildFrame) {F M : Field}
    (hFM : ∀ s, s ∈ frame.closedPolygon → F s = M s)
    {R : Site → β} (hR : IsBurningRank M R) :
    ∃ ρ : Site → ℕ, ∀ z o : Site, (z ∈ frame.closedPolygon ∧ Nonfree frame z) →
      (o ∈ frame.closedPolygon ∧ Nonfree frame o) →
      PassageStep frame.child.num frame.child.den F z o → ρ o < ρ z := by
  classical
  obtain ⟨sel, hsel, hsq⟩ := burning_sel hR
  have hagree : ∀ c, FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c →
      F c = M c ∧ F (incomingNeg c) = M (incomingNeg c) ∧ F (incomingPos c) = M (incomingPos c) := by
    intro c hc
    have hs := TransferW1.strictInterior_star frame hc
    exact ⟨hFM c hs.1, hFM _ hs.2.1, hFM _ hs.2.2⟩
  have hdec : ∀ z o : Site, (z ∈ frame.closedPolygon ∧ Nonfree frame z) →
      (o ∈ frame.closedPolygon ∧ Nonfree frame o) →
      PassageStep frame.child.num frame.child.den F z o → R o < R z := by
    rintro z o ⟨hzc, hzn⟩ - hG
    have hSI := TransferW1.nonfree_strictInterior frame hzc hzn
    have hstar := TransferW1.strictInterior_star frame hSI
    have hlapM : laplacian F z = laplacian M z :=
      W1Bridge.laplacian_congr (hFM z hstar.1) (hFM _ hstar.2.1) (hFM _ hstar.2.2)
    rcases hG with ⟨hl, hedge⟩ | ⟨hl, hf⟩
    · -- a black edge: both inputs of `M` at `z` have smaller rank
      have hbl : laplacian M z = -1 := by rw [← hlapM, hl]
      rcases hR z with ⟨-, hn, hp⟩ | ⟨hl0, -⟩
      · rcases hedge with h | h
        · rw [h]
          exact hn
        · rw [h]
          exact hp
      · exact absurd (hbl.symm.trans hl0) (by norm_num)
    · -- a white edge: the W1-forced input of `M` at `z` is the selected input, which has smaller rank
      have hwh : laplacian M z = 0 := by rw [← hlapM, hl]
      have hMf : FLatticePaper.W1.ForcedEdgeIn M (FLatticePaper.W1.StrictInterior frame.child.num frame.child.den)
          (fun _ _ => False) z o :=
        W1Bridge.forcedEdgeIn_congr hagree hf
      have hsel_eq : sel z = o :=
        TransferSat.forced_sound_R (R := FLatticePaper.W1.StrictInterior frame.child.num frame.child.den) sel
          (fun c hc => (hsel c hc).1) (fun a b _ => hsq a b) z o hMf
      rw [← hsel_eq]
      exact (hsel z hwh).2
  have hfin : {c : Site | FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c}.Finite :=
    W1Step.strictInterior_child_finite frame
  exact nat_rank_of_key _ hfin R (fun z => z) (fun z => z ∈ frame.closedPolygon ∧ Nonfree frame z)
    (PassageStep frame.child.num frame.child.den F)
    (fun z hz => TransferW1.nonfree_strictInterior frame hz.1 hz.2) (fun z o hz ho hG => hdec z o hz ho hG)

/-! ## The sheet minimum's burning rank from the conjugate's strong estimates -/

/-- **The burning rank of the sheet minimum from the conjugate's strong estimates** (the chain proof of `W1MRank`, its rank part). -/
theorem sheetMin_burning_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∃ R : Site → ℤ ×ₗ ℤ,
      IsBurningRank ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) R := by
  have hsheet := i3_sheetLocalInputs_of_strong h hSE
  have hG := hSE.packet
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant h hG (i3aGrade_deck h hG)
    (permitA_invariant h hG) hsheet.permitA hsheet.noA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant h hG (tGrade_add_odd_deck word)
    (permitC_invariant h hG) hsheet.permitC hsheet.noC
  exact W1MRank.sheetMin_burningRank_of_chain h hG hsheet.unit rankA rankC hrankA hrankC

/-! ## The passage reaches a free site, with the acyclic rank -/

/-- **The `K₊`-passage stops at a free site (Q36).** The acyclic rank of the passage is `passage_rank`, from the sheet minimum's
burning rank; the white steps are the W1-forced edges of `W1At`. -/
theorem plus_passage_free_Q36 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kPlusW word z₀ ≤ kPlusW word w) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kPlusW word f = kPlusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
  obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR
  exact FreeSchedule.plus_passage_free h hSE hPR hW hW1 hfort hz₀S hz₀E hmin
    ⟨ρ, fun z o hz hnz hG ho hno => hρ z o ⟨hz.2.1, hnz⟩ ⟨ho.2.1, hno⟩ hG⟩

/-- **The `K₋`-passage stops at a free site (Q36).** The same statement for `K₋`. -/
theorem minus_passage_free_Q36 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kMinusW word z₀ ≤ kMinusW word w) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kMinusW word f = kMinusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
  obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR
  exact FreeSchedule.minus_passage_free h hSE hPR hW hW1 hfort hz₀S hz₀E hmin
    ⟨ρ, fun z o hz hnz hG ho hno => hρ z o ⟨hz.2.1, hnz⟩ ⟨ho.2.1, hno⟩ hG⟩

end FLatticePaper.PassageRank
