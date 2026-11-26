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

The passage of `FreeSchedule.plus_passage_free` / `minus_passage_free` moves along `PassageStep F`: a black site to one of its inputs,
a white site to its W1-forced input. Its nonfree-to-nonfree steps lift to the finite strict interior `E° = StrictInterior n d`:

* every nonfree `z` has a deck translate `z + vr z ∈ E°` (`nonfree_bridge`), unique in its class (`strictInterior_unique`);
* a passage step `z → o` between nonfree sites lifts to `z + vr z → o + vr z`, an edge of the sheet minimum `M` inside `E°`;
* `M`'s burning rank `R` strictly decreases along it: at a black edge both inputs, at a white edge the selected input
  (`burning_sel`, `TransferSat.forced_sound_R`).

The white lift of the forced edge to `M` inside `E°` is the Protected Web Lemma (Q39), taken here as the named hypothesis `Q39Hyp`.
The counting rank `ρ z = #{u ∈ E° | R u < R (rep z)}` is then a `ℕ`-valued rank of the passage (`nat_rank_of_key`). -/

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

/-! ## Arithmetic of the strict interior modulo the deck -/

/-- The parity of a deck combination: `d + n` is even for odd `n`, `d`. -/
theorem combine_even {n d : ℤ} (hnodd : n % 2 = 1) (hdodd : d % 2 = 1) (i j : ℤ) :
    ((i * d + j * (n - d)) + (i * n + j * (n + d))) % 2 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, d + n = 2 * k := ⟨(d + n) / 2, by omega⟩
  have e : (i * d + j * (n - d)) + (i * n + j * (n + d)) = 2 * (k * i + n * j) := by
    linear_combination i * hk
  rw [e]
  generalize k * i + n * j = m
  omega

/-- **Uniqueness of the strict interior in a deck class (arithmetic).** A translate `b = a + (i d + j (n − d), i n + j (n + d))` of a
strict-interior point by the deck `(d, n)`, `(n − d, n + d)` is strict-interior only if the translate is trivial: the grades `t` and `s`
shift by `−jT` and `iT`, and the four open intervals have width below `T`. -/
theorem si_unique_arith {n d : ℤ} (hn1 : 1 ≤ n) (hnd : n < d) (hd3 : 3 ≤ d) (hnodd : n % 2 = 1) (hdodd : d % 2 = 1)
    {a b : Site} (ha : W1.StrictInterior n d a) (hb : W1.StrictInterior n d b) {i j : ℤ}
    (hb1 : b.1 = a.1 + (i * d + j * (n - d))) (hb2 : b.2 = a.2 + (i * n + j * (n + d))) : b = a := by
  have hT : 0 < W1.w1T n d := by
    have e : W1.w1T n d = (d - n) * (d + n) + 2 * (n * d) := by unfold W1.w1T; ring
    have h1 : 0 < (d - n) * (d + n) := mul_pos (by omega) (by omega)
    have h2 : 0 < n * d := mul_pos (by omega) (by omega)
    rw [e]
    linarith
  have hL : 4 ≤ d + n := by omega
  have hpar : (b.1 + b.2) % 2 = (a.1 + a.2) % 2 := by
    have hc := combine_even hnodd hdodd i j
    rw [hb1, hb2]
    omega
  have ht : (n * b.1 - d * b.2) - (n * a.1 - d * a.2) = -(j * W1.w1T n d) := by
    rw [hb1, hb2]
    unfold W1.w1T
    ring
  have hs : ((d + n) * b.1 + (d - n) * b.2) - ((d + n) * a.1 + (d - n) * a.2) = i * W1.w1T n d := by
    rw [hb1, hb2]
    unfold W1.w1T
    ring
  simp only [W1.StrictInterior, W1.w1b, W1.w1t, W1.w1a, W1.w1h, W1.w1s, W1.w1c] at ha hb
  generalize W1.w1T n d = T at ha hb hT ht hs
  have key : (j * T < T ∧ -T < j * T) ∧ (i * T < T ∧ -T < i * T) := by
    by_cases hev : EvenSite a
    · have hevb : EvenSite b := by
        unfold EvenSite at hev ⊢
        omega
      simp only [hev, hevb, ↓reduceIte] at ha hb
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      obtain ⟨hb1', hb2', hb3, hb4⟩ := hb
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    · have hevb : ¬ EvenSite b := by
        unfold EvenSite at hev ⊢
        omega
      simp only [hev, hevb, ↓reduceIte] at ha hb
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      obtain ⟨hb1', hb2', hb3, hb4⟩ := hb
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  obtain ⟨⟨hj1, hj2⟩, ⟨hi1, hi2⟩⟩ := key
  have hi0 : i = 0 := by
    rcases lt_trichotomy i 0 with h | h | h
    · exfalso
      have h1 : (0 : ℤ) ≤ (-1 - i) * T := mul_nonneg (by omega) hT.le
      have h2 : (-1 - i) * T = -T - i * T := by ring
      linarith
    · exact h
    · exfalso
      have h1 : (0 : ℤ) ≤ (i - 1) * T := mul_nonneg (by omega) hT.le
      have h2 : (i - 1) * T = i * T - T := by ring
      linarith
  have hj0 : j = 0 := by
    rcases lt_trichotomy j 0 with h | h | h
    · exfalso
      have h1 : (0 : ℤ) ≤ (-1 - j) * T := mul_nonneg (by omega) hT.le
      have h2 : (-1 - j) * T = -T - j * T := by ring
      linarith
    · exact h
    · exfalso
      have h1 : (0 : ℤ) ≤ (j - 1) * T := mul_nonneg (by omega) hT.le
      have h2 : (j - 1) * T = j * T - T := by ring
      linarith
  refine Prod.ext ?_ ?_
  · simp [hb1, hi0, hj0]
  · simp [hb2, hi0, hj0]

/-- The deck combination in coordinates: `combine i j = (i d + j (n − d), i n + j (n + d))` for the child frame. -/
theorem combine_coords (frame : ChildFrame) (i j : ℤ) :
    frame.child.modifiedDeck.combine i j =
      (i * frame.child.den + j * (frame.child.num - frame.child.den),
        i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
  have hk : frame.child.modifiedDeck.kernel = (frame.child.den, frame.child.num) := frame.child_modifiedDeck_kernel
  have ht : frame.child.modifiedDeck.transverse =
      (frame.child.num - frame.child.den, frame.child.num + frame.child.den) :=
    EndpointDeck.transverse_eq_Vdeck frame
  ext <;> simp [PeriodDeck.combine, hk, ht]

/-- Deck combinations have even coordinate sum. -/
theorem span_parity (frame : ChildFrame) {v : Site} (hv : v ∈ frame.child.modifiedDeck.span) :
    (v.1 + v.2) % 2 = 0 := by
  obtain ⟨i, j, rfl⟩ := hv
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  rw [combine_coords frame i j]
  exact combine_even hnodd hdodd i j

/-- **Uniqueness of strict-interior representatives.** Two strict-interior points differing by a deck translate are equal. -/
theorem strictInterior_unique (frame : ChildFrame) {a b v : Site}
    (ha : W1.StrictInterior frame.child.num frame.child.den a)
    (hb : W1.StrictInterior frame.child.num frame.child.den b)
    (hv : v ∈ frame.child.modifiedDeck.span) (hba : b = a + v) : b = a := by
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  obtain ⟨i, j, rfl⟩ := hv
  rw [combine_coords frame i j] at hba
  have hb1 : b.1 = a.1 + (i * frame.child.den + j * (frame.child.num - frame.child.den)) := by
    simp [hba]
  have hb2 : b.2 = a.2 + (i * frame.child.num + j * (frame.child.num + frame.child.den)) := by
    simp [hba]
  exact si_unique_arith (by omega) hnd hd3 hnodd hdodd ha hb hb1 hb2

/-- Nonfreeness is invariant under deck translates. -/
theorem nonfree_add_span (frame : ChildFrame) {z v : Site} (hz : Nonfree frame z)
    (hv : v ∈ frame.child.modifiedDeck.span) : Nonfree frame (z + v) := by
  intro w hw hfree
  apply hz (v + w) (FreeClosure.span_add hv hw)
  rw [← add_assoc]
  exact hfree

/-! ## The rank of the passage -/

/-- **The representative key decreases along the passage.** For the sheet minimum `M` with a global burning rank `R`, and the field
`F = M` on the closed polygon, the lift of a nonfree passage step is a strict decrease of `R` at the representatives. -/
theorem passage_rank {β : Type*} [LinearOrder β] (frame : ChildFrame) {F M : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV)
    (hFM : ∀ s, s ∈ frame.closedPolygon → F s = M s)
    {R : Site → β} (hR : IsBurningRank M R)
    (hQ39 : ∀ z o v : Site, v ∈ frame.child.modifiedDeck.span →
      W1.StrictInterior frame.child.num frame.child.den (z + v) →
      ForcedEdge F (fun _ _ => False) z o →
      W1.ForcedEdgeIn M (W1.StrictInterior frame.child.num frame.child.den) (fun _ _ => False) (z + v) (o + v)) :
    ∃ ρ : Site → ℕ, ∀ z o : Site, Nonfree frame z → Nonfree frame o → PassageStep F z o → ρ o < ρ z := by
  classical
  have hvex : ∀ z, Nonfree frame z → ∃ v, v ∈ frame.child.modifiedDeck.span ∧
      W1.StrictInterior frame.child.num frame.child.den (z + v) :=
    fun z hz => nonfree_bridge frame z hz
  choose! vr hvr hvSI using hvex
  obtain ⟨sel, hsel, hsq⟩ := burning_sel hR
  have hdec : ∀ z o : Site, Nonfree frame z → Nonfree frame o → PassageStep F z o →
      R (o + vr o) < R (z + vr z) := by
    intro z o hz ho hG
    have hedge : o = incomingNeg z ∨ o = incomingPos z := by
      rcases hG with ⟨-, h⟩ | ⟨-, hf⟩
      · exact h
      · exact MinPassage.forced_input_of_unseeded hf
    have hvz : vr z ∈ frame.child.modifiedDeck.span := hvr z hz
    have hvo : vr o ∈ frame.child.modifiedDeck.span := hvr o ho
    have hev : EvenSite (vr z) := span_parity frame hvz
    have hyS : W1.StrictInterior frame.child.num frame.child.den (z + vr z) := hvSI z hz
    have hyst := TransferW1.strictInterior_star frame hyS
    -- the translate of `o` by `vr z` is an input of `z + vr z`
    have hin : o + vr z = incomingNeg (z + vr z) ∨ o + vr z = incomingPos (z + vr z) := by
      rcases hedge with rfl | rfl
      · exact Or.inl (ForcedArrows.incomingNeg_add_even hev).symm
      · exact Or.inr (ForcedArrows.incomingPos_add_even hev).symm
    have hwS : o + vr z ∈ frame.closedPolygon := by
      rcases hin with h | h
      · rw [h]
        exact hyst.2.1
      · rw [h]
        exact hyst.2.2
    have hwSI : W1.StrictInterior frame.child.num frame.child.den (o + vr z) :=
      TransferW1.nonfree_strictInterior frame hwS (nonfree_add_span frame ho hvz)
    -- the representative of `o` is `o + vr z`
    have hvdiff : vr o - vr z ∈ frame.child.modifiedDeck.span := FreeClosure.span_sub hvo hvz
    have hsame : o + vr o = o + vr z :=
      strictInterior_unique frame hwSI (hvSI o ho) hvdiff (by abel)
    rw [hsame]
    -- the lift to `M` at `y = z + vr z`
    have hFy : laplacian F (z + vr z) = laplacian F z := by
      obtain ⟨i, j, hij⟩ := hvz
      rw [hij]
      exact laplacian_add_combine hper z i j
    have hyF : laplacian M (z + vr z) = laplacian F z := by
      rw [← hFy]
      exact (W1Bridge.laplacian_congr (hFM (z + vr z) hyst.1) (hFM (incomingNeg (z + vr z)) hyst.2.1)
        (hFM (incomingPos (z + vr z)) hyst.2.2)).symm
    rcases hG with ⟨hl, -⟩ | ⟨hl, hf⟩
    · -- a black edge: both inputs of `M` at `y` have smaller rank
      have hbl : laplacian M (z + vr z) = -1 := by rw [hyF, hl]
      rcases hR (z + vr z) with ⟨-, hn, hp⟩ | ⟨hl0, -⟩
      · rcases hin with h | h
        · rw [h]
          exact hn
        · rw [h]
          exact hp
      · exact absurd (hbl.symm.trans hl0) (by norm_num)
    · -- a white edge: the forced input of `M` at `y` is the selected input, which has smaller rank
      have hwh : laplacian M (z + vr z) = 0 := by rw [hyF, hl]
      have hQ := hQ39 z o (vr z) hvz hyS hf
      have hsel_eq : sel (z + vr z) = o + vr z :=
        TransferSat.forced_sound_R (R := W1.StrictInterior frame.child.num frame.child.den) sel
          (fun c hc => (hsel c hc).1) (fun a b _ => hsq a b) (z + vr z) (o + vr z) hQ
      rw [← hsel_eq]
      exact (hsel (z + vr z) hwh).2
  have hfin : {c : Site | W1.StrictInterior frame.child.num frame.child.den c}.Finite :=
    W1Step.strictInterior_child_finite frame
  exact nat_rank_of_key _ hfin R (fun z => z + vr z) (Nonfree frame) (PassageStep F)
    (fun z hz => hvSI z hz) (fun z o hz ho hG => hdec z o hz ho hG)

/-! ## The sheet minimum's burning rank, and the named Protected Web input -/

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

/-- **Q39 (the Protected Web Lemma), a named input until w2's lemma lands.** An unseeded forced edge `z → o` of `standardField word`
lifts, at every deck translate `z + v` that lies in the strict interior, to a forced edge of the sheet minimum inside the strict
interior, with the translated input `o + v`. -/
def Q39Hyp (word : Word) : Prop :=
  ∀ z o v : Site, v ∈ (frameAt word).child.modifiedDeck.span →
    W1.StrictInterior (frameAt word).child.num (frameAt word).child.den (z + v) →
    ForcedEdge (standardField word) (fun _ _ => False) z o →
    W1.ForcedEdgeIn ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))))
      (W1.StrictInterior (frameAt word).child.num (frameAt word).child.den) (fun _ _ => False) (z + v) (o + v)

/-! ## The passage reaches a free site, with the acyclic rank -/

/-- **The `K₊`-passage stops at a free site (Q36).** The acyclic rank of the passage is supplied by `passage_rank`, from the sheet
minimum's burning rank and the named Protected Web input `Q39Hyp`. -/
theorem plus_passage_free_Q36 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hQ39 : Q39Hyp word)
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kPlusW word z₀ ≤ kPlusW word w) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kPlusW word f = kPlusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
  obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (StripsM.hper_word h hSE)
    (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR hQ39
  exact FreeSchedule.plus_passage_free h hSE hPR hW hW1 hfort hz₀S hz₀E hmin
    ⟨ρ, fun z o _ hnz hG _ hno => hρ z o hnz hno hG⟩

/-- **The `K₋`-passage stops at a free site (Q36).** The same statement for `K₋`. -/
theorem minus_passage_free_Q36 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    (hQ39 : Q39Hyp word)
    {S : Set Site} (hfort : FortAt (Nonfree (frameAt word)) (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kMinusW word z₀ ≤ kMinusW word w) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kMinusW word f = kMinusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  obtain ⟨R, hR⟩ := sheetMin_burning_of_strong h hSE
  obtain ⟨ρ, hρ⟩ := passage_rank (frameAt word) (StripsM.hper_word h hSE)
    (fun s hs => standardField_eq_sheetMin_of_strong h hSE hs) hR hQ39
  exact FreeSchedule.minus_passage_free h hSE hPR hW hW1 hfort hz₀S hz₀E hmin
    ⟨ρ, fun z o _ hnz hG _ hno => hρ z o hnz hno hG⟩

end FLatticePaper.PassageRank
