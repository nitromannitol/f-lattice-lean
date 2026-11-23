import FLatticePaper.Plane.Induction.MinPassage
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! # The free-site steps of the schedule (task 107): the passage stops at a free site, and the ordered removals

* `ordered_removal`: a row `ent 0, …, ent (N−1)` of sites in which each entry lying in a fort forces an earlier entry in the fort (or
  is excluded by its own step) has no entry in the fort. This is the ordering argument of the free removals (Q1, the two lists).
* `reach_nonfree`: along a successor relation whose rank strictly decreases between nonfree valid points, a valid nonfree point reaches a
  valid point that is not nonfree (the passage stops at the first free site).
* `plus_passage_free`, `minus_passage_free`: for a fort `S` of `standardField word`, a minimum `z₀` of `K₊` (resp. `K₋`) over `S` in the
  closed polygon gives a point of `S` in the closed polygon with the same `K` that is not nonfree, i.e. a free site up to the deck. The
  successor is an input (the forced input of a white, the black input of a black), from `minK_white_forced_plus/minus` and
  `minK_black_input_plus/minus`; the rank is the acyclicity of the finite bulk quotient, named as the hypothesis `hrank`.
* `hMidpoints`, `vMidpoints` and their parity parts: the internal free sites (the free traces without their two endpoints), the fan starts of
  ALL_SLOPE_STEP.

Not here: the per-entry fan step (an entry in the fort gives an earlier entry or a lower value), the deck covariance that transports a free
site `f + v` of the orbit to the row, and the coverage of the free sites by the row. These are named inputs of the row instance. -/

namespace FLatticePaper.FreeSchedule

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.KMinBridge FLatticePaper.MinPassage FLatticePaper.TransferW1

/-- **Ordered removal.** If each entry `ent k` (`k < N`) that lies in `S` forces an earlier entry in `S`, or is excluded by its own step,
then no entry of the row lies in `S`. -/
theorem ordered_removal (S : Set Site) (ent : ℕ → Site) (N : ℕ)
    (hstep : ∀ k < N, ent k ∈ S → (∀ j < k, ent j ∉ S) → False) :
    ∀ k < N, ent k ∉ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    exact hstep k hk hmem (fun j hj => ih j hj (lt_trans hj hk))

/-- **The passage reaches a free site.** Along a successor relation `Step` on the valid points, a valid nonfree point has a valid
successor; if the rank strictly decreases between nonfree valid points, some valid point reached from it is not nonfree. -/
theorem reach_nonfree {α : Type*} (valid nf : α → Prop) (Step : α → α → Prop)
    (hsucc : ∀ z, valid z → nf z → ∃ o, Step z o ∧ valid o)
    (hrank : ∃ ρ : α → ℕ, ∀ z o, valid z → nf z → Step z o → valid o → nf o → ρ o < ρ z) :
    ∀ z0, valid z0 → nf z0 → ∃ f, valid f ∧ ¬ nf f := by
  obtain ⟨ρ, hρ⟩ := hrank
  suffices H : ∀ n : ℕ, ∀ z, ρ z ≤ n → valid z → nf z → ∃ f, valid f ∧ ¬ nf f from
    fun z0 hv hn => H (ρ z0) z0 le_rfl hv hn
  intro n
  induction n with
  | zero =>
    intro z hz hv hn
    obtain ⟨o, hS, hvo⟩ := hsucc z hv hn
    by_cases hno : nf o
    · have := hρ z o hv hn hS hvo hno
      omega
    · exact ⟨o, hvo, hno⟩
  | succ n ih =>
    intro z hz hv hn
    obtain ⟨o, hS, hvo⟩ := hsucc z hv hn
    by_cases hno : nf o
    · exact ih o (by have := hρ z o hv hn hS hvo hno; omega) hvo hno
    · exact ⟨o, hvo, hno⟩

/-- **The `K₊`-passage stops at a free site.** Let `z₀` be a minimum of `K₊` over the fort `S`, in the closed polygon. Then there is a point
of `S` in the closed polygon with the same `K₊` that is not nonfree (a free site up to the deck). The rank `hrank` is the acyclicity of the
finite bulk quotient of the passage. -/
theorem plus_passage_free {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : IsIncomingFort (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kPlusW word z₀ ≤ kPlusW word w)
    (hrank : ∃ ρ : Site → ℕ, ∀ z o, (z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kPlusW word z = kPlusW word z₀) →
      Nonfree (frameAt word) z → (o = incomingNeg z ∨ o = incomingPos z) →
      (o ∈ S ∧ o ∈ (frameAt word).closedPolygon ∧ kPlusW word o = kPlusW word z₀) → Nonfree (frameAt word) o →
      ρ o < ρ z) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kPlusW word f = kPlusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  by_cases hnf₀ : Nonfree (frameAt word) z₀
  · have hpk := packet_of_strong h hSE
    obtain ⟨f, ⟨hfS, hfE, hfK⟩, hfn⟩ := reach_nonfree
      (fun z => z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kPlusW word z = kPlusW word z₀)
      (fun z => Nonfree (frameAt word) z)
      (fun z o => o = incomingNeg z ∨ o = incomingPos z)
      (by
        intro z hv hnfz
        obtain ⟨hzS, hzE, hzK⟩ := hv
        have hSI := nonfree_strictInterior (frameAt word) hzE hnfz
        have hstar := strictInterior_star (frameAt word) hSI
        have hminz : ∀ w ∈ S, kPlusW word z ≤ kPlusW word w := fun w hw => by
          rw [hzK]
          exact hmin w hw
        rcases hpk.binary z with hb | hb
        · obtain ⟨i, hi, hiS, hiK⟩ := minK_black_input_plus h hSE hPR hpk hfort hzS hzE hb hminz
          have hiE : i ∈ (frameAt word).closedPolygon := by
            rcases hi with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          exact ⟨i, hi, ⟨hiS, hiE, by rw [hiK, hzK]⟩⟩
        · obtain ⟨o', hf'⟩ := hW1 z hSI hb
          have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
          have hio := forced_input_of_unseeded hf
          have hoE : o' ∈ (frameAt word).closedPolygon := by
            rcases hio with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          obtain ⟨hoS, hoK⟩ := minK_white_forced_plus h hSE hPR hW hW1 hfort hzS hzE hnfz hb hf hoE hminz
          exact ⟨o', hio, ⟨hoS, hoE, by rw [hoK, hzK]⟩⟩)
      hrank z₀ ⟨hz₀S, hz₀E, rfl⟩ hnf₀
    exact ⟨f, hfS, hfE, hfK, hfn⟩
  · exact ⟨z₀, hz₀S, hz₀E, rfl, hnf₀⟩

/-- **The `K₋`-passage stops at a free site**: the same statement for `K₋ = P + J₋`, with the black and white steps of `K₋`. -/
theorem minus_passage_free {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hPR : FLatticePaper.PassagePR.PriceRangeOn word)
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {S : Set Site} (hfort : IsIncomingFort (standardField word) S) {z₀ : Site} (hz₀S : z₀ ∈ S)
    (hz₀E : z₀ ∈ (frameAt word).closedPolygon)
    (hmin : ∀ w ∈ S, kMinusW word z₀ ≤ kMinusW word w)
    (hrank : ∃ ρ : Site → ℕ, ∀ z o, (z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kMinusW word z = kMinusW word z₀) →
      Nonfree (frameAt word) z → (o = incomingNeg z ∨ o = incomingPos z) →
      (o ∈ S ∧ o ∈ (frameAt word).closedPolygon ∧ kMinusW word o = kMinusW word z₀) → Nonfree (frameAt word) o →
      ρ o < ρ z) :
    ∃ f, f ∈ S ∧ f ∈ (frameAt word).closedPolygon ∧ kMinusW word f = kMinusW word z₀ ∧ ¬ Nonfree (frameAt word) f := by
  by_cases hnf₀ : Nonfree (frameAt word) z₀
  · have hpk := packet_of_strong h hSE
    obtain ⟨f, ⟨hfS, hfE, hfK⟩, hfn⟩ := reach_nonfree
      (fun z => z ∈ S ∧ z ∈ (frameAt word).closedPolygon ∧ kMinusW word z = kMinusW word z₀)
      (fun z => Nonfree (frameAt word) z)
      (fun z o => o = incomingNeg z ∨ o = incomingPos z)
      (by
        intro z hv hnfz
        obtain ⟨hzS, hzE, hzK⟩ := hv
        have hSI := nonfree_strictInterior (frameAt word) hzE hnfz
        have hstar := strictInterior_star (frameAt word) hSI
        have hminz : ∀ w ∈ S, kMinusW word z ≤ kMinusW word w := fun w hw => by
          rw [hzK]
          exact hmin w hw
        rcases hpk.binary z with hb | hb
        · obtain ⟨i, hi, hiS, hiK⟩ := minK_black_input_minus h hSE hPR hpk hfort hzS hzE hb hminz
          have hiE : i ∈ (frameAt word).closedPolygon := by
            rcases hi with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          exact ⟨i, hi, ⟨hiS, hiE, by rw [hiK, hzK]⟩⟩
        · obtain ⟨o', hf'⟩ := hW1 z hSI hb
          have hf := FLatticePaper.W1.forcedEdgeIn_forced hf'
          have hio := forced_input_of_unseeded hf
          have hoE : o' ∈ (frameAt word).closedPolygon := by
            rcases hio with rfl | rfl
            · exact hstar.2.1
            · exact hstar.2.2
          obtain ⟨hoS, hoK⟩ := minK_white_forced_minus h hSE hPR hW hW1 hfort hzS hzE hnfz hb hf hoE hminz
          exact ⟨o', hio, ⟨hoS, hoE, by rw [hoK, hzK]⟩⟩)
      hrank z₀ ⟨hz₀S, hz₀E, rfl⟩ hnf₀
    exact ⟨f, hfS, hfE, hfK, hfn⟩
  · exact ⟨z₀, hz₀S, hz₀E, rfl, hnf₀⟩

/-! ## The midpoint sets (step (4)): the internal free sites of the two traces -/

/-- The internal free H sites: the free H trace without its two ends `H_0 = (1,0)` and `H_{d−1}`. -/
def hMidpoints (frame : ChildFrame) : Set Site :=
  {z | z ∈ frame.freeH ∧ z ≠ hFirst ∧ z ≠ frame.hLast}

/-- The internal free V sites: the free V cut without its two ends `V_0 = (0,0)` and `V_{L−1}`. -/
def vMidpoints (frame : ChildFrame) : Set Site :=
  {z | z ∈ frame.freeV ∧ z ≠ vFirst ∧ z ≠ frame.vLast}

/-- The odd internal H midpoints: the fan starts with a north input (ALL_SLOPE_STEP). -/
def hMidOdd (frame : ChildFrame) : Set Site :=
  {z | z ∈ hMidpoints frame ∧ ¬ EvenSite z}

/-- The even internal V midpoints: the low-slope fan starts (ALL_SLOPE_STEP). -/
def vMidEven (frame : ChildFrame) : Set Site :=
  {z | z ∈ vMidpoints frame ∧ EvenSite z}

theorem hMidOdd_subset (frame : ChildFrame) : hMidOdd frame ⊆ frame.freeH :=
  fun _ hz => hz.1.1

theorem vMidEven_subset (frame : ChildFrame) : vMidEven frame ⊆ frame.freeV :=
  fun _ hz => hz.1.1

end FLatticePaper.FreeSchedule
