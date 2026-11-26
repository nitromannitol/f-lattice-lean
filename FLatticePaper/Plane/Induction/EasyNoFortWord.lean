import FLatticePaper.Plane.Induction.EasyNoFort
import FLatticePaper.Plane.Induction.WordBoundary
import FLatticePaper.Plane.Induction.Q30Strips
import FLatticePaper.Plane.Induction.TraceStep
import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.TieReduce

/-! # The easy-frame `RestrictedNoFort` at the game's own word

The word frame `frameAt word` with the field `standardField word`. The data of the reduction in `EasyNoFort` are supplied as follows:
* the packet, the deck drifts of `P` and `J` (`ChildFrame.price_kernel`, `price_transverse`, `slip_kernel`, `slip_transverse` from the
  generator periods `StripsM.hper_word`);
* the strips `hS`, `hO` (`Q30Strips.hstrip_of_strong`, `hodd_of_strong`);
* `hPH` (`WordBoundary.hPH_of_trace`) and `hJH` (`WordBoundary.roundedSlip_freeH_word`).

Named inputs that remain: the trace `TraceAt word` (for `hPH`), the seeds `SeedFields word` (for `hO`), the V pattern `hpat` with its
break `r`, the confinement `hconf`, and the H₀-core `hcore`. The easy-frame condition `2 num ≤ den` is `hd`. -/

namespace FLatticePaper.EasyNoFortWord

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.EasyNoFort

/-- **`RestrictedNoFort` for `permitsQ1` at sign `−1`, at the game's word, on the easy frames.** -/
theorem restrictedNoFort_minus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hTr : TraceFromPsi.TraceAt word)
    (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (r : ℤ) (hr0 : 0 ≤ r) (hrL2 : r ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ r then 0 else -1)
    (hconf : ∀ S : Set Site, IsRestrictedFort (standardField word) (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) (-1)) S →
      (∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) (-1) z) →
      ∀ z ∈ S, z ∈ (frameAt word).closedPolygon)
    (hcore : ∀ S : Set Site, IsRestrictedFort (standardField word)
        (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) (-1)) S →
      (∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) (-1) z) →
      (∀ z ∈ S, z ∈ (frameAt word).closedPolygon) →
      (∀ z ∈ S, ¬ (frameAt word).openRect z → z = hFirst ∨ z = vFirst) → S = ∅) :
    RestrictedNoFort (standardField word)
      (fun z => (frameAt word).price (standardField word) z + (frameAt word).roundedSlip (standardField word) (-1) z)
      (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) (-1)) := by
  have hP := packet_of_strong hw hSE
  have hper := StripsM.hper_word hw hSE
  have hbd := TraceStep.hbd_of_traceAt hw hSE hTr
  refine restrictedNoFort_minus (frameAt word) hP ?_ ?_ r hr0 hrL2
    (WordBoundary.hPH_of_trace hTr) (fun h hh => WordBoundary.roundedSlip_freeH_word hw hSE (η := -1) (by norm_num) hh)
    hpat (Q30Strips.hstrip_of_strong hw hSE) (Q30Strips.hodd_of_strong hw hSE hbd hseed) hd hconf hcore
  · intro z
    exact ⟨by linarith [(frameAt word).price_kernel (standardField word) hper z],
      by linarith [(frameAt word).price_transverse (standardField word) hper z]⟩
  · intro z
    exact ⟨by linarith [(frameAt word).slip_kernel (standardField word) hper (-1) z],
      by linarith [(frameAt word).slip_transverse (standardField word) hper (-1) z]⟩

/-- **`RestrictedNoFort` for `permitsQ1` at sign `+1`, at the game's word, on the easy frames.** -/
theorem restrictedNoFort_plus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hTr : TraceFromPsi.TraceAt word)
    (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (r : ℤ) (hr0 : 0 ≤ r) (hr2 : r ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (hd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    (hpat : ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) 1 (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ (frameAt word).child.den + (frameAt word).child.num - r - 2 then 0 else 1)
    (hconf : ∀ S : Set Site, IsRestrictedFort (standardField word) (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) 1) S →
      (∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) 1 z) →
      ∀ z ∈ S, (z.1 + ((frameAt word).child.num - (frameAt word).child.den),
        z.2 + ((frameAt word).child.num + (frameAt word).child.den)) ∈ (frameAt word).closedPolygon)
    (hcore : ∀ S : Set Site, IsRestrictedFort (standardField word)
        (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) 1) S →
      (∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
        (frameAt word).roundedSlip (standardField word) 1 z) →
      (∀ z ∈ S, (z.1 + ((frameAt word).child.num - (frameAt word).child.den),
        z.2 + ((frameAt word).child.num + (frameAt word).child.den)) ∈ (frameAt word).closedPolygon) →
      (∀ z ∈ S, ¬ (frameAt word).openRect (z.1 + ((frameAt word).child.num - (frameAt word).child.den),
        z.2 + ((frameAt word).child.num + (frameAt word).child.den)) →
        z = hFirst ∨ z = RowAt.vAt (frameAt word) (-1)) → S = ∅) :
    RestrictedNoFort (standardField word)
      (fun z => (frameAt word).price (standardField word) z + (frameAt word).roundedSlip (standardField word) 1 z)
      (AuxRankQ1.permitsQ1 (frameAt word) (standardField word) 1) := by
  have hP := packet_of_strong hw hSE
  have hper := StripsM.hper_word hw hSE
  have hbd := TraceStep.hbd_of_traceAt hw hSE hTr
  refine restrictedNoFort_plus (frameAt word) hP ?_ ?_ r hr0 hr2
    (WordBoundary.hPH_of_trace hTr) (fun h hh => WordBoundary.roundedSlip_freeH_word hw hSE (η := 1) (by norm_num) hh)
    hpat (Q30Strips.hstrip_of_strong hw hSE) (Q30Strips.hodd_of_strong hw hSE hbd hseed) hd hconf hcore
  · intro z
    exact ⟨by linarith [(frameAt word).price_kernel (standardField word) hper z],
      by linarith [(frameAt word).price_transverse (standardField word) hper z]⟩
  · intro z
    exact ⟨by linarith [(frameAt word).slip_kernel (standardField word) hper 1 z],
      by linarith [(frameAt word).slip_transverse (standardField word) hper 1 z]⟩

end FLatticePaper.EasyNoFortWord
