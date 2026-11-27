import FLatticePaper.Plane.Induction.MinusRowPrefix
import FLatticePaper.Plane.Induction.WordDischarge
import FLatticePaper.Plane.Induction.WordVPattern
import FLatticePaper.Plane.Induction.WordBoundary
import FLatticePaper.Plane.Induction.SheetFort
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.OppWordCover
import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.EndpointRows
import FLatticePaper.Plane.Induction.W4Exceptional
import FLatticePaper.Plane.Induction.PsiMonoOffset
import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.FreeHWhite
import FLatticePaper.Plane.Induction.CapRayWide
import FLatticePaper.Plane.Induction.CapBaseN1
import FLatticePaper.Plane.Induction.MinusRowWiring
import FLatticePaper.Plane.Induction.NativeGrade
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.SheetFacts

/-! # The minus row up to its H block, with every hypothesis discharged at the word except the two traces

`TraceFromPsi.TraceAt word` (the word's own trace, for `hPH`) and `TraceAt (conjWord word)` (for the conjugate's V pattern) are
the inputs of the trace providers of the headline; everything else is proved from the word's strong core and seed fields. -/

namespace FLatticePaper.WordMinusEasy

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AuxRankQ1 FLatticePaper.FreeRows
  FLatticePaper.W1Seeds FLatticePaper.WordWebHyp FLatticePaper.WordVPattern FLatticePaper.WordDischarge

/-- **The odd band at the word**: the odd sites with `2 − 3d + n ≤ s ≤ 3d + n − 2` are harmonic. -/
theorem hO_word {word : Word} (hS : StrongCore word) (hpar : SeedFields word) :
    ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2 →
      standardField word z = harmonicGrid z := by
  intro z hz hlo hhi
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  rcases le_or_gt ((frameAt word).sGrade z) (1 - 2 * (frameAt word).child.den) with h1 | h1
  · exact OppWordCover.word_odd_lower hS hpar z hz hlo h1
  · rcases le_or_gt ((frameAt word).sGrade z) ((frameAt word).child.den + (frameAt word).child.num - 2) with h2 | h2
    · exact OppWordCover.word_strip hS z h1.le (by linarith)
    · exact OppWordCover.word_odd_upper hS hpar z hz h2 hhi

/-- **The minus V pattern at the word** (the rounded slip of the V labels for `η = -1`). -/
theorem hpat_minus_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hTrC : TraceFromPsi.TraceAt (conjWord word)) :
    ∀ k : ℕ, (k : ℤ) < (frameAt word).child.den + (frameAt word).child.num →
      (frameAt word).roundedSlip (standardField word) (-1) (VChain.vpath (frameAt word) k) =
        if (k : ℤ) ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num then 0 else -1 :=
  fun k hk => roundedSlip_minus_vpath hw hSE hTrC k hk

/-- **The H-boundary price at the word** (`hPH`), from the word's trace. -/
theorem hPH_word {word : Word} (hTr : TraceFromPsi.TraceAt word) :
    ∀ h : Site, (frameAt word).freeH h → (frameAt word).price (standardField word) h ≤ (frameAt word).cutPrice ∧
      ((frameAt word).price (standardField word) h = (frameAt word).cutPrice →
        h = FLatticePaper.Induction.hFirst) :=
  WordBoundary.hPH_of_trace hTr

/-- **The free H sites have zero rounded slip at the word** (`hJH` for `η = -1`). -/
theorem hJH_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∀ h : Site, (frameAt word).freeH h → (frameAt word).roundedSlip (standardField word) (-1) h = 0 :=
  fun _ hh => WordBoundary.roundedSlip_freeH_word hw hSE (Or.inr rfl) hh

/-- **The `H_0` and `V_0` whites at the word:** the laplacians at `(1,0)` and `(0,0)` vanish. -/
theorem hH0w_word {word : Word} (hS : StrongCore word) :
    laplacian (standardField word) ((1 : ℤ), (0 : ℤ)) = 0 :=
  laplacian_eq_zero_of_freeH (frameAt word) hS.packet.strips (FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt word))

theorem hV0w_word {word : Word} (hS : StrongCore word) :
    laplacian (standardField word) ((0 : ℤ), (0 : ℤ)) = 0 :=
  ChildFrame.laplacian_eq_zero_of_freeV (frame := frameAt word) hS.packet.strips
    (FLatticePaper.W4Exceptional.vFirst_mem_freeV (frameAt word))

/-- **The free prescription of `H_0` for `η = -1`** is `(1,1)`. -/
theorem hH0p_word {word : Word} (η : ℤ) (hη : η = -1) :
    ∀ i, FreePolicy.FreePresc (frameAt word) η ((1 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (1 : ℤ)) := by
  intro i
  have hm : FLatticePaper.Induction.hFirst ∈ (frameAt word).freeH :=
    FLatticePaper.PsiMonoOffset.hFirst_mem_freeH (frameAt word)
  have h := FreePolicy.freePresc_iff_H (frameAt word) η hm i
  have hp : (frameAt word).prescribedH η FLatticePaper.Induction.hFirst = (0, -η) :=
    (frameAt word).prescribedH_hFirst η
  rw [hp] at h
  show FreePolicy.FreePresc (frameAt word) η FLatticePaper.Induction.hFirst i ↔ i = ((1 : ℤ), (1 : ℤ))
  rw [h, hη]
  have hsum : FLatticePaper.Induction.hFirst + ((0 : ℤ), -(-1 : ℤ)) = ((1 : ℤ), (1 : ℤ)) := by
    norm_num [FLatticePaper.Induction.hFirst]
  rw [hsum]

/-- **The free prescription of `V_0`** is `(1,0)` for both signs. -/
theorem hV0p_word {word : Word} (η : ℤ) :
    ∀ i, FreePolicy.FreePresc (frameAt word) η ((0 : ℤ), (0 : ℤ)) i ↔ i = ((1 : ℤ), (0 : ℤ)) := by
  intro i
  have hm : FLatticePaper.Induction.vFirst ∈ (frameAt word).freeV :=
    W4Exceptional.vFirst_mem_freeV (frameAt word)
  have h := FreePolicy.freePresc_iff_V (frameAt word) η hm i
  have hp : (frameAt word).prescribedV η FLatticePaper.Induction.vFirst = ((1 : ℤ), (0 : ℤ)) :=
    EndpointRows.prescV00 η
  rw [hp] at h
  show FreePolicy.FreePresc (frameAt word) η FLatticePaper.Induction.vFirst i ↔ i = ((1 : ℤ), (0 : ℤ))
  rw [h]
  have hsum : FLatticePaper.Induction.vFirst + ((1 : ℤ), (0 : ℤ)) = ((1 : ℤ), (0 : ℤ)) := by
    norm_num [FLatticePaper.Induction.vFirst]
  rw [hsum]

/-- **The cap hypothesis of the H entries at the word**, with the `n = 1` and `n ≥ 3` cases (`CapBaseN1`, `CapRayWide`). -/
theorem cap_word {word : Word} (hS : StrongCore word) (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den) :
    ∀ K : ℕ, 3 ≤ K → (frameAt word).child.den + 2 * (frameAt word).child.num - 1 ≤ (frameAt word).child.num * (K : ℤ) →
      (frameAt word).child.num * (K : ℤ) ≤ (frameAt word).child.den + 3 * (frameAt word).child.num - 2 →
      ∃ p q : ℤ, (frameAt word).child.num * p - (frameAt word).child.den * q = 2 - (frameAt word).child.num ∧
        ∀ k : ℕ, k ≤ K → FLatticePaper.QuadraticCap.capMin k ≤ standardField word (p + (k : ℤ), q + (k : ℤ)) := by
  intro K hK3 hKs hKu
  obtain ⟨hn0, hnd', -, -, -⟩ := (frameAt word).child_facts
  obtain ⟨hn2, hd2⟩ := (frameAt word).child_odd
  have hsig := hsig_word hS
  rcases (show (frameAt word).child.num = 1 ∨ 3 ≤ (frameAt word).child.num by omega) with h1 | h3
  · exact CapBaseN1.hAS_n1 hS.packet hsig h1 K (by rw [h1] at hKu ⊢; omega)
  · exact CapRayWide.hAS_wide_of_proper hS.packet hsig h3 (by omega) K (by linarith)

/-- **The minus row up to its H block at the word.** Every site of the minus row before the V tail is outside a restricted fort
`S` for `permitsQ1 (frameAt word) (standardField word) (-1)` with the cut bound, for an easy word (`2n ≤ d`). -/
theorem minus_row_up_to_H_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongCore word)
    (hpar : SeedFields word) (hSE : StrongEstimates (conjWord word))
    (hTrW : TraceFromPsi.TraceAt word) (hTrC : TraceFromPsi.TraceAt (conjWord word))
    (hnd : 2 * (frameAt word).child.num ≤ (frameAt word).child.den)
    {S : Set Site}
    (hres : IsRestrictedFort (standardField word) (permitsQ1 (frameAt word) (standardField word) (-1)) S)
    (hK : ∀ z ∈ S, (frameAt word).cutPrice ≤ (frameAt word).price (standardField word) z +
      (frameAt word).roundedSlip (standardField word) (-1) z) :
    ∀ (k : ℕ) (e : Site), k < ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num).toNat + 2 +
        ((frameAt word).child.den - 1).toNat →
      (MinusRowWiring.minusSites (frameAt word) ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num))[k]? =
        some e → e ∉ S := by
  have hn1 : 1 ≤ (frameAt word).child.num := by
    obtain ⟨hn0, -, -, -, -⟩ := (frameAt word).child_facts
    omega
  have hNo : 1 ≤ (frameAt word).parents.odd.num := by
    have := frameAt_odd_num_pos hw
    omega
  exact MinusRowPrefix.minus_row_up_to_H_removed (frameAt word) (standardField word) hS.packet (hsig_word hS)
    (hZ2_word hS hpar) (hZ3_word hS hpar) hn1 hnd hNo (le_of_lt (brk_pos word)) (hrL2_word word) (cap_word hS hnd)
    (hpat_minus_word hw hSE hTrC) (hPH_word hTrW) (hJH_word hw hSE) (hO_word hS hpar) (M := W1MSheet.MW word)
    (SheetFort.sheetMin_recurrentField hw hSE) (fun s hs => standardField_eq_sheetMin_of_strong hw hSE hs)
    (hH0w_word hS) (hV0w_word hS) (hH0p_word (-1) rfl) (hV0p_word (-1)) hres hK

end FLatticePaper.WordMinusEasy
