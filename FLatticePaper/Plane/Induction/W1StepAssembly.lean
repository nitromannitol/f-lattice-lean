import FLatticePaper.StepHeadline
import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.HX12Strong
import FLatticePaper.Plane.Induction.LowerMem
import FLatticePaper.Plane.Induction.LowerBandStrong
import FLatticePaper.Plane.Induction.TopStrictDischarge
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.HderivClosed
import FLatticePaper.Plane.Induction.EvenWindow
import FLatticePaper.Plane.Induction.FreeRoutes
import FLatticePaper.Plane.Induction.RouteAssembly
import FLatticePaper.Plane.Induction.W1StepParts

/-! # The W1 step from the proved parts, with the open items as explicit hypotheses

`StepHeadline.W1Step` at a proper word `word` (not a two-power): the W1 forcing of the word, from the conjugate's strong estimates,
seeds, trace, games with a deck rank and W1 forcing. The engine is `CollarChain.W1Forced_end_to_end`; its inputs are wired here:
the route fields (`RouteAssembly.routeGenuine_of_parts`, through `FreeRoutes.hH_of_routes` and `hVodd_of_routes`), the four canonical
rules (`HderivClosed.hcanon_east` / `hcanon_west`), the strip and odd-band inputs of the standard field, and `hX1`, `hX2`, `hX3`
(`HX12Strong`, `LowerBandStrong`, `LowerMem`), and `hTop` (`TopStrictDischarge`).

The explicit hypotheses are the open items: `hQ37` (the `h3` middle target for `t ≤ d`), `hPbuild` (the ranked old policy of the
conjugate's canonical game, which is not yet built from the games), `hagree` (`TieAgreeHyp`), `hRow` (`RowStrictHyp`), `hPsi`
(`PsiFaceSign`), and `hthree` (the words whose conjugate is a pure power of threes, where the colour lemma of `hX3` does not apply). -/

namespace FLatticePaper.W1StepAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.StepHeadline FLatticePaper.W1NonfreeOut

theorem w1Step_of_parts
    (hQ37 : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → StrongEstimates (conjWord word) →
      ∀ z ∈ (frameAt (conjWord word)).freeH, EvenSite z → (z.1 - 1, z.2) ∈ (frameAt (conjWord word)).freeH →
        (frameAt (conjWord word)).tGrade z ≤ (frameAt (conjWord word)).child.den →
        laplacian (standardField (conjWord word)) (z.1, z.2 + 1) = 0)
    (hPbuild : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)),
        ∃ P : W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps,
          P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy)
    (hagree : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy → CollarChain.TieAgreeHyp word P)
    (hRow : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy →
          CollarChain.RowStrictHyp word (standardField (conjWord word)) P.retained)
    (hPsi : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → FaceWitness.PsiFaceSign word)
    (hthree : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      W1At word) :
    W1Step   := by
  intro word hproper _ _ _ _ hSE hpar _ hSE2 _ hGc hW1c
  by_cases hk : ∃ k : ℕ, conjWord word = List.replicate k Digit.three
  · exact hthree word hproper hk
  have hnot : ¬ ∃ k : ℕ, conjWord word = List.replicate k Digit.three := hk
  obtain ⟨G, -⟩ := hGc
  obtain ⟨P, hPret⟩ := hPbuild word hproper G
  have hη := (frameAt word).eps_unit
  obtain ⟨δ, hδη, hδ⟩ : ∃ δ : ℤ, (frameAt word).eps = -δ ∧ (δ = 1 ∨ δ = -1) :=
    ⟨-(frameAt word).eps, by ring, by omega⟩
  have hP := hSE.packet
  have hslipR := hSE.slipRange
  have hpriceR := hSE.priceRange
  have hdrift := hSE.priceDrift
  have hsig := W1StepParts.hsig_of_SE hP hslipR
  have hslip : ∀ z ∈ (frameAt (conjWord word)).closedPolygon, 0 ≤ (frameAt (conjWord word)).slip
      (standardField (conjWord word)) 1 z := fun z hz => (hslipR z hz).1
  have hIsym := FLatticePaper.W1Strips.standardField_iRefl hSE
  have hI : ∀ y : Site, standardField (conjWord word) (reflectionI - y) = standardField (conjWord word) y := by
    intro y
    have h := hIsym y
    rw [FLatticePaper.W1Strips.iRefl_eq_sub] at h
    exact h
  have hS : ∀ x : Site, 2 - 2 * (frameAt (conjWord word)).child.den ≤ (frameAt (conjWord word)).sGrade x →
      (frameAt (conjWord word)).sGrade x ≤ 2 * ((frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num) - 2 →
      standardField (conjWord word) x = harmonicGrid x := fun x h1 h2 =>
    hP.strips.2 x (by omega) (by omega)
  have hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num ≤
      (frameAt (conjWord word)).sGrade x → (frameAt (conjWord word)).sGrade x ≤
      3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 →
      standardField (conjWord word) x = harmonicGrid x := fun x hx h1 h2 => odd_band_conj hSE hpar x hx h1 h2
  have hcf := (frameAt (conjWord word)).child_facts
  have hlow : ∀ x : Site, ¬ EvenSite x → 2 - 3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num ≤
      (frameAt (conjWord word)).sGrade x → (frameAt (conjWord word)).sGrade x ≤ 1 - 2 * (frameAt (conjWord word)).child.den →
      standardField (conjWord word) x = harmonicGrid x := fun x hx h1 h2 => hO x hx h1 (by
        obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := hcf
        omega)
  have hup : ∀ x : Site, ¬ EvenSite x → (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 <
      (frameAt (conjWord word)).sGrade x → (frameAt (conjWord word)).sGrade x ≤
      3 * (frameAt (conjWord word)).child.den + (frameAt (conjWord word)).child.num - 2 →
      standardField (conjWord word) x = harmonicGrid x := fun x hx h1 h2 => hO x hx (by
        obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := hcf
        omega) h2
  have hdrU : ∀ z, (frameAt (conjWord word)).price (standardField (conjWord word))
      (z + (frameAt (conjWord word)).child.modifiedDeck.kernel) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z - 1 := fun z => by
    linarith [(hdrift z).1]
  have hdrV : ∀ z, (frameAt (conjWord word)).price (standardField (conjWord word))
      (z + (frameAt (conjWord word)).child.modifiedDeck.transverse) =
      (frameAt (conjWord word)).price (standardField (conjWord word)) z := fun z => by
    linarith [(hdrift z).2]
  have hRoute := RouteAssembly.routeGenuine_of_parts (G.game (frameAt word).eps hη) hη hP hW1c
    (G.deckEquiv (frameAt word).eps hη) hP.binary P.toOldPolicyWitness hPret (fun _ _ h => h) hsig
    (W1StepParts.hAS_all hP hsig) (W1StepParts.hsym_of_iRefl hP hIsym) (W1StepParts.hper_of_packet hP) hslip
    hpar.even_zero hIsym hlow hup (hQ37 word hproper hSE) hpriceR hdrU hdrV (W1StepParts.perK_of_packet hP)
  have hH : ∀ z ∈ (frameAt (conjWord word)).freeH, laplacian (standardField (conjWord word)) z = 0 →
      W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hw
    rw [hPret]
    exact FreeRoutes.hH_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hw
  have hVodd : ∀ z ∈ (frameAt (conjWord word)).freeV, ¬ EvenSite z →
      laplacian (standardField (conjWord word)) z = 0 → W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hodd hw
    rw [hPret]
    exact FreeRoutes.hVodd_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hodd hw
  have hδz' : ∀ z : Site, ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → (δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) := by
    intro z hδz
    by_cases hd : δ = 1
    · exact Or.inl hd
    · right
      rcases hδz with h | h
      · omega
      · exact h
  have hX1 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2)) := fun z hz hev hzF hδz _ =>
    hX1_of_strong hSE hz hev hzF hδ (hδz' z hδz)
  have hX2 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 ∨
        (laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = 0 ∧
          Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2 - δ)) := fun z hz hev hzF hδz _ =>
    hX2_of_strong hSE hz hev hzF hδ (hδz' z hδz)
  have hX3 : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      (z.1, z.2 - δ) ∈ (frameAt (conjWord word)).freeV ∧
        laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0 := fun z hz hev hzF hδz _ =>
    ⟨(frameAt (conjWord word)).lower_mem_freeV hz hev hzF hδ (hδz' z hδz),
      lap_lower_of_strong hnot hSE2 hz hev hzF hδ (hδz' z hδz)⟩
  have hcanon : ∀ z ∈ (frameAt (conjWord word)).freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst →
      ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) → laplacian (standardField (conjWord word)) z = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 →
      laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 →
      P.retained (z.1 + δ, z.2) (z.1 + δ, z.2 - δ) := by
    rcases hδ with rfl | rfl
    · intro z hz hev hzF hδz hw hw1 hw2
      exact HderivClosed.hcanon_east (G.game (frameAt word).eps hη) P.toOldPolicyWitness hPret hP hpriceR hdrU hdrV
        hW1c (W1StepParts.perK_of_packet hP) hI hS hO z hz hev hzF hδz hw hw1 hw2
    · intro z hz hev hzF hδz hw hw1 hw2
      have hη1 : (frameAt word).eps = 1 := by omega
      exact HderivClosed.hcanon_west (G.game (frameAt word).eps hη) P.toOldPolicyWitness hPret hη1 hP hpriceR hdrU hdrV
        hW1c (W1StepParts.perK_of_packet hP) hI hS hO z hz hev hzF hδz hw hw1 hw2
  have hTop := TopStrictDischarge.topStrictHyp_of_packet hproper hSE
  have hn3 := FLatticePaper.Induction.child_num_ge_three hproper
  have hE := CollarChain.W1Forced_end_to_end (word := word) hproper hSE P rfl hW1c hn3 δ hδη hδ G hPret hH hVodd hX3 hX1 hX2
    hcanon hTop (hRow word hproper G P hPret) (hPsi word hproper) (hagree word hproper G P hPret)
  exact W1Bridge.W1Forced_standardField_of_MW word hproper hSE hE

end FLatticePaper.W1StepAssembly
