import FLatticePaper.StepHeadline
import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.HX12Strong
import FLatticePaper.Plane.Induction.LowerMem
import FLatticePaper.Plane.Induction.TopStrictDischarge
import FLatticePaper.Plane.Induction.W1Bridge
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.HderivClosed
import FLatticePaper.Plane.Induction.EvenWindow
import FLatticePaper.Plane.Induction.FreeRoutes
import FLatticePaper.Plane.Induction.RouteAssembly
import FLatticePaper.Plane.Induction.W1StepParts
import FLatticePaper.Plane.Induction.PsiPacket
import FLatticePaper.Plane.Induction.OldPolicyBuild
import FLatticePaper.Plane.Induction.WestClose
import FLatticePaper.Plane.Induction.TieAgreeClose
import FLatticePaper.Plane.Induction.FreeInStep

/-! # The W1 step from the proved parts, with the open items as explicit hypotheses

`StepHeadline.W1Step` at a proper word `word`: the W1 forcing of the word, from the conjugate's strong estimates, seeds, trace, games
with a deck rank and W1 forcing. The engine is `CollarChain.W1Forced_end_to_end`; its inputs are wired here: the route fields
(`RouteAssembly.routeGenuine_of_parts`, through `FreeRoutes.hH_of_routes` and `hVodd_of_routes`), the ranked old policy of the
canonical game (`OldPolicyBuild.oldPolicyRanked_of_games`), the canonical rules by sign (`HderivClosed.hcanon_east` / `hcanon_west`),
the strip and odd-band inputs of the standard field, `hX1`, `hX2` (`HX12Strong`), `hX3` (`LowerMem` and the strips of the conjugate),
and `hTop` (`TopStrictDischarge`).

`TieAgreeHyp` is no longer an input: it is `TieAgreeClose.tieAgreeHyp_of_routes`, from the route data above. The explicit hypothesis is the open item `hRow` (`RowStrictHyp`); `hFreeIn` is `FreeInStep.hFreeIn_of_strong`. `PsiFaceSign` is `PsiPacket.psiFaceSign_of_packet`. -/

namespace FLatticePaper.W1StepAssembly

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1 FLatticePaper.StepHeadline FLatticePaper.W1NonfreeOut
  FLatticePaper.AndOrRank FLatticePaper.SquareClauses FLatticePaper.W1Witness FLatticePaper.W1Phase

theorem w1Step_of_parts
    (hRow : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy →
          CollarChain.RowFaceStrictHyp word (standardField (conjWord word)) P.retained)
    (hDich : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → CollarChain.WitnessDichotomy word) :
    W1Step := by
  intro word hproper _ hcore hseed _ hSE hpar _ _ _ hGc hW1c
  obtain ⟨G, hGr⟩ := hGc
  have hη := (frameAt word).eps_unit
  obtain ⟨R, cU, cV, hRU, hRV, hR⟩ := hGr (frameAt word).eps hη
  have hF : ∀ z, standardField (conjWord word) (reflectionI - z) = standardField (conjWord word) z := by
    intro z
    have h := FLatticePaper.W1Strips.standardField_iRefl hSE z
    rw [FLatticePaper.W1Strips.iRefl_eq_sub] at h
    exact h
  let P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
      (frameAt word).eps :=
    OldPolicyBuild.oldPolicyRanked_of_games hSE.packet hF G (frameAt word).eps hη R cU cV hRU hRV hR
      hW1c (fun c i o h _ ho hfo _ => FreeInStep.hFreeIn_of_strong hSE hpar c i o h ho hfo)
  have hPret : P.retained = (G.game (frameAt word).eps hη).policy := rfl
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
  have hI : ∀ y : Site, standardField (conjWord word) (reflectionI - y) = standardField (conjWord word) y := hF
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
    hpar.even_zero hIsym hlow hup hpriceR hdrU hdrV (W1StepParts.perK_of_packet hP)
  have hH : ∀ z ∈ (frameAt (conjWord word)).freeH, laplacian (standardField (conjWord word)) z = 0 →
      W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hw
    rw [hPret]
    exact FreeRoutes.hH_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hw
  have hVodd : ∀ z ∈ (frameAt (conjWord word)).freeV, ¬ EvenSite z →
      laplacian (standardField (conjWord word)) z = 0 →
      W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hodd hw
    rw [hPret]
    exact FreeRoutes.hVodd_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hodd hw
  have hδz' : ∀ z : Site, ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      (δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) := by
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
      (frameAt (conjWord word)).lap_lower_eq_zero (fun x h1 h2 => hP.strips.2 x (by omega) (by omega)) hz hev hzF hδ
        (hδz' z hδz)⟩
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
    hcanon hTop (hRow word hproper G P hPret) (hDich word hproper) (FLatticePaper.PsiPacket.psiFaceSign_of_packet hproper hcore hseed hSE hpar hn3) (TieAgreeClose.tieAgreeHyp_of_routes hproper hSE P rfl hW1c G hPret hRoute δ hδη hδ hX3 hX1 hX2 hcanon)
  exact W1Bridge.W1Forced_standardField_of_MW word hproper hSE hE


theorem westFree_of_parts
    (hRow : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) →
      ∀ (G : CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word)))
        (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
          (frameAt word).eps),
        P.retained = (G.game (frameAt word).eps (frameAt word).eps_unit).policy →
          CollarChain.RowFaceStrictHyp word (standardField (conjWord word)) P.retained)
    (hDich : ∀ word : Word, (∃ x ∈ word, x ≠ Digit.three) → CollarChain.WitnessDichotomy word)
    (word : Word) (hproper : ∃ x ∈ word, x ≠ Digit.three) (hcore : StrongCore word) (hseed : FLatticePaper.W1Seeds.SeedFields word)
    (hSE : StrongEstimates (conjWord word)) (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word))
    (hGc : FLatticePaper.Induction.GamesWithRank (conjWord word))
    (hW1c : FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)))
    (hsat : FLatticePaper.Induction.HasSatSelection (standardField word)) (η : ℤ) :
    (frameAt word).eps = 1 → FreePolicy.freePolicy (frameAt word) (standardField word) η
      ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)
      (incomingNeg ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1)) := by
  intro heps
  obtain ⟨G, hGr⟩ := hGc
  have hη := (frameAt word).eps_unit
  obtain ⟨R, cU, cV, hRU, hRV, hR⟩ := hGr (frameAt word).eps hη
  have hF : ∀ z, standardField (conjWord word) (reflectionI - z) = standardField (conjWord word) z := by
    intro z
    have h := FLatticePaper.W1Strips.standardField_iRefl hSE z
    rw [FLatticePaper.W1Strips.iRefl_eq_sub] at h
    exact h
  let P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) (fun _ _ => False)
      (frameAt word).eps :=
    OldPolicyBuild.oldPolicyRanked_of_games hSE.packet hF G (frameAt word).eps hη R cU cV hRU hRV hR
      hW1c (fun c i o h _ ho hfo _ => FreeInStep.hFreeIn_of_strong hSE hpar c i o h ho hfo)
  have hPret : P.retained = (G.game (frameAt word).eps hη).policy := rfl
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
  have hI : ∀ y : Site, standardField (conjWord word) (reflectionI - y) = standardField (conjWord word) y := hF
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
    hpar.even_zero hIsym hlow hup hpriceR hdrU hdrV (W1StepParts.perK_of_packet hP)
  have hH : ∀ z ∈ (frameAt (conjWord word)).freeH, laplacian (standardField (conjWord word)) z = 0 →
      W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hw
    rw [hPret]
    exact FreeRoutes.hH_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hw
  have hVodd : ∀ z ∈ (frameAt (conjWord word)).freeV, ¬ EvenSite z →
      laplacian (standardField (conjWord word)) z = 0 →
      W1NonfreeOut.ParentSquareOut (standardField (conjWord word)) P.retained z := by
    intro z hz hodd hw
    rw [hPret]
    exact FreeRoutes.hVodd_of_routes (G.game (frameAt word).eps hη) hη hP (G.deckEquiv (frameAt word).eps hη) hRoute z hz hodd hw
  have hδz' : ∀ z : Site, ((frameAt word).eps = -1 ∨ z ≠ (frameAt (conjWord word)).vLast) →
      (δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) := by
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
      (frameAt (conjWord word)).lap_lower_eq_zero (fun x h1 h2 => hP.strips.2 x (by omega) (by omega)) hz hev hzF hδ
        (hδz' z hδz)⟩
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
  have hdeck := FLatticePaper.ChainWire.deck_of_games G hη P.toOldPolicyWitness hPret
  have hfree : ∀ c : Site, 0 ≤ FLatticePaper.W1Step.sheetPsi word c → laplacian (FLatticePaper.W1MSheet.MW word) c = 0 →
      ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
      ParentSquareOut (standardField (conjWord word)) P.retained (zTurn (c - (frameAt word).sheetShift)) :=
    fun c h0 hM hnf =>
      FLatticePaper.ChainWire.hfree_of_classes hδη hδ hSE.packet hW1c (G.game (frameAt word).eps hη)
        P.toOldPolicyWitness hPret hdeck hH hVodd hX3 hX1 hX2 hcanon hnf
        (FLatticePaper.W1NonfreeHsqC.lapG_zero_of_nonneg hproper hSE h0 hM)
  have hPsi := FLatticePaper.PsiPacket.psiFaceSign_of_packet hproper hcore hseed hSE hpar hn3
  have hagree := TieAgreeClose.tieAgreeHyp_of_routes hproper hSE P rfl hW1c G hPret hRoute δ hδη hδ hX3 hX1 hX2 hcanon
  have hcollar : ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (FLatticePaper.W1MSheet.MW word) c = 0 → FLatticePaper.W1CollarFrame.CollarFrame (frameAt word) c →
      FLatticePaper.W1NonfreeHsqNonneg.HsqAt word P c := by
    intro c hcS hM hcoll
    by_cases h0 : 0 ≤ FLatticePaper.W1Step.sheetPsi word c
    · exact FLatticePaper.CollarChain.hcollar_A hproper hSE P rfl hW1c G hPret hTop (hRow word hproper G P hPret)
        hfree hPsi hagree (hDich word hproper) c hcS hM h0 hcoll
    · exact FLatticePaper.CollarChain.hC_of_inputs hproper hSE P rfl hW1c G hPret hTop (hRow word hproper G P hPret)
        hfree hPsi (hDich word hproper) c hcS hM hcoll (by omega)
  exact FLatticePaper.WestClose.westAtException_of_routes hproper hSE hcore P rfl hW1c G hPret heps hfree hcollar hsat η

end FLatticePaper.W1StepAssembly
