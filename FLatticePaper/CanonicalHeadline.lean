import FLatticePaper.StrongHeadline
import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.EPolicyFinal
import FLatticePaper.Plane.Induction.StrongSeedInduction
import FLatticePaper.Plane.Induction.GamesPolicy
import FLatticePaper.Plane.Induction.TwosResidual
import FLatticePaper.Plane.Induction.HResPWire
import FLatticePaper.Plane.Induction.HResNCases
import FLatticePaper.Plane.Induction.TwosGames
import FLatticePaper.Plane.Induction.W1Reciprocal
import FLatticePaper.Plane.Induction.NegTieHCutFinal

/-! Task 71: the odometers headline with the canonical signed games at every proper word.

One input `hgames` supplies, at each proper non-two-power word `w`, the canonical signed games of `w` together with a strict deck rank for
each sign (`GamesWithRank w`). From it the policy inputs of `hpol` at `w` (`policy_of_gamesWithRank`) and the canonical games of the conjugate
`conjWord w` (`hcan`) follow: the conjugate of a pure threes word is covered by `pure_threes_final`, the conjugate of a twos word `2^(k+1)` by
the input `htwoGames`, and every other conjugate is a proper non-two-power word, covered by `hgames`. -/

namespace FLatticePaper

open Farey Induction

/-- The reflection of the standard field of a conjugate word, from its strong estimates (`standardField_iRefl`): `F (I − z) = F z`. -/
theorem standardField_reflectI_conj (word : Word) (h : Induction.StrongEstimates (conjWord word)) (z : Site) :
    standardField (conjWord word) (reflectionI - z) = standardField (conjWord word) z := by
  have := FLatticePaper.W1Strips.standardField_iRefl h z
  rw [FLatticePaper.W1Strips.iRefl_eq_sub] at this
  exact this

/-- The canonical signed games at the conjugate of a pure threes word, from `pure_threes_final` (`reciprocalFrame k` is
`frameAt (3^k)` and `standardField_threes` identifies the field). -/
theorem canonical_at_threes (word : Word) (hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three) :
    Nonempty (Induction.CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word))) := by
  obtain ⟨k, hk⟩ := hp
  have hf : frameAt (conjWord word) = reciprocalFrame k := by
    rw [hk]
    try rfl
  have hF : standardField (conjWord word) = reciprocalField k := by
    rw [hk, standardField_threes]
  rw [hf, hF]
  exact FLatticePaper.EPolicy.pure_threes_final.2.2 k

/-- The conjugate `W1Forced` at a pure threes conjugate, from `w1Forced_threes` (the child of `3^k` is `1/(2k+3)`). -/
theorem w1Forced_at_threes (word : Word) (hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three) :
    FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
      (standardField (conjWord word)) := by
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  exact FLatticePaper.W1Reciprocal.w1Forced_threes k

/-- A word that is not a pure threes word has a digit other than `three`. -/
theorem exists_ne_three_of_not_replicate_three (w : Word) (h : ¬ ∃ k : ℕ, w = List.replicate k Digit.three) :
    ∃ x ∈ w, x ≠ Digit.three := by
  by_contra hc
  apply h
  refine ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩⟩
  by_contra hne
  exact hc ⟨b, hb, hne⟩

/-- **The odometers theorem from the canonical signed games (task 71).** The per-word inputs are `hgames` (the games with a deck rank at
each proper non-two-power word, which give the policy `hpol` and the canonical games of the conjugate `hcan`) and `hbd` (the boundary
bound, Q22). The tied rising pair `hResP` and the tied negative rising pair `hResN` are derived from the conjugate H-cut case of the negative tie (`H_cut_hQ21`, the target allowed to tie: `0 ≤ Ψ i`), whose one named input is `hFcorner` (the sheet difference at `V_p + I` is not `0` for `ε = +1`) and the conjugate `W1Forced` input `hW1` (at the conjugates that are not pure threes words).

`hW1` is named for now: it is the W1 statement itself at the conjugate word, with no producer yet. It is to be produced by the W1
induction (`W1(conj)` and the table at the conjugate give `W1(u)`, `W1Forced_of_tables_rk`), with the base at the pure words. -/
theorem odometersTheorem_of_canonical
    (hpureSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate k Digit.three))
    (hpureRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate k Digit.three))
    (htwoGames : ∀ k : ℕ, Induction.GamesWithRank (List.replicate (k + 1) Digit.two))
    (hgames : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.GamesWithRank word)
    (hbd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hW1 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word)))
    (hFcorner : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → (frameAt word).eps = 1 →
      sheetDiffW word ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) ≠ 0) :
    OdometersTheorem := by
  -- the twos base inputs: the base slip is proved (twos_baseSlip); the residual comes from the twos games with rank
  have htwoSlip : ∀ k : ℕ, Induction.BaseSlip (List.replicate (k + 1) Digit.two) := fun k => Induction.twos_baseSlip k
  have htwoRes : ∀ k : ℕ, Induction.StrongResidual (List.replicate (k + 1) Digit.two) :=
    fun k => Induction.strongResidual_twos_of_games k (htwoGames k)
  -- the canonical games of the conjugate of every proper non-two-power word
  have hcan : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Nonempty (Induction.CanonicalSignedGames (frameAt (conjWord word)) (standardField (conjWord word))) := by
    intro word hw hn
    by_cases hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three
    · exact canonical_at_threes word hp
    · by_cases hq : Induction.IsTwoPow (conjWord word)
      · obtain ⟨k, hk⟩ := hq
        rw [hk]
        exact Induction.games_of_gamesWithRank (htwoGames k)
      · exact Induction.games_of_gamesWithRank
          (hgames (conjWord word) (exists_ne_three_of_not_replicate_three _ hp) hq)
  -- the strong estimates and the seed fields of every word, from `hbd` and the policy of the games
  have hJ := Induction.strongSeeds_of_all
    (fun k => Induction.StrongEstimates.of_base_pure k (hpureSlip k) (hpureRes k))
    (fun k => Induction.StrongEstimates.of_base_two k (htwoSlip k) (htwoRes k)) hbd
    (fun word hw hn => Induction.policy_of_gamesWithRank (hgames word hw hn))
  have hE : ∀ word : Word, Induction.StrongEstimates word := fun word => (hJ word).1
  have hres : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.StrongResidual word :=
    fun word hw hn => Induction.strongResidual_of_conj hw (Induction.exists_ne_two_of_not_twoPow hw hn)
      (hE (conjWord word)) (hbd word hw hn) ((hJ (conjWord word)).2)
      (Induction.policy_of_gamesWithRank (hgames word hw hn))
  -- the conjugate W1Forced at every proper non-two-power word: pure threes conjugates from `w1Forced_threes`, the rest from `hW1`
  have hW1all : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word)) := by
    intro word hw hn
    by_cases hp : ∃ k : ℕ, conjWord word = List.replicate k Digit.three
    · exact w1Forced_at_threes word hp
    · exact hW1 word hw hn hp
  -- the V-block input hQ21: the conjugate H-cut case (`H_cut_hQ21`), with the named corner input `hFcorner`
  have hQ21 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon → i ∈ (frameAt word).closedPolygon →
        c + (frameAt word).uq ∈ (frameAt word).closedPolygon → i + (frameAt word).uq ∈ (frameAt word).closedPolygon →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j ≤ -1) → 0 ≤ sheetDiffW word i →
        ∀ v ∈ (frameAt (conjWord word)).child.modifiedDeck.span,
          zTurn (c - (frameAt word).sheetShift) + v ∈ (frameAt (conjWord word)).freeH → False := by
    intro word hw hn c i hr hcE hiE hcu hiu hΨc hΨj hΨi
    obtain ⟨j, hj, hjΨ⟩ := hΨj
    have hslipW : ∀ z ∈ (frameAt word).closedPolygon,
        0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
          standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2 := by
      intro z hz
      have hs := (hE word).slipRange z hz
      simpa [ChildFrame.slip] using hs
    exact Induction.H_cut_hQ21 hw (hE (conjWord word)) (hE word).packet
      (Induction.oldPolicyData_of_canonical (standardField_reflectI_conj word (hE (conjWord word)))
        (hcan word hw hn).some (frameAt word).eps (frameAt word).eps_unit)
      hslipW (hFcorner word hw hn) hr hcE hiE hcu hiu hΨc hj hjΨ hΨi
  -- the tied rising pair hResP, from the V-block input hQ21 and the conjugate W1Forced hW1
  have hResP : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
        c ∈ (frameAt word).closedPolygon →
        (c - (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i - (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False :=
    fun word hw hn => Induction.hResP_of_Q21 hw (hE word) (hE (conjWord word)) ((hJ (conjWord word)).2)
      (Induction.oldPolicyData_of_canonical (standardField_reflectI_conj word (hE (conjWord word)))
        (hcan word hw hn).some (frameAt word).eps (frameAt word).eps_unit)
      (hW1all word hw hn) (hQ21 word hw hn)
  -- the tied negative rising pair hResN, from the negative tie (hNegTie_of_Q21, target allowed to tie)
  have hResN : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ c i, RisingBlackPair (standardField word) (-(frameAt word).shortShift) c i →
        c ∈ (frameAt word).closedPolygon →
        (c + (frameAt word).uq ∈ (frameAt word).closedPolygon ∧ i + (frameAt word).uq ∈ (frameAt word).closedPolygon) →
        sheetDiffW word c = 0 → (∃ j, FLatticePaper.Edge j c ∧ sheetDiffW word j = -1) → False :=
    fun word hw hn c i hr hcE hpair hΨc hj =>
      Induction.hResN_of_cases hw (hE (conjWord word)) (hE word).packet
        (Induction.oldPolicyData_of_canonical (standardField_reflectI_conj word (hE (conjWord word)))
          (hcan word hw hn).some (frameAt word).eps (frameAt word).eps_unit)
        (Induction.hNegTie_of_Q21 hw (hE word) (hE (conjWord word)) ((hJ (conjWord word)).2)
          (Induction.oldPolicyData_of_canonical (standardField_reflectI_conj word (hE (conjWord word)))
            (hcan word hw hn).some (frameAt word).eps (frameAt word).eps_unit)
          (hW1all word hw hn) (hQ21 word hw hn))
        hr hcE hpair.1 hpair.2 hΨc hj
  -- the S3 no-fort inputs of each proper word: the sign-one canonical policy of its game, with the packet periods
  have hbulk : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      Induction.S3NoFortInputs (frameAt word) (standardField word) :=
    fun word hw hn => Induction.S3NoFortInputs_of_canonical
      ((Induction.games_of_gamesWithRank (hgames word hw hn)).some.game 1 (Or.inl rfl)).toCanonicalPolicy
      (hE word).packet.periods
  exact odometersTheorem_of_policy hpureSlip hpureRes htwoSlip htwoRes hres
    (fun word hw hn => ⟨fun _ _ => False, ⟨Induction.oldPolicyData_of_canonical
      (standardField_reflectI_conj word (hE (conjWord word))) (hcan word hw hn).some (frameAt word).eps
      (frameAt word).eps_unit⟩⟩)
    hResP hResN hbulk

/-- **The odometers theorem with the pure threes inputs discharged (task 71).** The pure threes inputs `BaseSlip` and `StrongResidual`
come from `pure_threes_final`. The named inputs are `htwoGames` (the twos games with a deck rank; the twos base slip and the twos residual
follow from it), `hgames` (the proper non-two-power words), `hbd` (Q22), `hW1` (the conjugate `W1Forced`), `hFcorner` (the named corner input of the H-cut case, Q27). The S3 no-fort inputs are derived from the sign-one games. -/
theorem odometersTheorem_of_canonical_pure
    (hflatP : ∀ k : ℕ, ∀ c i : Site, TwosEPolicy.TwosSel (2 * (k : ℤ) + 4) 1 (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) 1 c →
      TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) 1 i < TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) 1 c)
    (hflatM : ∀ k : ℕ, ∀ c i : Site, TwosEPolicy.TwosSel (2 * (k : ℤ) + 4) (-1) (standardField (List.replicate (k + 1) Digit.two)) c i →
      (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) i =
        (frameAt (List.replicate (k + 1) Digit.two)).chainPotential (standardField (List.replicate (k + 1) Digit.two)) (-1) c →
      TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) i < TwosEPolicy.rhoTwos (2 * (k : ℤ) + 4) (-1) c)
    (hgames : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → Induction.GamesWithRank word)
    (hbd : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hW1 : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word →
      ¬ (∃ k : ℕ, conjWord word = List.replicate k Digit.three) →
      FLatticePaper.W1.W1Forced (frameAt (conjWord word)).child.num (frameAt (conjWord word)).child.den
        (standardField (conjWord word)))
    (hFcorner : ∀ word : Word, (∃ x ∈ word, x ≠ .three) → ¬ Induction.IsTwoPow word → (frameAt word).eps = 1 →
      sheetDiffW word ((frameAt word).parents.odd.num - (frameAt word).parents.odd.den + 1,
        (frameAt word).parents.odd.num + (frameAt word).parents.odd.den - 1) ≠ 0) :
    OdometersTheorem :=
  odometersTheorem_of_canonical FLatticePaper.EPolicy.pure_threes_inputs.1 FLatticePaper.EPolicy.pure_threes_inputs.2
    (fun k => FLatticePaper.TwosEPolicy.twos_gamesWithRank k (hflatP k) (hflatM k))
    hgames hbd hW1 hFcorner

end FLatticePaper
