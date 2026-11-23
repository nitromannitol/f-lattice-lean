import FLatticePaper.Plane.Induction.W1MDescent
import FLatticePaper.Plane.Induction.W1TieInputs
import FLatticePaper.Plane.Induction.W1TieBand
import FLatticePaper.Plane.Induction.StrongPriceValues
import FLatticePaper.Plane.Induction.W1Phase
import FLatticePaper.Plane.Induction.I3Application

/-! # Task 85 (sheet level): the A arrow of every M-white tie is M-forced

For a word `word` with strong estimates `hSE` of its conjugate, and the policy `P` of the conjugate (an `OldPolicyRanked`), with the sheets
`A = sheetA Fq`, `C = sheetC Fq`, `Fq = quarterTurnField (standardField (conjWord word))`, the minimum `M = min(A, C)`, the tie set
`T c : C c = A c`, and the A policy `sheetPolicyA P lv` (`lv = sheetShift`):

`a_arrow_forced`: every M-white tie `c` has an input `o` retained by the A policy with `ForcedEdge M c o`.

Ingredients (all proved in the imported modules): the binarity of `M` (`sheetMin_binary_recurrent_of_strong`); the rank decrease along the
A policy (`P.rank_decr`); the rank bound on the tie band (`rank_bound_on_band`, from the chain potential drift `chainPotential_drift` of the
strong estimates and the rank increments `hinc`); the closure of the tie band under the chains (`parent_inputs_tie`, `chain_in_band`,
`tie_iff_chain`); the A quota at M-white ties (`lapA_zero_of_mwhite`, the parent quota); and the descent (`mforced_of_descent`).

Named inputs: the square data `hsq` at every M-white tie (the free-root table and the nonfree private squares, on the sheets), and the rank
increments `hinc` of the policy for `η = eps(word)`. -/

namespace FLatticePaper.W1MSheet

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1TieInputs FLatticePaper.W1TieBand

/-- The quarter-turned earlier field of the word. -/
noncomputable abbrev FqW (word : Word) : Field := quarterTurnField (standardField (conjWord word))

/-- The sheet minimum `M = min(A, C)` of the word. -/
noncomputable abbrev MW (word : Word) : Field := (frameAt word).sheetMin (FqW word)

/-- The sheet input of a sheet point `c` over a parent input `p` of `Z(c − lv)`. -/
theorem sheet_input_of_parent (c lv : Site) (hlv : EvenSite lv) (p : Site)
    (hp : p = incomingNeg (zTurn (c - lv)) ∨ p = incomingPos (zTurn (c - lv))) :
    ∃ i : Site, (i = incomingNeg c ∨ i = incomingPos c) ∧ zTurn (i - lv) = p := by
  have hn := FLatticePaper.W1HagreeNonfree.zTurn_neighbors c lv hlv
  by_cases hc : EvenSite c
  · rcases hp with hp | hp
    · exact ⟨incomingNeg c, Or.inl rfl, by rw [(hn.1 hc).1, hp]⟩
    · exact ⟨incomingPos c, Or.inr rfl, by rw [(hn.1 hc).2, hp]⟩
  · rcases hp with hp | hp
    · exact ⟨incomingPos c, Or.inr rfl, by rw [(hn.2 hc).2, hp]⟩
    · exact ⟨incomingNeg c, Or.inl rfl, by rw [(hn.2 hc).1, hp]⟩

/-- **The A arrow of every M-white tie is M-forced** (task 85). -/
theorem a_arrow_forced (word : Word) (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hinc : ∃ lam : ℤ, 0 < lam ∧ ∀ x : Site,
      P.rank (x + (frameAt (conjWord word)).child.modifiedDeck.kernel) = P.rank x - lam ∧
      P.rank (x + (frameAt (conjWord word)).child.modifiedDeck.transverse) = P.rank x + 2 * (frameAt word).eps * lam)
    (hsq : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 →
      ∃ p0 p1 p2 : Site, ∃ a b : ℤ,
        c ∈ squareCorners a b ∧ p0 ∈ squareCorners a b ∧ p1 ∈ squareCorners a b ∧ p2 ∈ squareCorners a b ∧
        (∀ c' ∈ squareCorners a b, c' ≠ c → c' = p0 ∨ c' = p1 ∨ c' = p2) ∧
        p0 ≠ p1 ∧ p1 ≠ p2 ∧ p0 ≠ p2 ∧ (p0 = incomingNeg c ∨ p0 = incomingPos c) ∧
        ¬ sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c p0 ∧
        Edge p1 p0 ∧ Edge p2 p1 ∧ Edge c p2 ∧
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p0 p1 ∧
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p1 p2 ∧
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p2 c) :
    ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 →
      ∃ o : Site, (o = incomingNeg c ∨ o = incomingPos c) ∧
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c o ∧
        ForcedEdge (MW word) (fun _ _ => False) c o := by
  intro c0 hT0 hM0
  -- the binarity of the sheet minimum, the chain identity, and the drifts
  obtain ⟨hbinM, _⟩ := FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong h hSE
  have hbinF : ∀ x, laplacian (FqW word) x = -1 ∨ laplacian (FqW word) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hlvE : EvenSite (frameAt word).sheetShift := (frameAt word).evenSite_sheetShift
  obtain ⟨K, hK⟩ := tie_iff_chain word h hSE.packet
  obtain ⟨lam, hlam, hlamP⟩ := hinc
  have hdrift := chainPotential_drift (frame := frameAt (conjWord word)) (G := standardField (conjWord word))
    (η := (frameAt word).eps) hSE.priceDrift (hSE.slipDrift _ (frameAt word).eps_unit)
  obtain ⟨hΦU, hΦV⟩ := hdrift
  obtain ⟨B, hB⟩ := rank_bound_on_band (child_det_ne_zero (conjWord word)) (Φ := chainPot word (standardField (conjWord word)))
    (R := P.rank) (η := (frameAt word).eps) (lam := lam) (K := K)
    (fun x => hΦU x) (fun x => hΦV x) (fun x => (hlamP x).1) (fun x => (hlamP x).2)
  -- the rank bound on the tie band
  have hrankB : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      P.rank (zTurn (c - (frameAt word).sheetShift)) ≤ B := by
    intro c hT
    have hc := hK c
    rw [hT, sub_self, zero_add] at hc
    exact hB _ hc
  -- the A quota at M-white ties
  have hquot : ∀ c : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 →
      ∃ i : Site, (i = incomingNeg c ∨ i = incomingPos c) ∧
        sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c i := by
    intro c hT hM
    have hA0 := lapA_zero_of_mwhite (frameAt word) (FqW word) hbinF c hM hT
    have e1 : laplacian ((frameAt word).sheetA (FqW word)) c =
        laplacian (FqW word) (c - (frameAt word).sheetShift) :=
      laplacian_sub_even (FqW word) (frameAt word).sheetShift hlvE c
    have hG0 : laplacian (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = 0 := by
      show laplacian (standardField (conjWord word)) (i3Z (c - (frameAt word).sheetShift)) = 0
      rw [← i3_laplacian_quarterTurn (standardField (conjWord word)) (c - (frameAt word).sheetShift), ← e1]
      exact hA0
    rcases P.quota.2 _ hG0 with hr | hr
    · obtain ⟨i, hi, hzi⟩ := sheet_input_of_parent c (frameAt word).sheetShift hlvE _ (Or.inl rfl)
      exact ⟨i, hi, by
        show P.retained (zTurn (c - (frameAt word).sheetShift)) (zTurn (i - (frameAt word).sheetShift))
        rw [hzi]
        exact hr⟩
    · obtain ⟨i, hi, hzi⟩ := sheet_input_of_parent c (frameAt word).sheetShift hlvE _ (Or.inr rfl)
      exact ⟨i, hi, by
        show P.retained (zTurn (c - (frameAt word).sheetShift)) (zTurn (i - (frameAt word).sheetShift))
        rw [hzi]
        exact hr⟩
  -- the closure of the tie band under the chains
  have hmono : NonincreasingAlong (chainPot word (standardField (conjWord word))) P.retained :=
    P.chainNonincreasing _ (frameAt word).eps_unit
  have hcl : ∀ c p0 p1 p2 : Site, (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c →
      laplacian (MW word) c = 0 → (p0 = incomingNeg c ∨ p0 = incomingPos c) →
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p0 p1 →
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p1 p2 →
      sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift p2 c →
      (frameAt word).sheetC (FqW word) p0 = (frameAt word).sheetA (FqW word) p0 ∧
      (frameAt word).sheetC (FqW word) p1 = (frameAt word).sheetA (FqW word) p1 ∧
      (frameAt word).sheetC (FqW word) p2 = (frameAt word).sheetA (FqW word) p2 := by
    intro c p0 p1 p2 hT hM hp0 hR0 hR1 hR2
    have hT0 : (frameAt word).sheetC (FqW word) p0 = (frameAt word).sheetA (FqW word) p0 :=
      inputs_tie_of_mwhite (frameAt word) (FqW word) hbinF c hM hT p0 hp0
    have hcK : chainPot word (standardField (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) = K := by
      have hc := hK c
      rw [hT, sub_self, zero_add] at hc
      exact hc
    have hp0K : chainPot word (standardField (conjWord word)) (zTurn (p0 - (frameAt word).sheetShift)) = K := by
      have hc := hK p0
      rw [hT0, sub_self, zero_add] at hc
      exact hc
    obtain ⟨hp1K, hp2K⟩ := chain_in_band word hmono hcK hp0K hR0 hR1 hR2
    unfold chainPot at hp1K hp2K
    have hT1 : (frameAt word).sheetC (FqW word) p1 = (frameAt word).sheetA (FqW word) p1 := by
      have hc := hK p1
      have e : i3Z (p1 - (frameAt word).sheetShift) = zTurn (p1 - (frameAt word).sheetShift) := rfl
      rw [e, hp1K] at hc
      linarith
    have hT2 : (frameAt word).sheetC (FqW word) p2 = (frameAt word).sheetA (FqW word) p2 := by
      have hc := hK p2
      have e : i3Z (p2 - (frameAt word).sheetShift) = zTurn (p2 - (frameAt word).sheetShift) := rfl
      rw [e, hp2K] at hc
      linarith
    exact ⟨hT0, hT1, hT2⟩
  -- the descent
  exact FLatticePaper.W1MDescent.mforced_of_descent (MW word) (fun c =>
      (frameAt word).sheetC (FqW word) c = (frameAt word).sheetA (FqW word) c)
    (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
    (fun c => P.rank (zTurn (c - (frameAt word).sheetShift))) B hbinM
    (fun x y hxy => P.rank_decr _ _ hxy)
    (fun c hT => hrankB c hT) hquot hsq hcl c0 hT0 hM0

end FLatticePaper.W1MSheet
