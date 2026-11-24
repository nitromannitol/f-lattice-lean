# w1: the strong residual of a proper word, field by field (survey)

Target: `StrongResidual word` (`Plane/Induction/StrongResidual.lean`) at a proper word from `StrongEstimates (conjWord word)`.
Theorem: `FLatticePaper.Induction.strongResidual_of_conj` (`Plane/Induction/StrongResidualStep.lean`), built with zero errors
and zero warnings; it depends on the four named inputs below and nothing else.

Status vocabulary: **proved** (an existing lemma, derived from the conjugate's estimates or the packet of the word);
**reduces to** (an existing lemma, with a named input that it still needs); **named** (a hypothesis of the theorem with no
producer in the repository for proper words).

## Field by field

| `StrongResidual` field | existing lemma (namespace) | what it needs | status |
|---|---|---|---|
| packet of the word (an input of `of_residual`, not a field) | `packet_of_strong` (`Induction`, TieReduce) | `StrongEstimates (conjWord word)` only | **proved** |
| `priceRange` | `priceRange_of_conjugate` (`StrongPriceInputs`) | the conjugate's estimates, and the boundary bound `hbd` | **reduces to** `hbd` |
| `priceDrift` | `ChildFrame.price_kernel`, `price_transverse` (`Potentials`) | the packet's periods (`hpk.periods`) | **proved** |
| `slipDrift` | `ChildFrame.slip_kernel`, `slip_transverse` (`Potentials`) | the packet's periods; the constants `0` and `2η` match the field | **proved** |
| `zeroStripInterval` | `zeroStripInterval_of_packet` (`W1ZeroStrip`) | the packet | **proved** |
| `zeroEvenLine` | `zeroEvenLine_field` (`W1ZeroStrip`) | the packet, `priceRange`, the two price drifts, and the even seed `hseed` | **reduces to** `hseed` |
| `F1_unitPrice`, `F1_noPriceSaddle` | `unitPrice_and_noSaddle` (`StrongUnitPrice`) | `priceRange`, the transverse price drift, and the star classification `hcls` | **reduces to** `hcls` |
| `F2F3_policy` | `rankWithIncrements_of_strict_hull` (`EPolicy`, F2F3Pure) | the price and rounded-slip drifts (proved above), the monotone policy, and a strict rank with characters on `U, V` | **reduces to** `hpol` |

## The four named inputs (the smallest set with the current lemmas)

1. **`hbd`**: the boundary bound `P ≤ c₀` on the boundary of the closed polygon (`priceRange_of_conjugate`). This is the
   earlier priced boundary comparison, which the header of `StrongPriceInputs` leaves named. Its source is the H-source
   argument, which is the open question **Q22**: the pin "V_1 south" has no admissible input on 34 of the 116 words of length
   at most four (the conclusion holds on all 116; see `QUESTIONS-DETAIL.md`, Q22).

2. **`hseed`**: the even seed `standardField word w = harmonicGrid w` on the odd sites of the sGrade line that `zeroEvenLine_field`
   needs. For the pure words it is `standardField_threes_harmonic_seed`; for a proper word there is no producer. Not among
   Q21–Q25; **named (open)**.

3. **`hcls`**: `StarClassified (frameAt word) (standardField word)`, the classification of the stars (every neighbour lies in
   the closed polygon, the H-star band, or the V-source). No producer for proper words. Not identified with Q21–Q25; **named
   (open)**.

4. **`hpol`**: for each sign, a policy along which the chain potential, the primitive price and the rounded slip do not increase,
   with a quota, together with a strict rank having characters `cU, cV` on the child's kernel and transverse periods, strict
   along the policy. This is the policy and rank of the word itself: the headline supplies a canonical signed policy only for the
   conjugate. The rank with characters is the reflected rank of the reciprocal case (w2). The route to a proof is a canonical
   signed policy of the word plus the rank (`CanonicalSignedGames`, `rankWithIncrements_of_strict_hull`). Possibly the two-rank
   reduction, Q24 (to be confirmed); **named (open)**.

## What changed relative to the older route

- `priceRange_of_strong` (named in the task) needs four named inputs (`hagree`, `hPU`, `hPV`, `hbd`). `priceRange_of_conjugate`
  derives `hagree`, the recurrence and the drifts from the conjugate's estimates, so only `hbd` remains.
- The packet is no longer an input: `packet_of_strong` gives it from the conjugate's estimates. The two drift fields of the word
  come from its periods, so they are not inputs either.
- `StrongResidual.of_reduced` (via `StrongResidualReduced`) is not used: the F2F3 family is built directly with
  `rankWithIncrements_of_strict_hull`, which takes all `(a, c)` at once.

## Consequence for the headline

`odometersTheorem_of_canonical_pure` takes `hres : StrongResidual word` at every proper non-two-power word. With this theorem,
`hres` at such a word is implied by `StrongEstimates (conjWord word)` together with `hbd`, `hseed`, `hcls` and `hpol` at that word.
The four inputs are not discharged for any proper word that is not a pure threes word. For the pure threes words,
`StrongResidual` itself is already given by `pure_threes_inputs` (from `pure_threes_final`), so the theorem is not needed there.
