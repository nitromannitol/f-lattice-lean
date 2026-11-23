# Producer map of the strong estimates at a proper word

For a proper word `u` (not all threes, not a power of two), the standard field `G = standardField u` must carry the fields of
`StrongEstimates u`, the seed fields `SeedFields u`, and the old policy data `OldPolicyData` used by the odd-child and Q3
arguments. This file records, for each field, the written argument that produces it at `u`, the data that argument consumes,
and the status of the Lean formalization. Notation: `N/D` is the odd parent of `u`, `nq/dq` its even parent, `d = 2D + dq`,
`n = 2N + nq`, `L = d + n`, `T = d² + 2dn − n²`, `Lp = D + N`, `ε = Nd − Dn = ±1`, `W = (1 + ε)/2`, `P` the primitive price,
`D_η` the short slip, `t_p = Nx − Dy`, `s_p = (D+N)x + (D−N)y`. The conjugate of `u` is `conjWord u`, the even child of the
swapped birth prefix, which is strictly shorter than `u`.

Lean status labels: **proved** (no hypothesis beyond the named inputs), **consumed** (a field used as a hypothesis, not
produced), **partly** (produced modulo a named input), **open** (no Lean production), **base** (proved only at the pure words).

## A. Fields of `StrongEstimates u` and `StrongResidualReduced u`

| Field | (a) Written production | (b) Inputs | (c) Lean status |
|---|---|---|---|
| Packet (periods, strips, reflection, binary) | Word induction: the packet of the standard field follows once the open inputs hold at every proper word (`WordInduction.packet_standardField`). | `OpenInputs` at each proper word, which `openInputs_of_strong` derives from `StrongEstimates (conjWord u)`. | partly: proved modulo `StrongEstimates` of the conjugate and the base words. |
| `slipRange`: `0 ≤ D₁ ≤ 2` on `E` | Strong D on the bulk, `STRONG_PRICE_AND_ALTERNATE_STEP` §2; the harmonic and zero regions, `fixes/Q4-strips.md` (zero region, harmonic region). | Conjugate's strong estimates; star-zone inputs; `VArcInputs u`; the sheet unit increments and constrained ranks of the conjugate. | partly: `i3_slipFields_of_strong` (SlipFields.lean) proves it from `StrongEstimates (conjWord u)`, `StarZoneInputs u` and `VArcInputs u`. |
| `priceRange`: `c₀ − 1 ≤ P ≤ c₀` on `E` | Unrounded primitive price on the stars, `STRONG_PRICE_AND_ALTERNATE_STEP` §1; `P(E) ⊂ {c₀−1, c₀}` by the boundary comparison with the recurrent comparison field `M = min(A, C)`, §2; the identity `P − c₀ = (F − h₀)` differences, `escape/newzeros/NO_ODD_SLIP_AUDIT.md` §1. | Earlier price ranges and drifts (conjugate); W1 unit transfer on strict-interior stars; recurrent `M`; the sewn field and its polygon cover. | open. Consumers: `StrongEstimates.price_mem_range`, `price_floor_bound` (ParentStepDischarge), `Q3Strong`. Checked numerically on 3174 closed-polygon sites. |
| `priceDrift`: `P(z+U) = P(z) − 1`, `P(z+V) = P(z)` | Deck identity of the primitive price, `STRONG_PRICE_AND_ALTERNATE_STEP` (drifts `(−1,0)`); no further input beyond the periods. | `HasGeneratorPeriods` (the packet). | **proved** from the packet: `ChildFrame.price_kernel`, `ChildFrame.price_transverse` (Potentials.lean). |
| `slipDrift`: `D_η(z+U) = D_η(z)`, `D_η(z+V) = D_η(z) + 2η` | Deck identity of the short slip, same source. | `HasGeneratorPeriods`. | **proved** from the packet: `ChildFrame.slip_kernel`, `ChildFrame.slip_transverse`. |
| `zeroStripInterval`: `f = 0` for `1 − D ≤ t_p ≤ N + 2D − 1` | Old zero strip `[1 − r, b + 2r − 1]` and the zero region argument, `fixes/Q4-strips.md` ("Zero region", with the second offer formula (3)). | Ordinary strips and binarity of the conjugate; the conjugate's zero strip; the even-parity extension below. | open at general `u`. The Lean `zeroStrip_of_strong` (Q3Paragraph8) only restates the conjugate's own field. Proved at the pure words: `BaseStrip.reciprocal_zeroStripInterval` (`3^k`) and `TwosStripFacts.twos_zero_strip` (`2^k`). |
| `zeroEvenLine`: `f = 0` at even sites with `t_p = −D` | Even-parity extension of the odd zero strip: the sandwich `h(s) ≤ h(s − 2)` between the upper endpoint zero and the `h₀` strip, `escape/newzeros/NO_ODD_SLIP_AUDIT.md` §§2–4; `PARITY_ZERO_INTERVAL_EXTENSION.md`; the odd-child transfer at `−D` in `fixes/Q4-strips.md`. | The native even price bound `P ≤ c₀` (see row `odd_zero`); the `h₀` strip; the pure-run initial values (`BASE_TWO_PIXEL_ZEROS`). | open at general `u`. No Lean production. |
| `F1_unitPrice`: unit increments of `P` on every edge | `STRONG_PRICE_AND_ALTERNATE_STEP` §1: each strict star lies in `E`; the two-level range and the W1 unit transfer give `|δP| ≤ 1` on the star families. | W1 strict-interior unit proofs at `u`; the price range; the translated star families. | open in general. Lean W1 pieces: `W1Lower.harmonicGrid_shift_price`, `price_odd_range` (for W1 cases). Consumer: `i3_noCrossStars_shift`. |
| `F1_noPriceSaddle`: no opposite nonzero increments at a star | Same argument, `STRONG_PRICE_AND_ALTERNATE_STEP` §§1, 3. | As for `F1_unitPrice`. | open in general; consumer `i3_noCrossStars_shift`. |
| `F2F3_reduced`: a quota policy along which `Φ_η`, `P` and the rounded slip do not increase, and a rank with increments `(−1, η)` | Chain-gap monotonicity, `STRONG_PRICE_AND_ALTERNATE_STEP` §4 (with `TWO_RANK_RAW_PHI_AUDIT`, the two-rank lemma); strict rank directions from `escape/ALL_SLOPE_STEP.md` (its addendum fixes the free directions); integer strict rank from `escape/weighted_rank_audit/WEIGHTED_FORT_AND_BELLMAN_RANK.md` §§1–4. | The canonical policy of the conjugate (the row `OldPolicyData` below); canonical strict ranks; the forced-white classification. | open. The bridge `WeightPolicy.rankWithIncrements_of_monotone` (a rank from a monotone retained policy) is proved under its own hypotheses on the deck; the policy and its monotonicity are not. |

## B. Seed fields `SeedFields u`

| Field | (a) Written production | (b) Inputs | (c) Lean status |
|---|---|---|---|
| `even_zero`: `G(2 − L) = 0` on even sites with `t = 2 − L` | Even child branches of the pair induction, `escape/newzeros/PAIR_INDUCTION.md` (first branch `fA = 0` from the odd parent's seed; second branch `fC = 1`, with one exception value `0`). | `SeedFields (conjWord u)` (the odd parent's zero); the packet; `OpenInputs u`; the sheet minimum on `E`. | partly: `W1Seeds.even_zero_of_packet`, `W1Hexc.even_zero_full`, `W1Hc.even_zero_of_packet_hc` reduce it to `SeedFields (conjWord u)`, the packet and `OpenInputs u`; the exceptional case is proved (`hExc_exception`). The pure words are named inputs (`hpure`, `htwo`). |
| `odd_zero`: `quarterTurn G = 0` on even sites with `t_p = 1 − (D+N)` | Two written routes. (i) Odd child branches of the pair induction, `PAIR_INDUCTION.md` (the branch values; the odd-child sheet identity is the open step). (ii) The sandwich of `NO_ODD_SLIP_AUDIT.md` §3: the lower endpoint of the even-parity zero interval, from its upper endpoint zero, the `h₀` strip and the native even bound `P ≤ c₀`. | (i) The odd child's sheet identity in the conjugate chart and the even parent's field. (ii) The native even price bound of the even role (to be confirmed as the conjugate's `priceRange` upper bound); reflection about `I = (1,−1)`. | open. Route (i): the branch values are checked at the seed points, but the odd-child sheet identity is not established on the odd child's polygon. Route (ii): not formalized. Proved equivalence: `W1Seeds.odd_zero_iff_bottom`, `odd_bottom_of_odd_zero`. |

## C. Old policy data `OldPolicyData frame G seed` (the odd-child and Q3 arguments)

| Field | (a) Written production | (b) Inputs | (c) Lean status |
|---|---|---|---|
| `retained`, `quota`: a black centre retains both inputs, a white one at least one | The earlier canonical policy: retention of the chosen parent edge at a black or tied minimum, `fixes/Q3.md` (external facts), `fixes/Q1.md`; matched construction in `STRONG_PRICE_AND_ALTERNATE_STEP` §§1–2. | Canonical strict ranks (`escape/ALL_SLOPE_STEP.md`); the forced-white and free-arc classification (`W1_CONSTRUCTOR` §§1–4). | open. `OldPolicyData` is never instantiated; `MatchedPolicy.lean`, `NoBlackPair.lean`, `SheetCover.lean`, `SheetCharts.lean` consume it. |
| `priceNonincreasing`: `P' = frame.price G` does not increase along `retained` | `STRONG_PRICE_AND_ALTERNATE_STEP` §1 (the primitive price does not increase on the allowed edges, including both inputs at a black star). | The price range and drifts of the conjugate; the W1 unit transfer. | open as a field. Consumer: `parentPolicy_price` (MatchedPolicy) derives the transported nondecrease from it. |
| `bFun`, `bNondecreasing`: the raw slip `b` does not decrease along `retained` | `canonical/strong_bulk/CANONICAL_V_RAW_SLIP_MONOTONICITY.md` (a conditional theorem: `D₊` is nonincreasing on canonical free V edges, given `Ψ` monotonicity on the canonical `A`-graph and `D₊ ≤ 2`). | `Ψ = C − A` nondecrease; native `D₊ ≤ 2`; known V and H traces. | open. No Lean production; the theorem is stated under its own hypotheses in the archive. |
| `chainNonincreasing`: `Φ_η` does not increase along `retained`, `η = ±1` | Chain-gap monotonicity, `STRONG_PRICE_AND_ALTERNATE_STEP` §4 (two genuine decreasing lexicographic policies; `TWO_RANK_RAW_PHI_AUDIT`). | The two policies for `F` and its translate `g`; the common-chart tie rule. | open. Consumer: `NoBlackPair.noBlackPairRise_of_oldPolicy`. |
| `reflection`: retained edges are carried to retained edges by `c ↦ I − c` | Reflection about `I = (1,−1)` (`NO_ODD_SLIP_AUDIT.md` §1, `h₀(I − z) = h₀(z)`), transported through the policy by `f(I − x) = f(x)` (`fixes/Q3.md`). | The symmetric definition of the policy; the old reflection `g((r + b) − j) = g(j)`. | open as a field. Consumer: `parentPolicy_reflection` transports it. |
| `forcedRetained`: forced-white edges are retained | Uniqueness of the forced input at a forced white, from the forced-white classification of the earlier canonical policy (`fixes/Q1.md`, `ForcedEdge` in SquareClauses). | The forced-edge seed; the strict-interior unit derivations (`W1_CONSTRUCTOR` §§1–5). | open. |
| `westAtException`: the prescribed west input at `V_p + I` when `W = 1` | The parent sign convention at the exceptional old V endpoint (`fixes/Q3.md`, external facts). | The W1 exceptional vertex; the parent's sign convention. | open, named. |

## D. Base words (the hypotheses the headline still takes)

The pure words `3^k` and the two-powers `2^k` are not produced by the induction. Their fields are proved for the reciprocal
fields (`BaseStrip`, `TwosStripFacts`, `BaseFields`), and the seeds are the literal pure-run values of
`escape/newzeros/BASE_TWO_PIXEL_ZEROS.md` (§§1–4, with the entire lines of §5). Their numerical checks cover the pure words of
length at most four. In Lean these enter `odometersTheorem_of_strongResidual` as `hpureSlip`, `hpureRes`, `htwoSlip`, `htwoRes`.

## E. Summary

Produced in Lean from the conjugate and the packet: `priceDrift`, `slipDrift` (from the periods), the packet (given the open
inputs), `slipRange` (given the star-zone and arc inputs), `even_zero` (given `SeedFields` of the conjugate and `OpenInputs`).
Open: the price range and the unit and no-saddle fields, the zero strip and its even line at general words, the policy fields
and the rank, `odd_zero` (its odd-child sheet identity, or the sandwich route), and every `OldPolicyData` field. The written
productions for the open fields are the archive sections listed above; where a written production relies on a recurrent
comparison or on an audit boundary that the archive itself states, that dependence is recorded in the row.
