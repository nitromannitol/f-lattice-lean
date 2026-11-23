# Q3 chain: inventory of named hypotheses (task 59)

Categories:
- (i) field data of the conjugate's strong estimates (`StrongEstimates (conjWord word)`);
- (ii) the old canonical policy / forced-white classification;
- (iii) a reading (PROVISIONAL, checked numerically before stating);
- (iv) geometry awaiting W1's rectangle facts (task 45, Pick count);
- (v) structural (non-cube word, parent bounds, child parity, definitional instantiation).

Status: *discharged* = supplied by a wrapper from `StrongEstimates (conjWord word)` and `∃ x ∈ word, x ≠ three`;
*open* = still a named hypothesis of a theorem that the chain uses.

## Strong estimates used by the Q3 chain (the top inputs, category (i))

| field | file:line | used by |
|---|---|---|
| `packet` (periods, reflection) | StrongEstimates.lean:55 | Q3Field (reflection, periods); Q3Strong, Q3Field wrappers |
| `priceRange` | StrongEstimates.lean:60 | price_floor_bound (Q3Bound.lean:64), p_shift_bound (Q3Strong.lean:32) |
| `priceDrift` | StrongEstimates.lean:66 | price_floor_bound (Q3Bound.lean:65), p_shift_bound (Q3Strong.lean:32) |
| `zeroStripInterval` | StrongEstimates.lean:80 | zeroStrip_of_strong (Q3Paragraph8.lean:37) |

## Named hypotheses in the Q3 files

| hypothesis | file:line | category | status |
|---|---|---|---|
| `hSE : StrongEstimates (conjWord word)` | Q3Strong.lean:18, 33, 47; Q3Field.lean:287, 305; Q3Paragraph8.lean:38, 71 | (i) | top input |
| `h : ∃ x ∈ word, x ≠ three` | Q3Strong.lean:17, 32, 46; Q3Field.lean:286; Q3Paragraph8.lean:20, 28, 37, 70 | (v) non-cube | top input |
| `hconj : conj.child = frame.parents.odd.rotate` | Q3Bridge.lean:19; Q3Hlat.lean:24, 36; Q3Bound.lean:18, 63; Q3Field.lean:178, 207 | (v) frame relation | discharged by `frameAt_conj_child` (Q3Strong.lean:17–46) |
| `hG : HasGeneratorPeriods conj.child G …` | Q3Bridge.lean:20; Q3Bound.lean:19; Q3Field.lean:85 | (i) | discharged by `hSE.packet.periods` (Q3Strong.lean:46) |
| `hP : conj.Packet G` (`fr.Packet G`) | Q3Field.lean:119, 157, 166, 207 | (i) | discharged by `hSE.packet` (Q3Field.lean:286–305) |
| `hR` (price range) | Q3Bound.lean:64 | (i) | discharged by `hSE.priceRange` (Q3Strong.lean:32) |
| `hD` (price drift) | Q3Bound.lean:65–66 | (i) | discharged by `hSE.priceDrift` (Q3Strong.lean:32) |
| `hN1 : 1 ≤ N`, `hND : N + 1 ≤ D` | Q3Bound.lean:67 | (v) parent bounds | discharged by `frameAt_odd_num_pos` + odd parity (Q3Strong.lean:17–46) |
| `hB : 0 < B` (in `parentFloor_le_sub_sheetStep`) | Q3Bound.lean:52 | (v) | derived by `nlinarith` in `p_shift_bound` (Q3Bound.lean:70s) |
| `hweb : HRootWeb N D (parentTGrade x)` | Q3Paragraph8.lean:72 | (iv) | **open**: the regular floor step of the H web (even `[1, N+D−1]`, odd `[N,D]`); the exceptional values are proved in ParentWeb.lean. This is the only open named hypothesis of paragraph 8 (H part). |
| `hRectInputs` | (was Q3Exit.lean:44–45) | (iv) | **discharged**: W1Exit.lean:303–307 (`exit_centre_on_boundary_spectrum`, unconditional). The Q3 wrapper `ChildFrame.exit_centre_on_boundary_spectrum` (Q3Exit.lean) keeps the hypotheses, as a generic lemma. |
| `hBoundary` | (was Q3Exit.lean:46) | (iv) | **discharged**: W1Exit.lean:303–307 (`boundaryClosed`). |
| `openRect` (definition) | Q3Exit.lean:25–34 | (iii) reading / (iv) W1 | PROVISIONAL: parity-resolved open rectangle, the W1 reading of task 45. |
| `onBoundarySpectrum` (definition) | Q3Exit.lean:36–40 | (iii) reading | PROVISIONAL: t or s in the H/V spectrum up to ±T. |
| `hn : 3 ≤ n`, `hnd : n + 2 ≤ d` | Q3Window.lean:21, 29, 37, 45 | (v) child structure | `n ≥ 3` is a paper hypothesis; `n + 2 ≤ d` follows from parity and `n < d` (instantiation needed). |
| `hz`, `hu` (membership bounds of the ends in E) | Q3Window.lean:22–23, 30, 38–39, 46 | (iv) definitional | instantiated by `closedPolygon` membership (Q3Exit.lean:47 uses the same polygon). |
| `hin` (input relation) | Q3Window.lean:23, 31, 39, 47 | (v) structural | instantiated by `incomingNeg/incomingPos`. |
| `hexit` (exit reading) | Q3Window.lean:23, 31, 39, 47 | (iii) reading | PROVISIONAL: the exit from the supported interval (Q2 notation, paragraph 3). Checked: with both ends in E, all 464 upper and 464 lower exits satisfy the bounds (q3_window_check.py). |
| `hsep : L ≤ μ − lam` and `hstep : s₂ − s₁ ≤ L` | Q3Inputs.lean:14–15 | (iii) reading (window mod 2C) | PROVISIONAL: `chart_separation` is a generic lemma. Note: the parity tightening (both shifted s even, so the gap is `L + 2` not `L − 2`) must be applied before using `hsep` (`μ − lam = L − 2` with `lam = 2−d+n`, `μ = 2n`). |
| `hstep` (unit input) | Q3Inputs.lean:61 | (v) | `(a,b)` is one of the four unit inputs. |
| `hn`, `hd` (nonnegativity of num, den) | Q3Inputs.lean:62 | (v) | from `frame.valid.even_bounds` / `odd_bounds`. |
| `hB`, `hwidth`, `hl`, `hh`, `hlo`, `hhi` (spectrum inequality) | Q3Arithmetic.lean:16–17 | (iii) reading | `B = s(U_p) = 2C` and the window `[l, h]` the V spectrum of the child; checked numerically (q3_chart_mod_check.py). |
| `hd`, `hD` (nonzero denominators) | Q3Arithmetic.lean:37 | (v) | `ℚ` casts of `den ≠ 0`, from the odd bounds. |

## Readings and claims not formalized (no Lean hypothesis, numerics only)

- **Category (ii) (the old canonical policy and forced-white classification):** no Lean hypothesis in the Q3 files. The paper's uses (the "matched old policy" in paragraph 4, the retention and the monotone policy in paragraphs 6 and 7, the forced-white edges in paragraph 2) are not formalized. The S3 `CanonicalPolicy` structure (S3Canonical.lean) is a different, earlier object.
- **Category (iii) window mod 2C (chart, paragraph 4):** the common-shift check `q3_chart_mod_check.py` holds with the window `[λ, λ+2C)` taken mod `2C`, on all 417360 pairs (shift 0 or `−ηεU_q`). The Lean `chart_separation` (Q3Inputs.lean:14) covers only the separation step. The window itself is not formalized.
- **Paragraph 8, V star (task 60, formalized):** `native_V_a_zero_or_one` (Q3VStar.lean) gives `a ∈ {0,1}` on the native box, from `price_floor_bound_of_strong` and `zeroStrip_of_strong` (category (i)); `aVal_translate_UV` gives `a(x + iU_p + jV_p) = a(x) + j`; `drop_forces_j_zero` gives `j = 0` for a drop 1 → 0. The reading of 'the pair' (which two values of `d_f` form the pair, PROVISIONAL, category (iii)) is not fixed by the text; the lemmas are stated for `a` and for `d_f` values through `a = −p`.
- **V path (task 60):** the floor agreement `vBlock_floor_agree` (Q3VPath.lean), the box `vbox_tp_bounds` and the odd vertices `odd_vertex_tp_bounds` carry no named hypotheses beyond the child parameters (category (v)).
- **Paragraph 2 (inputs of a black centre in E):** the exit lemma `exit_centre_on_boundary_spectrum` (Q3Exit.lean:43) reduces the claim to the two named hypotheses (iv). The strip facts of paragraph 2 are field data (i), not used in Lean.
- **Paragraphs 9–10 (task 60, Q3Para10.lean and Q3White.lean), one notion of child left V vertex:** `IsLeftVertex` is not used; the notion is the V cut `freeV` of S3FreeBoundary (left boundary of `closedPolygon`, `vSpectrum (sGrade z)`). Formalized: `block_mem_freeV` (every `1 ≤ l ≤ D` vertex `(−b, 2l − 1 − b)`, `b = ⌊(d−n)l/d⌋`, is in `freeV`, with `q = (d−n)l − db ∈ [1, d−1]` proved from `ε = ±1`); `parent_block_mem_freeV` (the parent vertex `v_l`, `l < D`, via `vBlock_floor_agree`); `VpI_not_freeV` (for `ε = +1`, `V_p + I` has its left neighbour in `E`); `index_of_freeV` (`x = v + iU_p`, `x, x+U_q ∈ E` gives `i ∈ {0,1}`); `exceptional_i_zero`. Whiteness: `laplacian_eq_zero_of_freeV` (under `Packet.strips`, the star of a `freeV` vertex lies in the h0 strip, where `F = harmonicGrid`, so its Laplacian is `0`); `laplacian_add_period` with `child_kernel` (the packet period `F(z+U) = F z + c` with `U = (d,n)` the child's modified kernel, since `d+n` is even, makes the Laplacian `U`-periodic). `black_centres_contradiction` closes the case analysis: `i = 0` gives `x = v`, `i = 1` gives `x + U_q = v + U`, both white, so `x` and `x + U_q` cannot both be black. The black hypotheses `hb : laplacian F x = −1` and `hbu : laplacian F (x + U_q) = −1` are **named inputs** (paragraph 2 field data, category (i)/(iii)) at task 60; task 61 derives `hbu` from `hb` and a rise along `U_q` (Q3Rise.lean, see the task-61 section below). The packet `periods` and `strips` are category (i).
- **Paragraph 9–10 readings (PROVISIONAL):** the parity-resolved spectrum (`even s ∈ [0,2n]`, `odd s ∈ [2−d+n, L−2]`) of the earlier `IsLeftVertex` is replaced by the S3 `vSpectrum` union `[2−d+n, L−2]` (`s` is always even, so the two notions differ only at even sites with `s ∈ (2n, L−2]`); the index argument and the white argument use the union window and do not need the parity split.

## Paragraph 1 and the old-policy interface (task 61)

- **Paragraph 1 (a rise forces both centres black), formalized:** for a black centre `c` with a rise `slipIncrement = 1` at an input `u` along an even shift `σ`, `rise_partner_neg/pos` (OddRise.lean) give that the other input is −1 and that `c + σ` is black. The input sum lies in {0, −1} by binarity, and the unit bound forces the partner to −1; the ranges `D_±` are not used. Q3Rise.lean: `partner_black_of_rise` (σ = `U_q`, with the unit slip `hU` for `U_q` as a named input) and `no_rise_at_block_centre` (a rise at a black V-block centre is impossible, by `black_centres_contradiction`). Axioms: standard (checks/Q3Rise.lean).
- **σ mismatch (reported, not chosen):** `OddRise` and `OddBlackNoRise` use σ = `shortShift = εU_p` (the producer's `F1_unitSlip`, StrongProducer.lean:51); the V-block contradiction needs the partner `x + U_q`. Q3.md's chart analysis gives common shifts `ηεU_p` or `−ηεU_q`, and the pair `(z, z + εU_q)` appears in the negative chart. So the unit slip for `U_q` is an extra input, and no strong-estimate field supplies it.
- **OldPolicyData (OldPolicy.lean) against `StrongResidual` / `StrongResidualReduced`:**
  - already present: `quota` (RetainQuota in `F2F3_policy` and `F2F3_reduced`); `chainNonincreasing` (NonincreasingAlong `chainPotential η`, η = ±1, in both);
  - partly present: `pNondecreasing` (NonincreasingAlong `price` in `StrongResidualReduced` only; the sign and the Z-shift identification with `p = c₀ − P(Z·)` are not verified);
  - not present (to add to the strong estimates): `bNondecreasing` (raw slip), `reflection` (about I = (1, −1)), `forcedRetained` (ForcedEdge), `westAtException` (ε = 1, prescribed west input at V_p + I);
  - `F2F3_policy` gives the policy only existentially (`∃ policy`); the data needs the producer to return the policy itself;
  - `RankWithIncrements` (in `F2F3_policy`) is not a field of OldPolicyData.
- **`OddBlackNoRise` assembly (not done):** `OddBlackNoRise F σ` asks, for every black `c` with odd `F c − F (c+σ)`, that no input has `slipIncrement > 0`. `no_rise_at_block_centre` covers only the V-block centres and only the shift `U_q`. The other black centres need `NoBlackPairRise` (the paragraph 3–8 sheet exclusion, OddRise.lean, premise not proved) for σ = `shortShift`. Which centres and which shift the rise is assumed on is the further reading.
- **Numerics (task 61 rerun, union `freeV`):** `q3_block_check.py`: all 8 rows True. `q3_para10_check.py`: C1 116 True, C2 2426 True, C3 2368 True, C4 (W = 1) 58 True. The earlier W = 0 exceptional rows were a script artifact (`V_p + I` was added to the W = 0 block) and are removed; C2 falls from 2542 to 2426.

## Summary of open items

1. `hweb` (Q3Paragraph8.lean:72), category (iv): the H-web floor step (the regular even and odd web values; the V-web floor step is in Q3VPath as an arithmetic box, not as a named hypothesis).
2. (discharged in task 60: `hRectInputs`, `hBoundary`, by W1Exit.lean:303–307.)
3. The rectangle and boundary readings `openRect`, `onBoundarySpectrum` (Q3Exit.lean:25, 36), category (iii)/(iv): PROVISIONAL.
4. `hexit` (Q3Window.lean:23, 31, 39, 47), category (iii): the exit reading.
5. `chart_separation` (Q3Inputs.lean:14): needs the parity tightening (`L + 2`), category (iii).
6. (done in task 60: `paragraph5_field_identity` with `hlat` removed from Q3Bridge.lean; the proved identity is `paragraph5_field_identity_proved`, Q3Bound.lean.)
7. (task 60, paragraphs 9–10; updated in task 61) `black_centres_contradiction` (Q3White.lean) needs two black centres `x`, `x + U_q`. Task 61 derives `hbu` from `hb` and a rise along `U_q` (Q3Rise.lean). The premise `hb` (a black V-block centre with a rise) stays a named premise, and the unit slip `hU` for `U_q` is a named input.
8. (task 61) The unit slip for the shift `U_q` (`hU`, Q3Rise.lean) is not a strong-estimate field: `F1_unitSlip` (StrongProducer.lean:51) is for `shortShift = εU_p` only. This is the σ mismatch, reported and not chosen.
9. (task 61) `OddBlackNoRise` assembly: needs the paragraph 3–8 exclusion `NoBlackPairRise` for all black odd centres (not proved in OddRise.lean) and the reading of σ. Reported, not chosen.
10. (task 61) `OldPolicyData` fields `bNondecreasing`, `reflection`, `forcedRetained`, `westAtException` are not in the strong estimates, and `pNondecreasing` is only partly there (see the task-61 section).

All (i)-category hypotheses are supplied by `StrongEstimates (conjWord word)` through the `_of_strong` wrappers (Q3Strong, Q3Field, Q3Paragraph8).
