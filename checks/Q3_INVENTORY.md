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

## NoBlackPairRise: the case split (task 62, NoBlackPair.lean)

Target: `NoBlackPairRise F shortShift` (OddRise.lean), i.e. no rise at a black odd centre with black translate. The
paper's cases (fixes/Q3.md, paragraphs 3–10) are the named inputs of `noBlackPairRise_of_cases`:

| case (Q3.md) | Lean leaf | status | reason |
|---|---|---|---|
| sheet choice: strict root / tie, retention | `hcover` (cover of a rising black pair by the cases) | named | the active sheet and its matched policy are not Lean objects |
| first common chart, `F(·+ησ) − A = min(0, Ψ − 2η)` | `firstCommon`, `hfirst` | proved from `hfirst` | `rise_excluded_at_edge`: `Φ₁(i) ≤ Φ₁(c)` and `P(c+σ) ≤ P(i+σ)` give slip increment `≠ 1` (`slipIncrement_eq_chain_gap`); `hfirst` is the chain-gap and price monotonicity on first-chart edges, named |
| exit with the same slip | `exitSameSlip`, `hexit` | named | needs the exit geometry (Q3Exit `openRect` / `onBoundarySpectrum`, PROVISIONAL) |
| adjacent positive chart (first offer) | `adjacentPositive`, `hadj` | named | needs the primitive span bound `p(x−e) ≥ p(x) − 1` on the period index; `t_p(−e) ≥ 0` is in Q3Para10 but not wired to `p` |
| negative chart, `a: 1 → 0`, nonfree root | `negativeNonfree`, `hnonfree` | named | needs `a(x) = p(I − x)` from `f(I−x) = f(x)`; `Packet.reflection` is about `frame.centre` with a `tGrade` term, not literal `F(I−y) = F(y)` |
| negative chart, free H roots `a = 0` | `negativeFreeH`, `hfreeH` | named | needs the native H star classification (`t_p` ranges) |
| negative chart, free V roots `j = 0`, `i ∈ {0,1}` | `negativeFreeV` → `BlockPairAt`, `hfreeV` | output named; contradiction proved | `not_rising_of_blockPair` (`ε = ±1`): the black partner has the Laplacian of `c − U_q` or `c + U_q` by the period `U = U_p + U_q`; `black_centres_contradiction` (Q3White) excludes the pair |
| exceptional `V_p + I` (W = 1) | `exceptionalVertex`, `hexc` | named | paragraph 10: `a(v) = p(0) + 1` and `a(v − (1,0)) = p(1,0) + 1` need `westAtException` and the zero-strip values of `p` at `t_p ∈ {0,−1,N,N−1}` |

Shift and sign mismatches found in this step (not chosen; for the lead):
- `OldPolicyData.pFun` is the paper's `p(x) = f(x − εU_q) − f(x)`, but the Lean `price` uses `parentShift = ε(N−D, N+D)` (the odd parent's transverse, `ChildFrame.lean:23`), so `price` is not `p` and `pNondecreasing` does not give `hfirst`'s price step.
- With quota (a black centre retains both inputs) and `chainNonincreasing` on all retained edges, `hfirst` applied to every black pair would exclude every rise. The paper's chart analysis is needed exactly because the monotone quantities hold on different charts, so `hfirst` must be stated per chart (as done), not globally.
- `noBlackPairRise_of_oldPolicy` takes `firstCommon ⇒ P.retained` and the price step as named inputs; `chainNonincreasing 1` is used as the chain-gap monotonicity.

### Task 63 status (supersedes the status column above; SheetCases.lean, MatchedPolicy.lean)

- Mismatch 1 (chart-monotone quantity), restated: `OldPolicyData.priceNonincreasing : NonincreasingAlong (frame.price G) retained` on the conjugate frame's own price. By paragraph 5, `p(x) = c₀ − P'(Zx)` (`paragraph5_field_identity_of_strong`), so this is `p` nondecreasing along the transported policy `parentPolicy P c i := P.retained (Z c) (Z i)` (`parentPolicy_price`). `pFun` is removed.
- Matched policies as Lean objects: `parentPolicy P` (parent sheet), `sheetPolicyA P lv` (`c, i ↦ parentPolicy (c − lv) (i − lv)`), `sheetPolicyC P lv centre` (pulled back by the exchange `z ↦ centre − z`, `SheetExchange`). Price steps in their own coordinates: `sheetPolicyA_price`, `sheetPolicyC_price`. Reflection: `parentPolicy_reflection` (from `P.reflection`, with `Z(I − w) = I' − Zw`, `zTurn_reflect`).
- Sheet selection (paragraph 3), as far as the unit bound allows: `sheetMin_A_at_input` (`Ψ(c) ≥ 1`, unit bound on `Ψ = C − A` gives `M = A` at the input), `sheetMin_C_at_input`, `sheetMin_A_at_tie`. The unit bound on `Ψ` is a named input: `SheetLocalInputs.unit` is stated for `sheetChainPotential` (`Ξ`), and `Ψ = C − A` is not yet identified with `Ξ` (`sheetC_sub_sheetA_eq` gives `C − A` as a two-point `G` difference plus an affine term).

| case | status (task 63) | leaf |
|---|---|---|
| nonfree root (`a: 1 → 0`) | **proved**: `nonfree_drop_excluded` (`paragraph7_of_strong`, `paragraph5_field_identity_of_strong`, `parentPolicy_reflection`, `parentPolicy_price`) | no hypothesis beyond `P` and `hSE` |
| free H roots (`a = 0`) | **proved given `hweb`**: `H_drop_excluded` (`H_root_a_eq_zero`). `hweb : HRootWeb N D (parentTGrade x)` is **not** supplied by ParentWeb (ParentWeb has only the endpoint values); it stays the named paragraph-8 input in the cover | `hweb` |
| free V roots (`j = 0`, `i ∈ {0,1}`) | **proved** given the block output: `ChildFrame.not_rising_of_blockPair` | the cover output `BlockPairAt` |
| exceptional `V_p + I` (W = 1) | **proved given `hT`**: `exceptional_drop_excluded`, with `p(0) = 0` (`pJump_origin_zero`) and `p(1,0) = 0` (`pJump_corner_zero`) from `zeroStrip_of_strong` | `hT : a(v − (1,0)) = p(1,0) + 1` (the paper's `V_p`-step; `HarmI2.harmR_shift_Vp` needs a periodicity hypothesis not yet wired) |
| adjacent positive chart (first offer) | **partial**: `first_offer_of_strict` (`min(p x, Ψ + p(x − e)) = p x` for `Ψ ≥ 1`, from `p_shift_bound_of_strong`); the contradiction is not closed | `hadj` |
| first common chart | named (`hfirst`); the chain monotonicity in `noBlackPairRise_of_cases` is stated for the conjugate chain with `η = 1`, not for the word's `η = eps(word)` in the sheet coordinates (`i3_sheet_eq_chainPotential`) | `hfirst` |
| exit with the same slip | named (`hexit`) | `hexit` |
| cover of a rising black pair by the cases | named (`hcover`); the sheet choice is the selection lemmas above | `hcover` |

`noBlackPairRise_of_sheet_cases` (SheetCases.lean) states `NoBlackPairRise (standardField word) (frameAt word).shortShift` from `hcover`, `hfirst`, `hadj`, `hexit`, `hT` (all named) and the closed leaves above; checks in `checks/SheetCases.lean` (standard axioms only).

### Task 64 status (SheetCharts.lean; supersedes the task 63 rows for hfirst, hadj, hT)

- (a) `Ψ = C − A` and the sheet chain: PROVED. `sheetDiff_eq_neg_chain`: `Ψ(z) = −Ξ(z − l_v) + K` for a constant `K`, with `Ξ` the sheet chain potential (`i3_sheet_eq_chainPotential`), from `i3_chainSheet_identity` (the affine part cancels there), `chainPotential_eq_sub_chainSheet` and `quarterTurnField G = G∘Z + h₀`. The numerics (scripts/sheet_psi_check.py, eight words, box of radius 3) agree: `Ψ(z) + Ξ(z − l_v)` is constant. Consequences, proved: the unit bound of `Ψ` on edges (`sheetDiff_unit`, from `i3_sheet_unit_of_strong`, translated by the even `−l_v`); `Ψ` nondecreasing along the A-policy edges (`sheetDiff_mono_A`, from `chainNonincreasing` at `η = eps(word)`); the strict-root selection `sheetMin_A_of_strict_root` (`Ψ(c) ≥ 1` selects `A` at each input).
- (b) first common chart, `η = +1` (the sign of `NoBlackPairRise`): PROVED. `first_chart_excluded`: under `FirstChartEdge` (both ends `A`, the shifted value minus `A` equal to `min(0, Ψ − 2)` at both ends, the edge A-retained), `D₊ = max(0, 2 − Ψ)` and `Ψ` does not decrease, so no rise. The `η = −1` analogue is not needed for `NoBlackPairRise` and is not written.
- (c) adjacent chart: PROVED. `adjacent_chart_excluded`: `AdjacentChartEdge` (both ends `A`, a strict target `Ψ(i) ≥ 1`, the shifted values `min{p(x), Ψ + p(x − e)}` at `x = z − l_v`, the edge A-retained) gives `D(i) − D(c) ≤ 0`. The tied target is not in this lemma (the paper reflects it to the negative chart).
- (d) `hT`: PROVED. `exceptional_hT_proved`: `a(v − (1,0)) = p(1,0) + 1`, from `v − (1,0) = (0,−1) + V_p` (`aVal_translate_V`) and `jumpA_eq_pJump` (paragraph 7).
- Named in the cover (`noBlackPairRise_of_charts`): `hcover` (the chart witnesses, which carry the paper's chart formulas `F(·+σ) − A = min(…)`), and the exit leaf `hexit`. The link `F = sheetMin` on the star (needed to derive `F c = A c`, `F i = A i` at a strict root from `sheetMin_A_of_strict_root`) is not in Lean; `hcover`'s witnesses state `F = A` directly.
- Checks: `checks/SheetCharts.lean` (9 `#print axioms`, standard axioms only); zero warnings and errors in the sandbox log; root build clean.

### Task 65 status (SheetPieces.lean, ExitSlip.lean, SheetCover.lean)

- (1) `F = sheetMin` on `E`: PROVED. `standardField_eq_sheetMin_of_strong` (the `RespectsPeriodsOn` hypothesis discharged from the strong estimates through `openInputs_of_strong`, `sheetFacts_of_conjPacket`, `stripInputs_sheetMin`, `respectsPeriodsOn_of_heightInputs`); `standardField_eq_sheetMin_on_star` (centre and both inputs in `E`).
- (3) exit case, the centre exiting from below (`η = +1`): PROVED. `CentreLowerExit c i` (`c, i ∈ E`, `Edge i c`, `t(c) − 2 < a_χ − T`) gives `D(c) = D(i) = 2` (`slip_translate_V`: `D w = D(w − V) + 2` from the packet's transverse period, `transverseGrade = −tGrade`, `tGrade σ = −2`), via the window lemmas `Q3Window.lower_exit_*` and the zero strip at `w − V`, `w − V + σ`. So the slip increment is `0` (`not_rising_of_centre_exit`). `n ≥ 3` and `n + 2 ≤ d` are derived (`child_num_ge_three`, `child_facts`), not assumed.
- Exit at the input `i` itself (the shifted input leaves the window): NAMED (`inputExit`); the window lemmas take the centre as the exiting end, so this needs its own parity table.
- (4) `hweb`: REDUCED, not proved. `HRootWeb_iff_bounds`: `HRootWeb N D t ↔ 0 ≤ t ≤ N + D` (the web is the whole interval). So `hweb` is the bound `0 ≤ t_p(x) ≤ N + D` on the free H cut `freeH` (bottom boundary of `E`, `t` in the H spectrum); that bound is still the open lattice statement (not in ParentWeb, which has the endpoint values only).
- (2) chart witnesses: NOT CLOSED. The first chart needs `F(z + σ) = M(z + σ)` at the shifted point, and `M = sheetMin` is not periodic on the plane: a numerical test (scripts/sheet_global_period_check.py) shows `M(z + U) − M(z)` is not constant for five of the eight words tested (`sheets.py` also notes `F = min(A, C)` holds on the polygon only). So the shifted value is not a sheet value of `M` at `z + σ` unless `z + σ` is in the polygon or the periodization is analysed; the paper's chart separation (`chart_separation`) is only the generic separation lemma. The cover `hcover` keeps the witnesses `FirstChartEdge` / `AdjacentChartEdge` as named.
- Assembled: `noBlackPairRise_of_cover` (SheetCover.lean): `NoBlackPairRise (standardField word) shortShift` from the named cover (chart witnesses, `inputExit`, the H drop with `hweb` inside its witness) and the closed leaves. Checks: `checks/SheetCover.lean` (7 `#print axioms`, standard axioms only). Zero warnings and errors in the sandbox log; root build clean.

### Task 66 status (ChartPeriods, ChartShift, ChartSeparation, ChartGrades, ChartCommon, ChartWitness, InputExit, HWeb)

- (2) the charts at the shifted points. PROVED: `f = quarterTurnField G` is `U_p`-periodic with constant 0 (`quarterTurnField_Upar_period`, from the conjugate packet, `coherentConstantV_eq`, `harmonicGrid_sub_even`; numerics in `scripts/sheet_chart_shift_check.py`); `A(x + σ) = A(x)` and `C(x + σ) = C(x) − 2` (`sheetA/C_add_shortShift`; `ε a_q·U_p = −2`); `A(x − εU_q) − A(x) = p(x − l_v)` and `C(x − εU_q) − A(x) = Ψ(x) + p(x − l_v − e)` (`sheetA/C_sub_eps_Uq`, paragraph 5); `sheetStep = sheetOffset`.
- The chart separation, in the grades: `sep_even_centre`, `sep_odd_centre` (linear, `omega`, with the even windows and the gap `L + 2 > L`), and the common chart `common_chart_option`: for `c, i ∈ E` with `i` an input of `c` and both shifted grades in the `t`-range, `(c + σ, i + σ ∈ E)` or `(c − εU_q, i − εU_q ∈ E)`. Numerics: `scripts/chart_common_k_check.py` (no failure on ten words), `scripts/sep_abstract_check.py`.
- The witnesses: `firstChart_witness` (strict root `Ψ c ≥ 1`; the shifted values `min(0, Ψ − 2)`) and `adjacentChart_witness` (`Ψ c ≥ 0`, `Ψ i ≥ 1`). Both need the retention `sheetPolicyA P c i`, which stays NAMED (`hret`).
- (3') the input exit: PROVED. `InputLowerExit` (`c, i ∈ E`, `Edge i c`, `t(i) − 2 < a(i) − T`), `input_exit_window` (the parity table: `t(c) = t(i) ± n` if `c` even, `± d` if `c` odd, with `n ≥ 3`, `n + 2 ≤ d` from the proper word), and `slip_increment_zero_of_input_exit` (same slip, via `slip_eq_two_of_window`).
- (4) `hweb`: PROVED on the free H cut: `parentTGrade_bounds_of_freeH` (`0 ≤ t_p ≤ N + D`) and `hweb_of_freeH`. The argument is the identity `L · t_p = L_p · t + ε(x + y)` (every site) with `t, x + y ∈ [0, L − 1]` on the free H cut (from the `s`-window and `T(x+y) = L s − 2nt`, parity, and `n, d` odd), so no floor step is needed. W1's `H_endpoint` covers the even residues of the same identity; numerics agree (`scripts/freeH_tp_check.py`, `scripts/freeH_odd_check.py`). Deviation from the note: I did not use `H_endpoint`/`residue_*`.
- The cover `noBlackPairRise_of_chart_cover` (ChartWitness.lean): `NoBlackPairRise (standardField word) shortShift` from the named `hrep` (paragraph 2 and the deck representative), `hstrict` (strict root and target `Ψ c, Ψ i ≥ 1`; the tie and `C` cases are reflected in the paper and are NAMED), and `hret` (matched-policy retention). The centre exit (`not_rising_of_centre_exit`) and the input exit (`not_rising_of_input_exit`) are closed; the first and adjacent charts are closed by `first_chart_excluded` and `adjacent_chart_excluded`. The negative-chart drops (`nonfree`, `H`, `V`, `exc`) are not used on this path; they belong to the tie/`C` reflection.
- Checks: `checks/ChartWitness.lean` (18 `#print axioms`, standard axioms only; no `sorryAx`). Zero warnings and errors in the sandbox logs; root build clean (2560 jobs).

### Task 67 status (RepInputs.lean, ChartWitness.lean; supersedes the task 66 rows for hrep, hret)

- (1) hrep: PROVED in its usable form. `ChildFrame.rising_centre_input_mem` and `ChildFrame.black_input_mem`: a black centre in `E` has both inputs in `E`, by the exit lemma `W1Exit.exit_centre_on_boundary_spectrum` and `ChildFrame.laplacian_eq_zero_of_boundary` (a boundary-spectrum centre is white: translate by `shiftV (−k)` onto the H-strip, where `F = 0`, or by `shiftU k` onto the V-strip, where `F = harmonicGrid`). The literal form "every rising pair has its inputs in `E`" is false in general; the lattice acts on rising pairs (`laplacian_add_lattice`, `slip_add_lattice`: the slip shifts by `2j`), and `rising_translate` moves a rising pair into `E`, so `ChildFrame.noBlackPairRise_of_E` reduces `NoBlackPairRise` to rising pairs with centre in `E`.
- (2) hret: PROVED from the strict centre bound. `sheetPolicyA_of_strict`: `Ψ(c) ≥ 1` makes `sheetMin = sheetA` at `c` and both its inputs (`sheetMin_A_at_input`, `sheetMin_A_of_strict_root`), so `laplacian F c = laplacian G (zTurn (c − sheetShift))` (`laplacian_sub_even`, `i3_laplacian_quarterTurn`, even `sheetShift`). A black `c` gives a black parent; the quota retains both inputs; `zTurn (i − sheetShift)` is one of them (`i3_edge_Z`). The white-parent argument of paragraph 3 is not needed for hret; it belongs to the tie case of hstrict.
- (3) hstrict: NAMED, not proved. `noBlackPairRise_of_chart_cover_strict` needs only `hstrict : ∀ c i, RisingBlackPair … c i → c ∈ E → 1 ≤ sheetDiffW word c ∧ 1 ≤ sheetDiffW word i`. Open: the tie (`Ψ = 0`) and `C` (`Ψ ≤ −1`) cases. The sheet exchange gives `Ψ(R z) = −Ψ(z)` (`sheetDiff_antisymm_of_exchange`), but the reflection does not map a rising pair at `c` to a rising pair at `R c`: with `D z = F z − F (z + σ)` and the packet reflection `F (c₀ − z) = F z − tGrade z + k`, `D (R z) = D (z − σ) + 2`, so the reflected configuration is based at `c − σ`. Paragraph 3 must therefore reflect the sheet edge (η), not the pair. Paragraph 5's tie reflection needs its text, and the drops (`nonfree_drop_excluded`, `H_drop_excluded`, `exceptional_drop_excluded`, the V-block contradiction) are proved but not yet wired to this case.
- Checks: `checks/RepInputs.lean` (16 `#print axioms`, standard axioms only, no `sorryAx`). Zero warnings and errors in the sandbox logs for `RepInputs`; root build `FLatticePaper` clean (2562 jobs).

### Task 68 status (SlipReflect.lean; supersedes the task 67 hstrict row)

- The reflection identity, checked numerically (`scripts/slip_reflect_check.py`: 623 points, zero failures) and proved (`ChildFrame.slip_reflect`): `D_{−σ}(R z) = D_σ(z) − 2`, from the packet reflection `F (R z) = F z − tGrade z + k` and `tGrade σ = −2`. This is the lead's `D_{−η}(Rz) = D_η(z) − 2η` with `η = 1`.
- PROVED: `laplacian_reflect` (R preserves the Laplacian), `reflect_input_neg/pos` (R swaps the two inputs, the centre is even), `reflect_mem_closedPolygon` (E is symmetric under R: `t(centre) = L − T`, `s(centre) = T + 2n`), `rising_reflect` (a rising pair for `σ` at `(c, i)` gives a rising pair for `−σ` at `(R c, R i)`), `sheetDiffW_reflect` (`Ψ (R z) = −Ψ z`, from `sheetExchange_of_packet`).
- PROVED: `chart_excluded_of_bounds`: a rising pair for `σ` with centre in `E` and both `Ψ ≥ 1` is excluded (the A-case for `+σ`; the cover's argument with `hret` from `sheetPolicyA_of_strict`).
- PROVED, with two named leaves: `noBlackPairRise_of_signs` gives `NoBlackPairRise σ` from `hNeg` (the A-case for `−σ`: a rising `−σ` pair with centre in `E` and both `Ψ ≥ 1` is impossible) and `hTie` (a rising `σ` pair with centre in `E` and `Ψ = 0` at the centre or the input is impossible). Mixed signs are impossible by the unit bound (`sheetDiff_unit`). Both negative is the reflection to `hNeg`.
- NOT DONE: (a) the A-case lemmas for `−σ`: the first chart (`min(0, Ψ + 2)` at `η = −1`), the adjacent chart with `Ψ ≥ 1` at the input, and the negative-chart drops, all for `σ' = −shortShift`; (b) the tie case of paragraphs 3 and 5 (Q3.md l.13, l.17–28): retention at tied targets, a tied target forcing a tied centre on A-contacts, reflection of tied adjacent charts to the negative orientation; (c) `OddBlackNoRise` through `OddRise`.
- Checks: `checks/SlipReflect.lean` (9 `#print axioms`, standard axioms only, no `sorryAx`). Zero warnings and errors in the sandbox logs; root build `FLatticePaper` clean (2567 jobs).

### Task 69 (a) status (NegChart.lean; the A-case for −σ)

- The reduction is by reflection, not by new chart lemmas. For a rising pair `(c, i)` for `−σ` with `c ∈ E` and `Ψ ≥ 1` at both ends, `rising_reflect_neg` gives the rising pair `(Rc, Ri)` for `σ`, and `reflect_mem_iff` (`E` is symmetric) moves the common chart. So the exits are the lower-exit lemmas of the `σ`-cover at `(Rc, Ri)`, and the common chart is `common_chart_option` at `(Rc, Ri)`, transported by `R`.
- Option 1 (`c − σ ∈ E`): PROVED, `neg_first_excluded`. `A` is `σ`-periodic and `C (z − σ) = C z + 2` (`sheetA_sub_shortShift`, `sheetC_sub_shortShift`), so `F (c − σ) = min (A c, C c + 2) = A c` and `D_−(c) = 0` is even: no rise. (The paper's `min (0, Ψ − 2η)` at `η = −1`.)
- Option 2 (`c + εU_q, i + εU_q ∈ E`): reduced to the arithmetic core `neg_chart_arith` and `nonfree_drop_excluded`. The `U`-period gives `F (z − σ) = F (z + εU_q)` (`F_sub_shortShift`, via `z − σ = (z + εU_q) + shiftU (−ε)` for any integer `ε`), so `D_−(z) = −min (a z, B z)` with `a z = A (z + εU_q) − A z = jumpA (z − l_v)` (`sheetA_uq_eq_jumpA`) and `B z = C (z + εU_q) − A z`. The rise `min (a c, B c) − min (a i, B i) = 1` with `0 ≤ a ≤ 1` and `B c ≤ B i` (retention) forces `a c = 1`, `a i = 0` on the retained edge, excluded by `nonfree_drop_excluded`. Retention for `−σ` is `sheetPolicyA_of_black` (the colour argument, no `σ` sign).
- Named leaves (the two paper facts): `hG1`, the unit bound. For `z ∈ E`, `zTurn (I − (z − l_v)) ∈ E_conj` (then `unit_of_polygon` gives `0 ≤ a ≤ 1` from `jumpA_eq_cutPrice` and the price range). `hbmono`, the raw slip `B = C (· + εU_q) − A` does not decrease along the matched edges. `OldPolicyData.bFun` is abstract data, so this is not yet the policy's `bNondecreasing` field; the identification of `bFun` with the sheet-defined raw slip is still open.
- Result: `noBlackPairRise_of_leaves` gives `NoBlackPairRise σ` from `hG1`, `hbmono` and the tie leaf `hTie` (task 69 (b)). `neg_sign_excluded` is the A-case for `−σ`.
- Checks: `checks/NegChart.lean` (10 `#print axioms`, standard only, no `sorryAx`). Zero warnings and errors in the sandbox logs; root build `FLatticePaper` clean (2568 jobs).

### Task 69 (b) status (RawB.lean, NegChart.lean, TieParity.lean; the lead's interface decisions)

- `OldPolicyData`: the abstract `bFun`/`bNondecreasing` are replaced by `rawSlipNonincreasing : ∀ η = ±1, NonincreasingAlong (fun y => G y − G (y + η • shortShift)) retained` (the conjugate's raw slip does not increase along retained edges). `W1Witness` builds unchanged.
- PROVED: `sheetB_eq`, the paragraph-6 identity `C (z + εU_q) − A z = (1 + ε) − D'_ε(Z (z − l_v))` (from `paragraph6_of_strong`, `sheetOffset = V_q + εU_q`, `phaseW = (1 + ε)/2`); hence `hbmono_of_raw`: `B` is nondecreasing along the matched edges, with no leaf.
- PROVED: `a_unit_bound`: `|a c − a i| ≤ 1` for an edge `(i, c)`, from `HasUnitPrice` via `jumpA_eq_cutPrice` and `reflect_edge_even`, `i3_edge_Z` (global, no membership).
- NOT derivable from the unit increments: the endpoint range `0 ≤ a i`, `a c ≤ 1`. Counterexample to the unit-only arithmetic: `a i = −6`, `B i = 100`, `a c = −5`, `B c = 0` satisfies `min (a c, B c) − min (a i, B i) = 1`, `B c ≤ B i`, `a c ≤ a i + 1`, with `a c ≠ 1`. The range is the price range of `a` on `E` (`priceRange` needs the polygon membership of `zTurn (I − (z − l_v))`); it stays the named leaf `hA01` in `neg_adjacent_excluded`, `neg_sign_excluded` and `noBlackPairRise_of_leaves`.
- PROVED: `sheetDiffW_eq_one_of_parity`: for a rising `σ` pair with `c + σ ∈ E`, the centre slip is `min (A c, C c) − min (A c, C c − 2)`, which is odd iff `Ψ c = 1`. So a tie at the centre (and any `Ψ c ≠ 1`) is excluded by parity in option 1. `rising_option1_excluded`: option 1 (`c + σ, i + σ ∈ E`) is excluded outright, with no tie hypothesis (the first chart needs only `Ψ c ≥ 1`).
- Still open (task 69 (b)): option 2 (`c − εU_q, i − εU_q ∈ E`) with a tie endpoint, i.e. the leaf `hTie` restricted to option 2; the paper's l.21 reflection to the negative orientation with C at both ends. The negative-chart lemma `neg_adjacent_excluded` already works for `Ψ ≥ 0` at both ends, provided the retention of a tied centre holds.
- Checks: `checks/NegChart.lean` (12 `#print axioms`), `checks/TieParity.lean` (2); standard axioms only. Zero warnings and errors in the sandbox logs; root build `FLatticePaper` clean (2573 jobs).

### Task 69 (b), second part (NegChart.lean, TieOpt2.lean; the slip-range leaf and the option-2 ties)

- The endpoint values of the negative chart come from the slip, as the lead specified: `D_−(c) = D_+(R c) − 2` (`slip_reflect_gen`), so `D_−(c) ∈ [−2, 0]` from the word's slip range on `E`; the rise parity gives `D_−(c) = −1`, and the rise gives `D_−(i) = 0`. So `neg_adjacent_excluded` now takes the slip range `hslip` (`0 ≤ D_+ ≤ 2` on `E` for the word's standard field) instead of the price-range leaf `hA01`. `neg_chart_arith` now takes `mc − Ac = 1` and `mi − Ai = 0` and the unit increment (`a_unit_bound`).
- Leaf: `hslip`. It is the slip-range field of the word's strong estimates (`i3_slipFields_of_strong`, which also needs `StarZoneInputs` and `VArcInputs`, supplied by the induction); it is not derived here.
- PROVED: `sheetPolicyA_of_nonneg` (retention at a centre whose star has `Ψ ≥ 0`, ties allowed: `F = sheetA` on the star). `neg_adjacent_nonneg`: the negative drop with `Ψ ≥ 0` at the centre and its star (ties allowed).
- PROVED: `plus_adjacent_nonpos_excluded`: a rising `σ` pair in option 2 whose centre star has `Ψ ≤ 0` is excluded by reflection to `neg_adjacent_nonneg`. `plus_adjacent_target_excluded`: a strict target `Ψ i ≥ 1` with a centre star `Ψ ≥ 0` is excluded by the positive adjacent chart and `sheetPolicyA_of_nonneg`.
- NOT COVERED (the residual of `hTie` in option 2): a tied centre whose star contains a `Ψ = −1` input (mixed star), and a tied target under a strict centre (`Ψ c = 1, Ψ i = 0`, which the fix's l.21 says cannot occur: a tied target forces a tied centre). Both need the winner-retention argument of l.13 (the white parent at a black minimum) and the tied-target claim of l.21, not yet formalized.
- Checks: `checks/NegChart.lean` (14 `#print axioms`), `checks/TieOpt2.lean` (4); standard axioms only. Zero warnings and errors in the sandbox logs; root build `FLatticePaper` clean (2583 jobs).
