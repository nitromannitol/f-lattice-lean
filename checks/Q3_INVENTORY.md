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

### Task 69 (c) status (OddAssembly.lean; OddBlackNoRise)

- `oddBlackNoRise_of_leaves`: `OddBlackNoRise (standardField word) σ` from `oddBlackNoRise_standard` (OddRise.lean), with `NoBlackPairRise` from `noBlackPairRise_of_leaves` (the conjugate's strong estimates and the old policy). The named leaves are `hslip` (the word's slip range on E), `hU` (the word's unit slip, the `F1_unitSlip` field of the word's slip fields, which also needs `StarZoneInputs` and `VArcInputs`), and `hTie` (the option-2 ties with a mixed star, and a tied target under a strict centre).
- Checks: `checks/OddAssembly.lean` (1 `#print axioms`, standard). Root build `FLatticePaper` clean (2584 jobs), zero warnings and errors.

### Task 69 final status (TieReduce.lean; the narrowed leaves; supersedes the hslip, hU and hTie rows)

- DISCHARGED from the conjugate's strong estimates: `slipRange_of_strong` (the word's slip range `0 ≤ D_+ ≤ 2` on `E`, via `slipFields_of_strong` with `arcInputs_of_strong`, which use `openInputs_of_strong`), `hU_of_strong` (the word's unit slip), and `packet_of_strong` (the word's packet, via `packet_of_openInputs_step`). So `hslip`, `hU` and `hpk` are no longer hypotheses.
- Configuration `Ψ c = 1, Ψ i = 0` is EXCLUDED by `sheetDiff_mono_A`: `strict_centre_target` gives `Ψ i ≥ Ψ c` for any rising pair with a strict centre (the retention `sheetPolicyA_of_black` holds for either sign), so the strict centre forces a strict target.
- `tie_excluded_of_narrow`: every tie `Ψ c = 0 ∨ Ψ i = 0` on a rising σ pair is excluded, except option-2 ties whose centre has an input with `Ψ = −1`. The `Ψ ≤ −1` ties reflect to the strict-centre case; the option-1 ties are excluded by parity; the option-2 ties with a `Ψ = +1` input reflect to a −σ option-2 tie with a `−1` input; the option-2 ties with all inputs `≤ 0` are excluded by `plus_adjacent_nonpos_excluded`.
- EXACT REMAINING LEAVES (Q16): `hResP` (σ) and `hResN` (−σ): an option-2 rising pair with a tied centre (`Ψ c = 0`) and an input with `Ψ = −1`. Nothing else is assumed beyond the conjugate's `StrongEstimates` and the `OldPolicyData` `P`.
- Checks: `checks/TieReduce.lean` (6 `#print axioms`, standard only, no `sorryAx`). Zero warnings and errors in the sandbox logs; root build `FLatticePaper` clean.

### Task 70 part 1 status (StrongHeadline.lean: the policy headline)

- `odometersTheorem_of_policy`, `hyperbola_of_policy`, `circlePacking_of_policy`: the headline with `hodd` replaced by the conjugate's old policy at each proper word (`hpol`, with some forced seed) and the two narrowed tie leaves at each proper word (`hResP`, `hResN`), through `oddBlackNoRise_of_narrow`. The other hypotheses (pure and two-power base inputs, residuals, `hbulk`) are unchanged.
- Checks: `checks/StrongHeadline.lean` (three new `#print axioms`, standard only). Root build clean.

### Task 70 part 2 status (ComparisonFields.lean: paragraph 4, the comparison fields)

- PROVED: `cmpLow_le_of_price` (`cmpLow ≤ F` on the closed polygon: `P ≥ c₀ − 1`, the word's price range `hWord.priceRange`, the input `StrongEstimates word`); `cmpUp_le_of_slip` (`F(z+σ) ≤ F z`, `D_+ ≥ 0`, from `slipRange_of_strong`); `cmpDown_le_of_slip` (`F(z−σ) − 2 ≤ F z`, `D_− ≥ −2`, from the slip bound at the reflected site and `slip_reflect_gen`).
- PROVED: `contact_black_E`: at a black centre `c ∈ E` with `F c = m c` for a binary `m ≤ F` on `E`, both inputs are contacts (`contact_black` with the inputs in `E`, `black_input_mem`).
- NOT FORMALIZED: the conclusion of paragraph 4 (`P` and `J_η` do not increase along black and forced white edges). It needs the unit-proof transfer through the finite square proof of `SquareClauses` (`forced_sound`) and the W1 exclusion of the resulting empty clause (the unseeded system of `F` by even translation and affine addition). These are the named inputs of paragraph 4 and are not yet stated as Lean hypotheses.
- Checks: `checks/ComparisonFields.lean` (4 `#print axioms`, standard only). Zero warnings and errors in the sandbox logs.

### Task 70 part 2 (c) status (ComparisonTransfer.lean: P, J₊, J₋ monotone on black and forced white edges)

- PROVED, no hypotheses beyond `StrongEstimates`: `price_nonincrease_black`, `jplus_nonincrease_black`, `jminus_nonincrease_black` (black roots: a contact root has both inputs as contacts by `contact_black_E`; otherwise the value bound of the range applies).
- PROVED from the two named hypotheses below: `price_nonincrease_forced`, `jplus_nonincrease_forced`, `jminus_nonincrease_forced`. The forced-contact step `forced_contact_transfer` is the only use of (T) and (W).
- HYPOTHESIS (T), the contained unit-proof transfer (`hT`): a contact forced-white root whose forced input is not a contact produces a finite empty clause `EC m` for its comparison field `m` (source: B2_INDEPENDENT_PRERANK_AUDIT §3). The Lean form is the one-step statement for `SquareClauses.ForcedEdge`; the source gives it as an induction on the contained unit proof, which is not formalized.
- HYPOTHESIS (W), the W1 no-refutation transferred to `m` (`hW : ¬ EC m`): the unseeded closure of each comparison field has no empty clause (source: §3, "the current W1 global no-refutation statement transfers to it"). `EC` is an abstract predicate here; no Lean statement of the global W1 no-refutation exists in the repo (`SquareClauses.unseeded_forces_standard_window` is one concrete window).
- Checks: `checks/ComparisonTransfer.lean` (six `#guard_msgs` on `#print axioms`, each exactly the standard three). Zero warnings in the build.

### Task 70 part 2 (c) status, second pass (ComparisonEmpty.lean: the concrete empty clause and (W))

- DEFINED: `EmptyClause G` (unseeded unit closure of `G` derives a conflict): (i) a white site with two distinct forced inputs; (ii) a unit square with every corner black or forced into the square.
- DEFINED (W): `HasSatSelection F`, a white input selection satisfying every square clause. `hasSat_of_strict` derives it from a strictly decreasing rank (`squareClauses_of_strict`).
- PROVED: `not_emptyClause_of_sat` (a satisfying selection excludes `EmptyClause`); `not_emptyClause_of_cmp` (for each comparison field `m`, from (W) for `F = standardField word`, via the even translate `z ↦ sel (z + t) − t`, since `laplacian m c = laplacian F (c + t)` for `t = −v`, `σ`, `−σ`).
- PROVED from (T) with the concrete `EmptyClause` and (W): `forced_contact_of_sat`, `price_nonincrease_forced_of_sat`, `jplus_nonincrease_forced_of_sat`, `jminus_nonincrease_forced_of_sat`. (T) is the hypothesis `hT`, for unseeded `ForcedEdge` only.
- NOT PROVED: (T). The induction base holds: when every other corner of the proof square is black, the gap identities force all four corners black for `m`, which is an all-black square, hence `EmptyClause m`. The step fails: a white corner `x` of the square has `laplacian m x = −(gap of its outside input)`, which the gap identities do not determine, so the all-black conclusion is unavailable.
- Checks: `checks/ComparisonEmpty.lean` (eight `#guard_msgs` on `#print axioms`, each the standard three).

### Task 71 status, step 1 (CanonicalSigned.lean: the producing direction to OldPolicyData)

- DEFINED: `CanonicalSignedPolicy frame F`, extending the S3 `CanonicalPolicy` with the W1 selection (`sel`, `sel_input`, `white_policy`, `squares`), the raw slip sign −1 (`rawSlipMinus`, Q1.md l.38), the chain comparison (`chainNonincreasing`, Q1.md l.40), reflection about `I` (`reflection`) and the exceptional west input (`westAtException`).
- PROVED: `oldPolicyData_of_canonical`: `OldPolicyData frame F (fun _ _ => False)` from the canonical signed policy. Derived: `quota` (the canonical quota); `priceNonincreasing` (`nonincreasingP`, since `cutGrade F 1 0 1 = price F`); the raw slip for both signs (sign +1 from `permitted`, sign −1 from `rawSlipMinus`); `forcedRetained` (`forced_sound` on the selection, with `white_policy`).
- NOT DERIVABLE from the other fields: `chainNonincreasing`. The chain potential `Φ_η = D_η + P(· + ησ)` compares `P` at the shifted edge `(c + ησ, i + ησ)`; the policy is not known to be invariant under `ησ`, and `ησ` need not lie in the child deck span. Arithmetic example (frame validity not checked): child `3/5` of parents `1/2`, `1/1` gives `σ = (−4, −2)`, which is not in the span of `(5, 3)` and `(−2, 8)` (determinant 46). `reflection` and `westAtException` are fields: they come from the symmetric definition and the W1 prescription.
- Checks: `checks/CanonicalSigned.lean` (six `#guard_msgs`, standard axioms only), after step 2.

### Task 71 status, step 2 (CanonicalHeadline.lean: the headline restated)

- PROVED: `FLatticePaper.odometersTheorem_of_canonical` (CanonicalHeadline.lean): the headline of `odometersTheorem_of_policy` with `hpol` replaced by `hcan : ∀ word, … → Nonempty (CanonicalSignedPolicy (frameAt (conjWord word)) (standardField (conjWord word)))` at proper words; the old policy data is produced by `oldPolicyData_of_canonical` with the empty seed.
- Fields of `OldPolicyData` needing more than the canonical fields: `chainNonincreasing`, `reflection`, `westAtException` are carried as canonical fields (no derivation from the rest); `priceNonincreasing`, `rawSlipNonincreasing` (both signs), `forcedRetained`, `quota` are derived.
- Checks: `checks/CanonicalSigned.lean` (six `#guard_msgs`, standard axioms only). Root build clean (2595 jobs before this step, no change in the import graph beyond the headline line).

### Task 72 (b): the reflection restricted to black and forced roots, derived

- DEFINED: `OldPolicyData.reflection` now carries the hypothesis `laplacian G c = -1 ∨ ForcedEdge G seed c i` (black or forced root). This is what `nonfree_drop_excluded` uses: Q3.md l.30, a nonfree root keeps both inputs (black) or its unique forced edge. `parentPolicy_reflection` and `nonfree_drop_excluded` take the same root hypothesis (`hroot`); the three cover statements (`SheetCover`, `SheetCharts`, `SheetCases`) carry it in the drop disjunct; the two `NegChart` call sites supply it from the extracted black roots `blackRoot_of_black`, `blackRoot_of_nonneg`.
- PROVED (`ReflectionI.lean`): `incomingNeg_reflectI`, `incomingPos_reflectI`, `edge_reflectI`, `laplacian_reflectI` (for `F (I − z) = F z`), `mem_corners_reflectI` (the square `squareCorners a b` goes to `squareCorners (−a) (−2 − b)`), `forced_reflectI` (unseeded forced edges are carried by `I`, by induction on `ForcedEdge`).
- DERIVED (`CanonicalSigned.lean`): `reflection_of_canonical`: black roots from the quota (`I − c` is black by the symmetry, and `I − i` is an input of `I − c` by `edge_reflectI`, which uses the new field `policyEdge : retained c i → Edge i c`); forced roots from `forced_reflectI` and `forcedRetained`. The field `reflection` is removed from `CanonicalSignedPolicy`.
- HEADLINE (`CanonicalHeadline.lean`): the symmetry `F (I − z) = F z` is taken from `standardField_iRefl` at the strong estimates of `conjWord word`.
- Checks: `checks/ReflectionI.lean` (eight `#guard_msgs`, standard axioms only). Root build clean (2596 jobs).

### Task 72 (a): the chain field as a statement about the pair of policies (CanonicalSigned.lean)

- DEFINED: `ChainPairData frame F η P`: an opposite-sign policy `opp` on `F` with `oppRawSlip` (`D_{−η}` nonincreasing along `opp`), and `chainNonincreasing`: `Φ_η` nonincreasing along the F-policy `P`. `CanonicalSignedPolicy.chainPairs` replaces the former field `chainNonincreasing`.
- PROVED: `translated_rawSlip`: the translated g-policy `c ↦ opp (c + ησ)` has `D_η` nondecreasing along it, from `D_η(z) = −D_{−η}(z + ησ)`.
- NOT PROVED (the conclusion of STRONG_PRICE_AND_ALTERNATE_STEP §4): `chainNonincreasing`. TWO_RANK_RAW_PHI_AUDIT reduces it to one exclusion: a raw rise along a retained F-edge needs both parents free with opposite chosen directions at a shifted P edge (its "remaining geometric exclusion"). The audit does not certify that exclusion, so the field stays a named input.
- Numeric (scripts/chain_shift_check.py): the identities `D_η(z) = −D_{−η}(z+ησ)` and `Φ_η(z) = F(z) − F(z+ησ−v) − ε a·(z+ησ)` hold on 2000 random integer fields. For all 628 proper Farey children (parent odd `N/D`, sibling even `n_q/d_q` with `|N d_q − D n_q| = 1`, child `(2N+n_q)/(2D+d_q)` in `(0,1)`), `σ` is NOT in the child deck span `{iK + jT}`: `det(K, σ) = 2ε² = 2`, while `det(K, T)` is the period denominator, at least 3 for proper children.

### Task 72 (c): westAtException (not derived from the current frame; numeric check)

- Numeric (scripts/exceptional_vertex_check.py): `V_p + I = (N − D + 1, N + D − 1)` is the `vLast` (`V + (1, −1)`) of the earlier frame whose child is the parent `N/D`. It lies in `freeV` of that frame for all 737 odd proper parents checked. Its prescribed direction is `(η, 0)`, with `η` the earlier vertical sign.
- West (`incomingNeg`, direction `(−1, 0)`) needs `η = −1` when `ε = 1`, i.e. `η = −ε`. The reading "(−, ε)" would give east; the sign convention needs checking against the source.
- Not derived: the prescription at `vLast` is a fact of the parent frame's canonical policy, not of the current frame's fields. `westAtException` stays a field.

### Task 72 (d): rawSlipMinus stays a field

- `rawSlipMinus` (sign `−1`, Q1.md l.38) remains a canonical field. Its prescribed directions are Q13, parked. The sign `+1` is derived from `permitted`.

### Task 72 (nonfree roots): the W1Forced root condition of the drop lemma (NonfreeRoot.lean)

- The cover drop disjunct (SheetCover, SheetCharts, SheetCases) now takes the drop root to be strict interior (`W1.StrictInterior`, the nonfree roots), and takes the hypothesis `hW1 : W1Forced (frameAt (conjWord word)).child.num .child.den (standardField (conjWord word))`. The earlier "black or forced" root input is no longer a separate hypothesis.
- PROVED `nonfree_root_forced`: at a strict-interior root of the old policy, black or the unseeded forced edge to the retained input. It uses `W1Forced` (forced edge `o`) and the new field `OldPolicyData.forcedWhiteUnique`: the only retained input at a white with an unseeded forced edge `z → o` is `o`.
- DERIVED `forcedWhiteUnique_of_canonical` (CanonicalSigned): `white_policy` plus `forced_sound` on the selection.
- CHANGED: the reflection hypothesis and `nonfree_drop_excluded` use unseeded forced edges (W1 is unseeded).
- Checks: `checks/NonfreeRoot.lean` (three guards), `checks/CanonicalSigned.lean` and `checks/ReflectionI.lean` pass. Root build clean (no warnings in the root log).

### Task 72 (Q1 paragraphs 7–8): the uniform escape horizon (UniformEscape.lean)

- PROVED `uniform_escape_horizon`: under `RestrictedNoFort`, a deck cover `sites`, the binary Laplacian and the deck covariance of the escape game, there is one horizon `m ≥ 1` with `RestrictedEscapesWithin (grade site) m site` for every site. The depths are finite on the cover (`restrictedNoFort_iff_cover`), escape is equivariant under the deck (`restrictedEscapesWithin_add`), and the depth is monotone in the horizon; the maximum over the finite cover is the horizon (`Finset.sup`).
- PROVED `andOr_rank_of_restrictedNoFort`: the rank of `andOr_rank_of_escape` with that horizon, from the restricted no-fort condition alone.
- The stopping bound `t + m K(z_t) ≤ m K(z_0) + m + m² d_0` of Q1 l.32 is the value bound `restrictedValue_le_of_uniform_escape` (`horizon · K + (horizon + horizon² · bound)`, `bound = d_0`), already formal in RestrictedBellmanRank. Not re-proved.
- Checks: `checks/UniformEscape.lean` (two guards, standard axioms only). Root build clean (no warnings in the root log).

### Task 72 (nonfree bridge): a nonfree site has a deck translate in StrictInterior (NonfreeBridge.lean)

- DEFINED: `Nonfree frame z := ∀ v ∈ span, z + v ∉ freeH ∪ freeV` (not on the free H/V set modulo the deck, the lead's wording).
- PROVED `outside_SI_free`: a point `w` of the closed polygon outside `W1.StrictInterior` lies in `freeH ∪ freeV`, or `w − V` or `w − K` does. Case analysis on the parity of `w` and on the failing strict inequality. Deck vectors: `K = (d, n)` (`s(K) = T`, `t(K) = 0`) and `V = (n − d, n + d)` (`t(V) = −T`, `s(V) = 0`). The upper t-strip is in `freeH` directly, the lower t-strip is in `freeH` after `−V`, the lower s-strip is in `freeV` directly, the upper s-strip is in `freeV` after `−K`.
- PROVED `nonfree_bridge`: `Nonfree frame z → ∃ v ∈ span, StrictInterior (z + v)` (`exists_shift_mem` puts a translate into the closed polygon).
- Numeric (scripts/nonfree_bridge_check.py): for 47 odd children `n/d` (`n + 2 ≤ d`, coprime, `d ≤ 21`) and sites in a box, both "no translate on E and boundary spectrum" and "no translate in freeH or freeV" give a strict-interior translate. A first run with a deck window `R = 4` gave failures only at the box corners, which vanished for `R ≥ 8`.
- Checks: `checks/NonfreeBridge.lean` (two guards, standard axioms only). Module log has no warnings.

### Task 72 (nonfree root, deck form): the cover condition is literally "nonfree" (DeckForced.lean)

- PROVED `laplacian_span_inv`: the Laplacian of the standard packet is invariant under the child deck span. The kernel shifts the field by a constant and the transverse vector by an affine function, whose Laplacian is zero. The invariant set is a subgroup (`span_pred`), so it contains the span.
- PROVED `forcedEdge_add`: unseeded forced edges are carried by even translations that preserve the Laplacian (squares and inputs translate).
- PROVED `nonfree_root_forced_nonfree`: a nonfree root of the old policy is black, or its retained edge is the unseeded forced edge. The bridge `nonfree_bridge` gives a strict-interior translate, `W1Forced` gives the forced edge there, translating back gives it at the root, and `forcedWhiteUnique` identifies the retained input.
- CHANGED: the drop disjunct of SheetCover, SheetCharts and SheetCases now reads `Nonfree (frameAt (conjWord word)) (zTurn x)` (was the strict-interior root). The root condition uses `nonfree_root_forced_nonfree` with `hSE.packet`. The hypothesis `hW1` is unchanged.
- Checks: `checks/DeckForced.lean` (four guards, standard axioms only). Root log has no warnings.

### Task 72 (Q1 paragraph 6): the ordered free-site exclusions, the '+' row (checks/FREE_SITE_EXCLUSIONS.md)

- Numeric (scripts/free_site_exclusions.py): for every odd coprime child with `d ≤ 31` (106 children) and every `r ∈ [0, L−1]` (3422 rows), the '+' row lists each free deck class once; its consecutive V-passages (N, N–W, W–N–E: 121418) and descending H-passages (E, E–N, N–E–S: 76398) have no free interior site (194394 interior sites); the curves are in the Lean free sets. Transitions (tip routes, 10160) are counted, not classified.
- Reduction to `main`: none of the passage, tip or fan steps is a Lean lemma. The Lean facts used: `ChildFrame.freeH/freeV` (S3FreeBoundary), `Q3White.laplacian_eq_zero_of_freeV`, `Q3Para10.index_of_freeV`/`block_mem_freeV`/`VpI_not_freeV`, and `NonfreeBridge.outside_SI_free` (task 72).
- Named steps: FIXED_FREE_GAME_AUDIT §3–§9 and TIP_THEOREM, ALL_SLOPE_STEP sections are listed with file paths in the report.
- Scope: a numeric check, not the per-entry implications (E), (P), (F).

### Task 72 (FIXED_FREE §3-§4): the short-passage middles are nonfree, for all parameters (ShortPassages.lean)

- PROVED `nonfree_of_avoid`: a site is nonfree when the H spectrum avoids all `t − jT` and the V spectrum all `s + iT` (deck translates of a site have `t − jT`, `s + iT`).
- PROVED window lemmas (all parameters, arithmetic with `T ≥ 3L`): `avoid_H_odd_high` (`d < t < T+n`), `avoid_H_odd_low` (`d−T < t < n`), `avoid_H_even_high` (`L−2 < t < T+2`), `avoid_H_even_low` (`L−2−T < t < 2`), `avoid_V_high` (`L−2 < s < T+2−c`), `avoid_V_low` (`L−2−T < s < 2−c`).
- PROVED `nonfree_V_even_left`: an even V middle with `2n+2 ≤ s ≤ 2d−2` (its left neighbour lies in `E`, and its `i = 0` translates are off `E`). PROVED `nonfree_V_even_neg`: an even V middle with `L−2−T < s < 0` (its `i = 0` translates have negative `s`, so they are off `E`).
- PROVED the four route theorems, from the root hypotheses of FIXED_FREE §3–§4: `H_EN_middle_nonfree`, `H_NES_middle1_nonfree`, `H_NES_middle2_nonfree`, `V_NW_middle_nonfree`, `V_WNE_middle0_nonfree`, `V_WNE_middle1_nonfree`.
- The root hypotheses are NOT derived here: H-EN root `c+2 ≤ t(z)` (next endpoint in the even H spectrum) and `s(z) < T+2−2d` (box); H-NES root `n+2 ≤ t(z) ≤ d−2` (internal) and `2n−2 < s(z) < T+2−3d+n` (box); V-NW root `2n+2−c ≤ s(z) ≤ L−2` and `L−1−T+d < t(z) < d` (endpoint spectra); V-WNE root `2 ≤ s(z) ≤ 2n−2` and `2L−1−T < t(z) < n`. They hold on every route for all children with `d ≤ 31` (`scripts/passage_root_hypotheses.py`, `scripts/passage_window_claims.py`).
- Numeric support: spectral avoidance alone excludes every H middle and the odd V middle; the two even V middles need the `E`-argument above (`scripts/spectrum_avoidance_check.py`).
- Checks: `checks/ShortPassages.lean` (nine guards, standard axioms only). Root build clean.

### Task 72 (FIXED_FREE §5-§6 and the staircase box of the free H trace): FreeTraceBox.lean, CanonicalDirections.lean

- PROVED `FreeTraceBox.freeH_box`: every `z ∈ ChildFrame.freeH` satisfies `1 ≤ z.1 ≤ d`, `0 ≤ z.2 ≤ n − 1`. Proof from `mem_closedPolygon_iff`, `hSpectrum`, `tGrade_parity` and the integer lemmas `box_even`/`box_odd` (the integer bounds `x ≥ 1`, `x ≤ d`, `y ≥ 0`, `y ≤ n − 1` each follow from the polygon bounds; no numeric input).
- NOT PROVED (refuted as stated): "root ∈ freeH implies the route windows". Counterexample `(n, d) = (1, 3)`, root `(2, 0)`: it is a free even H site with `t = 2 < c + 2 = 4`, and its E-step `(3, 0)` is itself a free H site. `scripts/free_trace_route_check.py` (d ≤ 15): for `H_EN` and `V_NW` the window holds exactly when the E-step site is not a free site; for `H_NES` and `V_WNE` the window is sufficient, not necessary.
- PROVED §5 (`CanonicalDirections.lean`): `prescribedH_internal_even/odd`, `prescribedV_internal_even/odd`, `prescribedH_H0`, `prescribedV_V0`, `prescribedH_hLast_sub_U` (north), `prescribedV_vLast_sub_V` (`η` east), `prescribedV_odd_minus_one` (north), `prescribedV_even_minus_one` (west). The tip-specific starts `Vp+ex` and `Vp` are not yet shown to be internal V sites.
- PROVED §6: `tip_W0_middle_nonfree` (`v + (1,1)`, `ε = −1`, `t(v) = −B`, `s(v) = 2ε`, under `0 ≤ B`, `5L ≤ T − B`) and `tip_W1_middle_nonfree` (`v + (−1,0)`, `ε = +1`, same hypotheses). These take the tip values of `TIP_THEOREM.md` as hypotheses; the tip's own `t(v)`, `s(v)` are not derived here.
- Checks: `checks/FreeTraceBox.lean`, `checks/CanonicalDirections.lean` (standard axioms or subsets). Root build clean; sandbox logs grep-clean for warning, error, sorry.

### Task 72 (option b and TIP_THEOREM): RouteSteps.lean, CutTipEscape.lean

- PROVED `RouteSteps.freeV_odd_box`: every odd `z ∈ freeV` has `1 − c ≤ x ≤ 0`, `1 ≤ y ≤ L − 2` (integer lemma `vbox_odd`; no numerics). Proof: `s ≤ L−2` forces `x ≤ 0`; `s ≥ 2−c` forces `y ≥ 1`; for `y ≥ L−1` the `s`-window gives `x = 1−c` (parity contradiction) or `x ≤ −c` (contradicting `t ≥ n−T`); `s ≥ 2−c` gives `x ≥ 1−c`.
- PROVED `RouteSteps.freeH_even_s_lt`: every even `z ∈ freeH` has `s(z) < T + 2 − 2d`.
- PROVED `RouteSteps.H_EN_of_step`: an even `z ∈ freeH` with `z + (1,0) ∉ freeH` has nonfree middle `z + (1,0)` (the window `c + 2 ≤ t(z)` is the contrapositive: `t ≤ c` makes the E-step a free site).
- PROVED `RouteSteps.V_NW_of_step`: an odd `z ∈ freeV` with `z + (0,1) ∉ freeV` has nonfree middle `z + (0,1)`.
- H_NES and V_WNE keep their windows (the source's "internal" midpoint conditions; endpoints H_0, H_last, V_0 are separate).
- Numeric recheck with `n ≥ 3` (scripts/free_trace_window_check.py): window ⟺ step not free for H_EN and V_NW.
- PROVED (abstract game, RestrictedBellmanRank) `CutTipEscape.two_edge_escape`: a white root `r` with a white permitted input `u` whose permitted input `y` has grade below the level escapes at depth 2. Instances `tip_W0_escape` (root `v+(1,0)`, `v` even) and `tip_W1_escape` (root `v`, even): the two incoming steps of the tip routes are `incomingPos`/`incomingNeg` as in TIP_THEOREM.
- NOT PROVED: whiteness of the middles and the grade decrease at the port (field values from TIP_THEOREM); the forced-direction identification of the rejected input.
- Checks: `checks/RouteSteps.lean`, `checks/CutTipEscape.lean`. Sandbox logs clean for warning, error, sorry (one lint warning fixed).

### Task 72 (TIP_THEOREM hypotheses, whiteness): TipWhiteness.lean

- PROVED `TipWhiteness.laplacian_eq_zero_of_odd_strip`: an odd site whose vertical star has `s ∈ [1 − 2d + c, 2L − 1 − c]` is white for any field with `HasStrips` (the harmonic s-strip), by `harmonicGrid_harmonic`.
- PROVED `W1_middle_white`: the W1 middle `v + (−1,0)` is white from `s(v) = 2` alone (its star has `s = 2 − L ± c`, inside the strip).
- PROVED `W1_root_freeV`, `W0_root_freeV`: the tip roots `v` (W1) and `v + (1,0)` (W0) are free V sites, from the tip values `t(v) = −B`, `s(v) = 2` (W1) or `s(v) = −2` (W0) and `0 ≤ B`, `5L ≤ T − B`. Hence white by `ChildFrame.laplacian_eq_zero_of_freeV`.
- PROVED `W1_tip_white` (root and middle) and `W0_tip_root_white`.
- NOT PROVED: the whiteness of the W0 middle `v + (1,1)`. Its east input has `s = 3d + n − 2`, outside the harmonic s-strip `[1 − 2d, 2L − 1]`, so it needs the two-sheet evaluation of TIP_THEOREM (`fA`, `fC`).
- NOT PROVED: the existence of the tip vertex `v` with `t(v) = −B`, `s(v) = 2ε` from the parent data (the tip values stay hypotheses); the permits and the grade drop `0 → −1` at the port.
- Checks: `checks/TipWhiteness.lean`. Root build clean; sandbox logs clean for warning, error, sorry.

### Task 72 (TIP_THEOREM tip vertex): TipVertex.lean

- PROVED `TipVertex.tGrade_tipVertex`, `sGrade_tipVertex`, `evenSite_tipVertex`: the tip vertex is the parent's V vertex `V_p = (n_p − d_p, n_p + d_p)` in child coordinates, with `t(V_p) = −B`, `B = L d_p + c n_p`, and `s(V_p) = 2 eps` (identities using `eps_eq`). This derives the tip values that TIP_THEOREM states, so they are no longer hypotheses. The phase is `eps`: W1 is `eps = 1`, W0 is `eps = −1`.
- PROVED `TipVertex.W1_tip_white_of_eps`, `W0_root_white_of_eps`: the W1 root and middle, and the W0 root, are white for `HasStrips F`, given `eps` and the nonbase bounds `0 ≤ B`, `5L ≤ T − B` (kept as hypotheses).
- Checks: `checks/TipVertex.lean`. Root build clean; sandbox logs clean.

### Task 72 (TIP_THEOREM, the W1 escape with grade wired): TipEscape.lean

- PROVED `FLatticePaper.tipJ_port_lt_root`: with `J = ceil(D/2)` (`tipJ D = (D+1)/2`), `J(−2) < J(−1)`: the boundary profiles `D = −1` (root, `J = 0`) and `D = −2` (port, `J = −1`) give the drop.
- PROVED `FLatticePaper.tip_W1_escape_profiles`: the W1 cut tip (`eps = 1`) escapes at depth two in the restricted game with grade `J_η = tipJ (slip F η)`, given `HasStrips`, the nonbase bounds, the boundary profiles (named hypotheses `hD0`, `hD1`, sourced from ANCESTRAL_PSI_V_CUT_PROOF §§1–3 and VArcOffers), and the permits of the two route edges (`hru`, `hpu`, kept general; the source's permits are `slipPermits`, i.e. the sheet gap condition, not yet derived).
- Whiteness of the root and middle comes from `TipVertex.W1_tip_white_of_eps` (no hypothesis).
- NOT PROVED: the W0 middle (sheet evaluation), the permits from the sheet gap, and the boundary profiles themselves.
- Checks: `checks/TipEscape.lean`. Root build clean; sandbox logs clean.

### Task 72 (TIP_THEOREM, the W0 middle through the sheets): W0Sheets.lean

- PROVED the V_p jet `W0Sheets.quarterTurnField_add_tipVertex`: `Fp (x + V_p) = Fp x + (harmonicGrid (x + V_p) − harmonicGrid x)` for `Fp = quarterTurnField (standardField (conjWord w))`. The quarter turn sends `V_p` to minus the conjugate kernel `(d_p + n_p, d_p − n_p)`; `G` is periodic along it with constant `0` (`coherentConstantU_eq_zero`).
- PROVED the harmonic translations `harmonicGrid_add_tipVertex` (`+V_p`, constant `s` with `2s = −n_p − d_p − T_p`), `harmonicGrid_sub_Vq` (`−V_q`), and `harmonicGrid_two_one`.
- PROVED the sheet identities at `eps = −1`: `sheetA_of_eps` (`Fp(z − U_q)`), `sheetC_of_eps` (`Fp(z − V_q) + a_q·z + c_e`), with `sheetShift = U_q`, `sheetOffset = V_q − U_q`, `sheetConstant = (T_q − d_q − n_q)/2`.
- PROVED `tipEast_mem`: `(2,1) + V_p` is in the closed polygon (odd branch).
- PROVED `tipEast_standard`: `standardField word ((2,1) + V_p) = harmonicGrid ((2,1) + V_p)`, via `standardField_eq_sheetMin_of_strong`; the first sheet uses the parent zero band at `(2,1) − U_q` (`zeroStrip_of_strong`, with `parentTGrade = 2n_p − d_p + 1`), the second the odd parent harmonic band at `(2,1) − V_q` (`W1Hstrong.hStrong_of_strong`, with `parentSGrade = 3d_p + n_p − 2`), and `np ≤ dp − 1` from the child's properness.
- PROVED `W0_middle_white`: `laplacian (standardField word) (V_p + (1,1)) = 0`, from the harmonic strip (for the middle and its west input, `s = −2 + 2d` and `s = −2 + c`) and `tipEast_standard` (the east input). This closes the W0 middle of TIP_THEOREM.
- Hypotheses: `h`, `StrongEstimates (conjWord word)`, `SeedFields (conjWord word)`, `(frameAt word).Packet (standardField word)`, `eps = −1`, and the nonbase bounds `0 ≤ tipB`, `5L ≤ T − tipB`.
- Checks: `checks/W0Sheets.lean`. Root build clean; sandbox logs clean.
- Also fixed: `FLatticePaper.lean` was missing the `TipEscape` import; added with `W0Sheets`.

### Task 72 (queue Q16, the one-input tie): TieOneInput.lean

- PROVED `FLatticePaper.other_input_of_tie`: at a black minimum `M = min(A, C)` with `M c = A c`, `M i = A i` and `A` white at `c`, the other input `j` has `C j = A j − 1` (`Ψ j = −1`). This is the algebraic identity `ΔA − ΔM = 1` on the star; no policy is used.
- NOT PROVED: `hResP` and `hResN` (the leaves of `TieReduce.tie_excluded_of_narrow`). Still needed: the A-policy retention at the tied centre (from the `Ψ j = −1` input and `sheetDiff_mono_A`), the rising-pair slip increment and the old-root cases (`nonfree_drop_excluded`, Q3's H-star and V-star estimates), and the exceptional endpoint (Q19).
- Checks: `checks/TieOneInput.lean`. Sandbox logs clean.

### Task 72 (queue Q16, hResP, the tied centre): TieCentre.lean

- PROVED `tie_sheetA_white`: at a black centre `c` of `M = standardField word` in `E` with `Ψ c = 0` and an input `j` with `Ψ j = −1`, the sheet `A` is white at `c` (`laplacian A c = 0`) and `A i ≤ C i` for the other input `i`. This is `ΔA − ΔM = Σ (A − M)`, `(A − M) j = 1`, `ΔA ∈ {−1, 0}` (the binary Laplacian of the conjugate's quarter-turn field); no policy is used.
- PROVED `sheetPolicyA_of_tie`: the A-policy retains `c → i`. The quota at the white conjugate root retains one input, and `j` is not retained, since `sheetDiff_mono_A` would give `Ψ c ≤ Ψ j = −1`.
- PROVED `retained_of_quota` (the quota pick).
- NOT PROVED (still needed for `hResP`): the old-root argument. The retained edge must be `nonfree_drop_excluded`'s `parentPolicy` edge with `jumpA (c − lv) = 1` and `jumpA (i − lv) = 0`, which comes from the rising-pair slip structure (positive `σ`), and then either `nonfree_root_forced_nonfree` (nonfree old root) or the free-root exclusions (`H_drop_excluded`, the V-block) with the exceptional endpoint (Q19).
- Checks: `checks/TieCentre.lean`. Root build clean; sandbox logs clean.

### Task 72 (hResP, step 1, the positive-chart identity): SheetDownJump.lean

- PROVED `sheetA_sub_uq_eq_cutPrice`: `A (z − uq) − A z = cutPrice − price G (Z (z − l_v))` for the sheet `A = sheetA Fp`, from the paragraph-5 identity `paragraph5_field_identity_of_strong` at `z − l_v`, with `uq = εU_q`.
- NOT PROVED: the value of the jump at the rising pair. The positive chart needs which sheet wins at `c − uq` (Q3's "at a tie choose a target winner"), which fixes `A (c − uq) − A c ∈ {0, −1}` and so the jump; that argument is not yet formal.
- Checks: `checks/SheetDownJump.lean`. Root build clean; sandbox logs clean.

### Task 72 (hResP, the case reduction): HResP.lean

- PROVED `hResP_of_negTie`: the tied rising pair (`Ψ c = 0`, an input `j` with `Ψ j ≤ −1`, rising `σ` pair `(c, i)`, both endpoints with `− uq` in `E`) is excluded, reduced to the negative tied-target exclusion `hNegTie`. The cases: `i ≠ j, Ψ i ≥ 1` (positive chart, `sheetPolicyA_of_tie` retention, `adjacentChart_witness`, `adjacent_chart_excluded`); `Ψ i = 0` or the other input `Ψ = 0` (`plus_adjacent_nonpos_excluded`, the whole star `≤ 0`); `i = j`, `Ψ k ≥ 1` (reflect to `−σ`: the tied centre `I c`, the strict target `I i` (`Ψ = 1`), the input `I k` with `Ψ ≤ −1`), which is `hNegTie`.
- NOT PROVED: `hNegTie` (the negative tied-target exclusion). Its proof is `neg_adjacent_excluded` with `sheetPolicyA_of_tie` for the retention and the old-root analysis in place of `blackRoot_of_black` (the root is white): `nonfree_root_forced_nonfree` for a nonfree old root, and `H_drop_excluded` / the V-block with the Q19 exceptional endpoint for a free old root.
- Also generalized `TieCentre`: `tie_sheetA_white` and `sheetPolicyA_of_tie` accept `Ψ j ≤ −1`.
- Checks: `checks/HResP.lean`. Root build clean; sandbox logs clean.

### Task 72 (hNegTie, case (a): nonfree old root): NegTieNonfree.lean

- PROVED `negTie_drop_of_nonfree`: in the negative tied-target configuration (rising `−σ` pair `(c, i)`, tied centre, strict target `Ψ i ≥ 1`, an input `j` with `Ψ j ≤ −1`, both endpoints shifted by `+uq` in `E`) with the old root `zTurn (c − l_v)` nonfree in the conjugate frame, the configuration is excluded. The retention is `sheetPolicyA_of_tie`; the jumps `a(c − l_v) = 1`, `a(i − l_v) = 0` are the negative-chart arithmetic of `neg_adjacent_excluded`; the root condition is `nonfree_root_forced_nonfree` (black or the forced retained edge), closed by `nonfree_drop_excluded`.
- The hypothesis `hW1` (the conjugate's `W1Forced`) is the input of the covers, not derived here.
- NOT PROVED (case (b)): a free old root in the conjugate frame. Missing: (i) the strict-interior ⟹ nonfree count (FIXED_FREE §7), (ii) the H-web of the translate of the old root by `−V` or `−K` (`hweb_of_freeH` is stated for free H sites of the physical frame, and the correspondence with the conjugate's free sets via `zTurn` is not in Lean), (iii) the V-block for the translate and the exceptional endpoint of Q19 (`exceptional_drop_excluded` with `exceptional_hT_proved` is proved, but the old root must be the exceptional vertex).
- Checks: `checks/NegTieNonfree.lean`. Root build clean; sandbox logs clean.

### Task 72 (case (b), link 1: strict interior is nonfree): StrictNonfree.lean

- PROVED `FLatticePaper.Induction.strictInterior_nonfree`: a site of `StrictInterior` (parity-resolved `b − T < t < a`, `h < s < T + c`) is nonfree. The H trace: the windows of `avoid_H_even_low` / `avoid_H_odd_low` exclude every translate `t − jT`. The V trace: a free V translate `s + iT` lies in the parity range of `E` and in `vSpectrum`; odd strict interior points and even ones with `s > L − 2` are excluded for every `i`; even ones with `s ≤ L − 2` are the exceptional case: `i = 0`, `j = 0` (other `j` leave `E`), and the left neighbour lies in `E`.
- Checks: `checks/StrictNonfree.lean`. Root build clean; sandbox logs clean.
- Not in this step: links 2 and 3 of case (b).

### Task 72 (case (b), link 2: conjugate coordinates at the old root): ConjFreeRoot.lean

- PROVED `conj_tGrade_zTurn`: `t_c(zTurn x) = (d_p + n_p) − s_p(x)`; `conj_sGrade_zTurn`: `s_c(zTurn x) = 2 (t_p(x) − n_p)`; `conj_periodDenominator`: `T_c = 2 T_p` (`oddParentPeriod`). Conjugate child is `rotate(odd)`, so `conj_child_num_den` applies.
- PROVED `conj_freeV_hweb`: a free conjugate V site `zTurn x + combine i j` gives `HRootWeb (n_p) (d_p) (t_p x + i T_p)`.
- PROVED `parentTGrade_translate_V`: `t_p(x − iV_p) = t_p x + i T_p`.
- PROVED `jumpA_zero_of_strip`: `1 − d_p ≤ t_p x ∧ t_p x + 1 ≤ n_p + 2 d_p − 1` gives `jumpA x = 0`.
- PROVED `H_translate_drop_excluded`: with `jumpA x = 1`, `jumpA y = 0`, `HRootWeb (t_p x + i T_p)` and the neighbour zero strip `hsy` at `t_p y + i T_p`, we get `False` (the translation by `−iV_p` shifts `a` by `−i` at both points, so `a(x) = a(y) = i`).
- OPEN INPUT `hsy`: the neighbour zero strip is not automatic from HRootWeb arithmetic (brute force, scratchpad/neighbour_strip.py): it fails for a `+D` step from a regular value (top `N+D−1`), a `+D` or `+N` step from `N+D`, and a `−D` step from `0`.
- Checks: `checks/ConjFreeRoot.lean` (guards). Root build clean; sandbox logs clean.
- Not in this step: the freeH case of the conjugate free site (V-block, link 3).

### Task 72 (case (b), the even window hWin and the even neighbour zero): EvenWindow.lean

- PROVED `harmonicGrid_zTurn`: `h(Zx) = −h(x)` for all `x`.
- PROVED `odd_band_conj`: for the conjugate word, `F = h` on odd sites with conjugate `s` in `[2 − 3d_c + n_c, 3d_c + n_c − 2]`, from `lower_odd_h0` (odd seed `SeedFields.odd_bottom`, price range, drifts), `HasStrips.2` on `[1 − 2d_c, 2(d_c + n_c) − 1]`, and `odd_h0_upper`.
- PROVED `even_window_zero_of_strong` (= hWin): for even `x` with `1 − r ≤ t_p x ≤ 2r − 1`, `quarterTurnField G x = 0`. Here `Zx` is odd with `s_c(Zx) = 2(t_p x − N)` in the odd band (conj child `(D−N, D+N)`), so `G(Zx) = h(Zx) = −h(x)`.
- PROVED `evenSite_add_eps_uq_iff`: `x + εU_q` has the same site parity as `x` (`Fraction.Even` gives `num + den` even), so the partner is also even.
- PROVED `jumpA_zero_of_even_window`: even `x` with `t_p x` and `t_p x + 1` both in the extended window gives `jumpA x = 0`.
- CORRECTION recorded: the earlier parity-flip assumption was wrong, `εU_q` preserves parity.
- Neighbour zero (hsy) by parity, brute force over N, D (scratchpad/neighbour_samepar.py): even neighbour needs extended at `T`, `T+1` (`jumpA_zero_of_even_window`); odd neighbour needs ordinary at `T`, `T+1` (`jumpA_zero_of_strip`). The only residual classes are the exceptional H roots: `u = N+D` with an even root and `+N` step when `D = N+1`, and `u = D+1` with an odd root and `+D` step when `N = 1`.
- Checks: `checks/EvenWindow.lean` (guards). Root build clean; sandbox logs clean.
- Not in this step: the exceptional residual (link 3), and the Lean assembly of hsy from these parity cases.

### Task 72 (case (b), the regular H drop and the neighbour zero): NeighbourDrop.lean

- PROVED `evenSite_add_vec_iff`: the vertical translate `−iV_p` preserves site parity (coordinate sum changes by `−2in`).
- PROVED `odd_neighbour_strip`: for `u ≠ N+D` and step `±N` (odd neighbour), the neighbour and its partner lie in the ordinary zero strip.
- PROVED `even_neighbour_window`: for `u ≠ N+D` and step `±D` (even neighbour), the neighbour and its partner lie in the extended window.
- PROVED `H_drop_regular`: with the H-web at the root, `jump x = 1`, `jump y = 0`, the neighbour step by parity, and `u ≠ N+D`, the configuration is impossible (root zero gives `1 − i = 0`, neighbour zero gives `−i = 0`).
- Residual: `u = N+D` (exceptional H root), where the regular bands fail only for an even root with `+N` step at `D = N+1` and an odd root with `+D` step at `N = 1`. This is link 3.
- Checks: `checks/NeighbourDrop.lean` (guards). Root build clean; sandbox logs clean.

### Task 72 (link 3 residual, numerical check): scripts/rising_pair_check.py

- Question: does a rising tied configuration (RisingBlackPair with shift −σ, tie at the centre) ever have its old root at `t_p = N+D` or `D+1`?
- Answer (words over {1,2,3} of length ≤ 4, 112 words, both shift signs): the slip increment `(F i − F(i+σ)) − (F c − F(c+σ))` over all black centres `c` (lap = −1, `(F c − F(c+σ))` odd, `lap F (c+σ) = −1`) and their inputs `i` is `0` in every one of the 32930 (+σ) and 31766 (−σ) cases. No rising black pair exists, so the residual `u = N+D` never occurs on these fields.
- Consequence: the residual is excluded by the rising-pair statement itself (`NoBlackPairRise`, `OddRise.lean`: slip increment `≠ 1` at black pairs). A Lean proof of the residual needs that exclusion as a local fact; not yet derived from `W1_CONSTRUCTOR` §4.
- Not committed Lean: no change to the Lean sources in this step.

### Task 72 (case (b), H drop along an edge with the sharp conjugate band): ConjFreeRoot.lean (`conj_freeV_band`), EdgeDrop.lean

- PROVED `conj_freeV_band` (ConjFreeRoot): a free conjugate V site `zTurn x + combine i j` forces `1 ≤ t_p x + i T_p ≤ N + D − 1`. The conjugate V spectrum in `u = t_p x + i T_p` is `s = 2(u − N)` with `2 − 2N ≤ s ≤ 2D − 2` (or `N ≤ u ≤ D`, contained in the same band). Strictly sharper than `HRootWeb`, which also allowed `0`, `N + D`, `D + 1`.
- Correction to the lead's parity labels: `s_c = 2(t_p − N)` is always even, so the V spectrum has no odd branch; the band is the single disjunct.
- PROVED `edge_step_parent`: an edge from `c` changes `t_p` by `±N` from an even centre and `±D` from an odd centre.
- PROVED `edge_parity_flip`, `evenSite_sub_even_iff`.
- PROVED `H_drop_edge`: with the edge `i` of `c`, `jump(c − sheetShift) = 1`, `jump(i − sheetShift) = 0`, and the sharp band at the root, the configuration is impossible. The residual `u = N + D` is outside the band, so `H_drop_regular` applies without `hu`.
- Consequence: the H-drop branch of hNegTie case (b) is closed by arithmetic, with no residual and no numerics.
- Checks: `checks/EdgeDrop.lean`, `checks/ConjFreeRoot.lean` (guards). Root build clean; sandbox logs clean.
- Next: the V block (conjugate freeH branch), with Q19.

### Task 72 (case (b), conjugate freeH branch, arithmetic): ConjFreeRoot.lean (`conj_freeH_band`)

- PROVED `conj_freeH_band`: a free conjugate H site `zTurn x + combine i j` forces the translated parent s-grade `σ = s_p x + j·2T_p` into one of two bands: `σ` odd in `[N−D+2, N+D−2]` (the conjugate's even-t branch), or `σ` even in `[0, 2N]` (the odd-t branch). Uses `L = D+N` odd.
- Reading: the even-root part `[0, 2N]` is the earlier (parent-child) frame's V spectrum restricted to its lower band; the odd-root part is the odd H band, which the frame's free V (even sites only) does not contain. The V block (BlockPairAt, Q19 west edge) still needs the identification of the earlier frame's free V with the conjugate free H, which is not yet proved.
- Checks: `checks/ConjFreeRoot.lean`. Root build clean; sandbox logs clean.

### Task 72 (V-block converse, numerics): scripts/conj_freeH_vpath_check.py

- (a) General children: every even free H point of an odd coprime child `(n, d)`, `d ≤ 25`, satisfies `z = (2l − b, b)` with `b = ⌊2nl/L⌋`, `L = n + d` (815 points).
- (b) Words ≤ 4 (112 words, 1652 conjugate free H points): the forward transport `x = zTurn(w) = (−w2, w1 − 1)` takes the 1058 even free H points onto the parent V vertices `(−b', 2l − 1 − b')`, `b' = ⌊(D − N) l / D⌋`, with `1 ≤ l ≤ D − 1`, all in the word frame's free V. The lead's `zTurnInv` direction is the wrong one.
- (c) The 594 odd free H points map to even parent sites; 536 land in the word frame's free V, and the other 58 are exactly `V_p + I = (N−D+1, N+D−1)` (the exceptional endpoint of Q19, not free for ε = +1).
- Consequence for the lead's step (2): the parent block vertex is `zTurn` of the even conjugate free H point, with `l < D`, so `parent_block_mem_freeV` applies.
- Lean is not yet written for (a) or (b); the next step is the floor description of the even free H points of a general ChildFrame.

### Task 72 (V-block converse, steps 1-3): VPathFloor.lean

- PROVED `even_spectrum_floor` (step 1): an even site with `t` in the even H spectrum is `z₂ = ⌊2 n l / (d+n)⌋` for `l = (z₁+z₂)/2`. The identity is `2 n l = t + (d+n) z₂` with `0 ≤ t < d+n`.
- PROVED `range_l`: with `r = (D−N) l − D b ∈ [1, D−1]` and `0 ≤ 2Dl − (D−N) b ≤ T_p + (D−N)`, `1 ≤ l ≤ D−1` (case analysis at `l ≤ 0`, `l = D`, `l ≥ D+1`).
- PROVED `conj_freeH_even_block` (step 2): an even conjugate free H point `w` has `zTurn w = (−b', 2l−1−b')`, `b' = ⌊(D−N) l / D⌋`, `1 ≤ l ≤ D−1`. Uses the spectrum bounds on `t`, the polygon bounds on `s`, `conj_periodDenominator` and `conj_child_num_den`.
- PROVED `conj_freeH_even_freeV` (step 3): `zTurn w` lies in the word frame's free V set (`parent_block_mem_freeV`, `l < D`).
- Numerics (scripts/conj_freeH_vpath_check.py, words ≤ 4) agree with these statements.
- Checks: `checks/VPathFloor.lean` (guards). Root build clean; sandbox logs clean.
- Not yet: the odd conjugate free H points and `V_p + I` (the Q19 west edge).

### Task 72 (V-block converse, odd points, numerics): scripts/conj_freeH_odd_check.py

- Odd conjugate free H points, written as `w = (2l − b + 1, b)` with `l = (w1 + w2 − 1)/2`, `b = w2`: the spectrum `t_c(w) = 2r + (D − N)` with `r = (D − N) l − D b` gives `0 ≤ r ≤ N` (exactly), and `b = ⌊(D − N) l / D⌋`, `0 ≤ l ≤ D − 1`. The image is `zTurn w = (−b, 2l − b)`.
- Each `l ∈ [0, D − 1]` with `0 ≤ r_l ≤ N` is hit by exactly one odd conjugate free H point; `r_l = N` holds exactly for `l = D − 1`, where the image is `excVertex = V_p + I`.
- For `r_l ≤ N − 1` the image is in the word frame's freeV (482 cases, words ≤ 4; the origin for `l = 0`); the word index `q = (d − n) l − d b` satisfies `q ≤ n` there (370 cases).
- `excVertex` is free exactly when ε = −1 (54 of 112 `r = N` cases in words ≤ 4; the other 58 have ε = +1). Words ≤ 5 agree (3208 odd points, no failures).
- Lean is not yet written for this; the algebra needed is the identity `D q = ε l + d r` (ε = N d − D n), giving `q ≤ n` from `r ≤ N − 1`.

### Task 72 (V-block converse, odd points): OddFreeH.lean

- PROVED `odd_block_arith`: with `r = (D − N) l − D b ∈ [0, N]` and the polygon band `1 − N ≤ σ + D ≤ T_p + D − 1` (`σ = 2Dl − (D − N) b`), `0 ≤ l ≤ D − 1` (from `D σ = T_p l + (D − N) r`).
- PROVED `odd_freeH_image`: for an odd free H point `w` of the conjugate child, `zTurn w ∈ freeV` (word frame) or `zTurn w = excVertex` (`V_p + I`). The first case splits: `r = N` gives `l = D − 1`, `b = D − 1 − N` (via `ε(l+1) = D(d(l−b) − n(l+1))` and `ε = ±1`); `r ≤ N − 1` gives the block vertex `(−b, 2l − b)` (`even_block_mem_freeV`, with `q ≤ n` from `D q = ε l + d r`), and `l = 0` gives the origin (`origin_mem_freeV`).
- PROVED `origin_mem_freeV`, `even_block_mem_freeV` (the child-frame block vertex `(−b, 2l − b)` with `q ≤ n`).
- Checks: `checks/OddFreeH.lean`. Root build clean; sandbox logs clean (rc=1 on the warning/error/sorry greps).
- Remaining for the V block: the excVertex case goes to the exceptional leaf (`exceptional_drop_excluded` with `exceptional_hT_proved`), and the −σ mirror of `BlockPairAt`.

### Task 72 (hNegTie case (b), −σ V-block mirror): NegBlock.lean

- PROVED `laplacian_negShift_eq_of_eps_one`, `laplacian_negShift_eq_of_eps_neg_one`: for the slip `−σ` the black translate `c + (−σ)` equals `(c + U_q) − U_c` (ε = +1) or `(c − U_q) + U_c` (ε = −1), so the child kernel gives `lap(c − σ) = lap(c + U_q)` resp. `lap(c − U_q)`.
- DEFINED `BlockPairNeg`: the mirror of `BlockPairAt` with base `c` (ε = +1) or `c − U_q` (ε = −1).
- PROVED `not_rising_of_blockPairNeg`: a `BlockPairNeg` centre is not a black pair with black translate `c + (−σ)` (via `black_centres_contradiction`).
- Open: the identification of the free root of a −σ tie with `BlockPairNeg c`. For ε = +1 the sheet shift vanishes (`phaseW = 1`), so the root is `c`, and the conjugate free H image of `zTurn c + v` is `I − c + R v` (`I = (1, −1)`), a point reflection of `c` and not a translate. The base of the −σ V block therefore needs the reflected point; this is queried with the lead.
- Checks: `checks/NegBlock.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, collar squares): CollarSquares.lean

- PROVED the parent-root memberships `bottom_root_mem`, `vPlus_root_mem`, `vMinus_root_mem` and the child-base identities `bottom_child_base`, `vPlus_child_base`, `vMinus_child_base`, plus the centre memberships `bottom_centre_mem`, `vPlus_centre_mem`, `vMinus_centre_mem`. These fix the three collar squares of the root `r = zTurn (c − l_v)`: bottom (upper-left of `c`, child `squareCorners (c.1 − 1) c.2`), aligned V with `ε = +1` (upper-right, `squareCorners c.1 c.2`), aligned V with `ε = −1` (lower-left, `squareCorners (c.1 − 1) (c.2 − 1)`).
- Numerics (`words ≤ 4`, scratchpad `arc_rule.py`, `nonaligned.py`): for every free collar centre the arc rule gives strict corners, including the non-aligned V side at the pricing point `c − W·U`. The exceptions are the bottom centres `(1,1)` with `ε = −1`; those are black and excluded by the laplacian-0 hypothesis, which is not yet proven from the strips.
- Open (not in this file): the strictness of these squares needs the free-root band for even bottom centres (`s > 2L − 2`, numerically except at `(1,1)`) and its left/right analogues; the parent chains are the named core claims of `W1Phase`; the nonfree roots use `parentSquare_nonfree`.
- Checks: `checks/CollarSquares.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, the black corner (1,1)): CollarOneOne.lean

- PROVED `laplacian_MW_one_one`: for every word with a proper letter, `laplacian (MW word) (1, 1) = −1`. The inputs of `(1,1)` are `(0,1)` and `(2,1)`, both odd; `(0,1)` has `s = d − n` in the harmonic strip (`F(0,1) = h₀(0,1) = −1`), and `(1,1)`, `(2,1)` have `t` in the zero strip (`F = 0`). The three sites lie in the closed polygon (`one_one_neighbourhood_mem`), where `MW` agrees with the standard field.
- Correction to the lead's note: `(2,1)` is odd (the inputs of an even site are odd); the argument uses only the zero strip there, so it is unaffected.
- The corner is black for every word, not only at `ε = −1`; the bottom collar excludes it by the laplacian-0 hypothesis in all cases.
- Checks: `checks/CollarOneOne.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, the glue to HsqAt): CollarGlue.lean

- DEFINED the arc predicates `BottomArc`, `LeftArc`, `RightArc` (the collar's H arc, left V arc and right V arc) and the base `collarBase`: bottom → `squareCorners (c.1 − 1) c.2`; otherwise left → `squareCorners c.1 c.2`; otherwise right → `squareCorners (c.1 − 1) (c.2 − 1)`. The arc rule has no sign dependence and matches the numerics (the left and right arcs never overlap without the bottom arc).
- PROVED `centre_mem_collarSquare`: the centre lies in its collar square.
- DEFINED the inherited structure `CollarChains` (fields `out`, `corners`, `phase`): the rejected pointer is outside the square; the other corners are black or forced white with the output in the square; the phase chains reach the centre. These are the parent's collar return chains, to be supplied as data like `OldPolicyWitness`.
- PROVED `hcollar_of_chains`: from `CollarChains` and the strictness of the collar square (`hstrict`, named), `HsqAt word P c` holds at every strict collar centre with laplacian 0.
- Checks: `checks/CollarGlue.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, (a) lemma 1): CollarBand.lean

- PROVED `exists_translate_of_not_nonfree`: a root that is not nonfree has a child-deck translate `z + (i U + j V)` in `freeH ∪ freeV`, with `U = (d, n)` and `V = (n − d, n + d)` (the child kernel and transverse).
- This is the first of the four lemmas for the band (a). The others are the parent identity `c − l_v = I − v + i V_p − j U_p` (with `v = zTurn w`), the sign of the translate index, and the bounds on `s(v)` from the V spectrum and `excVertex`.
- Checks: `checks/CollarBand.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, (a) lemma 2): CollarIdentity.lean

- PROVED `zTurn_zTurn_add`: `zTurn (zTurn x + p) = (1,−1) − x + (−p.2, p.1)` (the half-turn of a conjugate translate).
- PROVED `sW_centre_identity`: for the conjugate translate `p = i U_c + j V_c`, `s(c) = 2n + s(l_v) + 2 i (Nd − Dn) − j s(U_p) − s(v)` with `v = zTurn (zTurn (c − l_v) + p)` and `s` the word `s`-grade.
- Checks: `checks/CollarIdentity.lean`. Root build clean; sandbox logs clean.
- Open: the sign of `j` and the value `i = 1` (they come from the H spectrum of the translate, i.e. from the parent grades `s_p(c − l_v)`), and the bounds on `s(v)` (from `vSpectrum`, `s(v) ∈ [2 − d + n, L − 2]`).

### Task 72 (hcollar, band (a), H-point bounds): CollarBottomBand.lean

- PROVED `even_H_bounds`: an even H point `v` of the closed polygon has `l = (v.1 + v.2)/2 ≥ 1`, `v.2 ≤ l − 1` (the floor law) and `s(v) ≥ 2 d l + 2 n`.
- PROVED `odd_H_bounds`: an odd H point `v` of the closed polygon is `(1, 0)` or has `s(v) ≥ 3 L`.
- Numerics correction: the earlier band numerics used a box with `|y| ≤ 2n + 2`, too small; the strict region reaches `y ≈ L`. With the corrected box, the top (V-translate) collar fails the bottom square for odd centres. The top collar uses the square LR, and the centre reflection `z ↦ R − z` (`R = (n+1, 2n+d−1)`) maps strict top centres to strict bottom centres (grade identities, parity preserved), and maps the top witness `w + V` to the bottom witness `U + I − w`, which is a free H point (checked numerically; grade proof: `t ↦ L − t`, `s ↦ T + 2n − s`).
- Checks: `checks/CollarBottomBand.lean`. Root build clean; sandbox logs clean.

### Task 72 (hcollar, arc correction): CollarGlue.lean, CollarSquares.lean

- Corrected the arc rule. `BottomArc` is now the direct free-H witness only; the V-translate witness is `TopArc` with the lower-right square `squareCorners c.1 (c.2 − 1)` (`top_centre_mem`). The earlier merged definition put the top arc into the bottom square, which fails for odd top centres (numerics with the corrected box: 33 failures at word length 3).
- Numerics with the corrected box (words ≤ 3): pure classes B → upper-left, T → lower-right, L → upper-right, R → lower-left, with every strict corner strict. The mixed classes BL, BR, TL, TR (33 each) are the four black corners and are excluded by laplacian 0.
- Checks: `checks/CollarGlue.lean` (unchanged). Root build clean; sandbox logs clean.
