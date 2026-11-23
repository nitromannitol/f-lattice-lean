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
| `hlat` (lattice bridge) | Q3Bridge.lean:22 | — | **obsolete**: `lattice_bridge_exists` (Q3Hlat.lean:36) proves it; the proved version is `paragraph5_field_identity_proved` (Q3Bound.lean:17), which has no `hlat`. Recommend deleting `paragraph5_field_identity` (Q3Bridge.lean:18–…). |
| `hweb : HRootWeb N D (parentTGrade x)` | Q3Paragraph8.lean:72 | (iv) | **open**: the regular floor step of the H web (even `[1, N+D−1]`, odd `[N,D]`); the exceptional values are proved in ParentWeb.lean. This is the only open named hypothesis of paragraph 8 (H part). |
| `hRectInputs` | Q3Exit.lean:44–45 | (iv) | **open**: points of the open parity rectangle have both inputs in the closed polygon (checked numerically, q3_rect_check.py). |
| `hBoundary` | Q3Exit.lean:46 | (iv) | **open**: points of the closed polygon outside the open rectangle lie on a boundary spectrum mod T (checked numerically). |
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
- **Paragraph 8, V star:** `a ∈ {0,1}` and the `j = 0` translate are not formalized: they use the monotone V path and the translate index of `d_f`, which are not in the codebase's interface. Numerically `a ∈ {0,1}` holds on the child's native V sites (5700/5700, q3_child_native.py).
- **Paragraph 2 (inputs of a black centre in E):** the exit lemma `exit_centre_on_boundary_spectrum` (Q3Exit.lean:43) reduces the claim to the two named hypotheses (iv). The strip facts of paragraph 2 are field data (i), not used in Lean.

## Summary of open items

1. `hweb` (Q3Paragraph8.lean:72), category (iv): the H-web floor step.
2. `hRectInputs`, `hBoundary` (Q3Exit.lean:44–46), category (iv): W1's rectangle theorem (task 45).
3. The rectangle and boundary readings `openRect`, `onBoundarySpectrum` (Q3Exit.lean:25, 36), category (iii)/(iv): PROVISIONAL.
4. `hexit` (Q3Window.lean:23, 31, 39, 47), category (iii): the exit reading.
5. `chart_separation` (Q3Inputs.lean:14): needs the parity tightening (`L + 2`), category (iii).
6. `hlat` (Q3Bridge.lean:22): obsolete; delete with `paragraph5_field_identity`.

All (i)-category hypotheses are supplied by `StrongEstimates (conjWord word)` through the `_of_strong` wrappers (Q3Strong, Q3Field, Q3Paragraph8).
