# w3: plan for the aux rank (`hstrictR`)

Status: plan only. The aux rank is the one named premise `hstrictR` of `FreeAssemble.free_named_inputs`; nothing in this file is proved.

## 1. Target

For a sign `η ∈ {±1}` and the word `w` with field `F = standardField w`, a function `R : Site → ℤ` with

    (A) ∀ c i, auxS F η c i → R i < R c          (current form, `AuxRankSign.auxS`)

or, if `squares_gen` is restated (see §4), the selected-edge form

    (A') blacks: ∀ c i, lap c = -1 ∧ Edge i c → R i < R c;
         whites: ∀ c, lap c = 0 → ∃ i, Edge i c ∧ permits c i ∧ R i < R c.

Consumers: `AuxRankSign.hasSat_of_aux` (HasSatSelection via `ComparisonEmpty.hasSat_of_strict`), `AuxRankSign.forced_aux` / `forced_permitted_S` (through `AuxRank.squares_gen`), `AuxRankSign.freePolicy_aux`, `FreeAssemble.free_named_inputs` (`strictRank`).

## 2. A discrepancy to settle first

`AuxRankSign.auxS` keeps `slipPermits` at nonfree whites. Q1 (`flattice-astra/fixes/Q1.md`, "First form the auxiliary game for sign η") defines the auxiliary game differently:

- black sites: both inputs;
- free whites (`freeClosure c`): the prescribed input `FreePresc η c i`;
- every other white: **both** inputs allowed;

and only afterwards "the selected edges are permitted in the raw-slip game", by the slip calculation on the identified canonical graph.

Consequences. The Q1 game `permitsQ1 η c i := (lap c = -1 ∧ Edge i c) ∨ (lap c = 0 ∧ ((freeClosure c ∧ FreePresc η c i) ∨ (¬freeClosure c ∧ Edge i c)))` has fewer restrictions than `auxS`, so the Bellman rank for `permitsQ1` is the natural object. The slip permit of the selected input must then be proved (Q1, last paragraph), not built into the graph. Current `auxS` therefore asks for a strict rank on a graph where the slip permit is already a constraint. That is a stronger statement, and I cannot see it following from the Bellman construction without the selected-edge slip lemma. Recommendation: state the aux rank for `permitsQ1`, and prove the slip permit of the selected input separately (the `permitted` field of `FreeNamedInputs`).

## 3. Bellman route (archive note `weighted_rank_audit/WEIGHTED_FORT_AND_BELLMAN_RANK.md`)

The note proves, for a grade `K = A·P + C·J` with positive integers `A, C`:

1. no nonempty fort lies in `{K ≥ h}` (minimal-vertex argument, deck translation of the whole fort, finite same-pair elimination);
2. uniform exit depth `H` from pruning (`IsIncomingFort` / `RestrictedNoFort`);
3. bounded total reward `elapsed + H·K ≤ H·K(start) + H + H²·D`;
4. the obstacle Bellman iteration `R_{j+1} = max(H·K, 1 + 𝒯R_j)` stabilises, giving an integer strict rank with slope `H·K`.

Lean objects and the step each supplies:

| step | Lean lemma (file) | status |
|---|---|---|
| 1, no-fort in a half-space | `RankFromForts.RestrictedNoFort` (definition), `RankFromForts.noIncomingFort_of_restricted` | the **no-fort content itself is missing** (see §5) |
| 2, uniform exit depth | `BellmanRank.exists_escapeDepth_of_no_incomingFort`, `RestrictedBellmanRank.exists_restrictedEscapeDepth`, `exists_uniform_escapeDepth`, `exists_uniformRestrictedEscapeDepth` | present |
| 3, bounded correction | `BellmanRank.bellmanValue_le_of_uniform_escape`, `RestrictedBellmanRank.restrictedValue_le_of_uniform_escape`, `WeightChange.bellmanRank_lt`, `retWalk_length_le`, `retWalk_mono`, `exists_rank_increments` | present |
| 4, strict integer rank | `BellmanRank.exists_burningRank_of_no_incomingFort`, `RestrictedBellmanRank.exists_constrainedBurningRank_of_restrictedNoFort` (output `IsConstrainedBurningRank`, `AlternateMidpoint.lean:8`) | present, conditional on 1 |
| S3 wrapper | `RestrictedBellmanRank.S3_of_restrictedNoFort`, `S3_of_packet_restrictedNoFort` (permits = `slipPermits`, grade = `cutGrade 1 1 1`) | present, for `slipPermits` only |

The hypotheses of `exists_constrainedBurningRank_of_restrictedNoFort` for `permitsQ1` and the grade `K`:

- `hcover : deck.Covers sites`, `heven` (span even), `hcharge` (Laplacian `Λ`-invariant): from the packet (`ChildFrame.laplacian_add_lattice`);
- `hgrade : ∀ step ∈ span, ∃ increment, ∀ site, grade (site + step) = grade site + increment`: for `K = P + J` the drifts of `P` on `U, V` are in `StrongEstimates` (`StrongEstimates.lean`, the drift field); the drift of `J = roundedSlip` needs checking;
- `hperm : ∀ step ∈ span, ∀ site input, permits (site+step) (input+step) ↔ permits site input`: for `permitsQ1` this is `freeClosure` invariance (`freeClosure_add_span`) plus `freePresc_add_span` (`FreePolicy.lean:281`) plus `Edge` even translation (`incomingNeg_add_even`, `TwosEquiv.lean`); all available;
- `hlocal : PermitLocal field permits` (`RankFromForts.lean:44`): blacks both, whites one. For `permitsQ1` the white clause is `freePrescribed`/`Edge`, available;
- `hbinary`: `packet.binary`.

Only `hno : RestrictedNoFort field grade permits` is missing.

## 4. squares_gen

`AuxRank.squares_gen` takes `hstrict : ∀ c i, P c i → R i < R c`. The Bellman rank gives strictness on the selected input at whites and on both inputs at blacks. The square argument uses the minimum-rank corner's selected input, so `squares_gen` can be restated with `hstrict` only at blacks (both inputs) and at whites for the selected input `sel c`. This changes `AuxRankSign.forced_aux` and `freePolicy_aux` accordingly: the forced output `sel c` of a nonfree white is the selected input, so its decrease is what is needed.

## 5. What is missing

(a) The no-fort content `RestrictedNoFort field K permitsQ1`: no fort in a half-space `{K ≥ h}` for the Q1 game. This is Q1's ordered removals, fan exclusion and E-core argument, with the free-site list `V_r, …, V_{r+1−L}` and `H_0, …, H_{d−1}−U`. The Lean repo has the canonical no-fort inputs `S3NoFortInputs` (`S3Canonical.lean`, fields `free`, `bulkOrder`, `freeOrder`, `firstLevel`, `secondLevel`, `bulkBlack`) and derives them from the canonical games (`S3NoFortInputs_of_canonical`, `S3Canonical.lean:364`). Whether those inputs give `RestrictedNoFort` for `permitsQ1` (rather than for `slipPermits`) is the first thing to check. If not, the Q1 ordered-removal lemmas must be formalised.

(b) The selected-edge slip permit of §2 (Q1, last paragraph: "the selected edges are therefore permitted in the raw-slip game").

(c) The restatement of `squares_gen` in §4.

(d) Drift of `J = roundedSlip` along the span (for `hgrade`), if not already in the strong estimates.

## 6. Order of work

1. Check whether `S3NoFortInputs_of_canonical` yields `RestrictedNoFort` for `permitsQ1` (or for the canonical policy's permits). This decides whether (a) is a Lean lemma or a new block.
2. Define `permitsQ1` and prove `PermitLocal`, `hperm` (the invariance above) in a new module `AuxRankQ1.lean`, leaving `RestrictedNoFort` as the single named premise.
3. Apply `exists_constrainedBurningRank_of_restrictedNoFort` to get `IsConstrainedBurningRank`, and derive the selected-edge strict rank (A').
4. Restate `squares_gen` (§4) and redo `AuxRankSign.forced_aux` / `freePolicy_aux` for (A').
5. The selected-edge slip permit (§5(b)) to discharge `FreeNamedInputs.permitted` without the `auxS` slip constraint.
6. Only then decide whether `hstrictR` in `free_named_inputs` becomes the Bellman rank for `permitsQ1` with the named no-fort premise.

## 7. Corner

Still last, as the lead directed.
