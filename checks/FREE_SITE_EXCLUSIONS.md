# The ordered free-site exclusions: the '+' row (task 72, Q1 paragraph 6)

Scope: the '+' row of Q1.md l.21–28 only (the '−' row is Q13). This report records what is checked numerically, what reduces to
lemmas in `main`, and where the remaining steps are. It does not prove the per-entry implications.

## 1. The row and the statement schema

With `L = d + n`, `r = D + N`, `U = (d, n)` (kernel), `V = (n − d, n + d)` (transverse), `H_j`, `V_j` the free H and V sites in
the order of the curves `H[j]`, `V[j]` (FIXED_FREE_GAME_AUDIT §2; `.work/fields/escape/free_fixed_audit/routes.py`), `V_{j+L} = V_j + V`:

    V_{−r−1}, …, V_{−1},  H_0,  V_0, V_1, …, V_{L−r−2},  H_{d−1}−U, …, H_1−U.

The row has `L + d` entries, one per free deck class (`scripts/free_site_exclusions.py`). Each entry `e_k` has a successor `e_{k+1}`
and a route to it. Q1 l.30 gives the per-entry implication: membership of `e_k` forces one of

* (E) a componentwise lower endpoint with one strict inequality (a grade test at `e_k`);
* (P) an earlier entry `e_{k'}`, `k' < k`;
* (F) a finite fort of the recurrent comparison chart (contradicts recurrence on the finite core).

Route classes (Q1 l.30; `routes.py`):
* V-passage (ascending V): `N` (odd start, step `(0,1)`), `N–W` (odd, other step), `W–N–E` (even start);
* H-passage (descending in the row, so the forward route reversed): `E` (even start, step `(1,0)`), `E–N` (even, step `(1,1)`),
  `N–E–S` (odd start);
* transitions `(V_{−1}, H_0)`, `(H_0, V_0)`, `(V_{L−r−2}, H_{d−1}−U)`, `(H_1−U, V_{−r−1})`: tip routes (TIP_THEOREM).

## 2. Numeric results (`scripts/free_site_exclusions.py`)

| children (odd coprime, `n + 2 ≤ d`) | rows (all `r ∈ [0, L−1]`) | V-passages | H-passages | interior sites | bad interior sites | class clashes | curve ⊄ Lean free set |
|---|---|---|---|---|---|---|---|
| `d ≤ 21`: 47 | 1018 | 23591 | 14578 | 37151 | **0** | **0** | **0** |
| `d ≤ 31`: 106 | 3422 | 121418 | 76398 | 194394 | **0** | **0** | **0** |

Transitions (tip routes): 3007 (`d ≤ 21`), 10160 (`d ≤ 31`), counted, not classified here.

"Bad interior site" = a site of a passage (other than its endpoints) that is a deck translate of a free site (exact class key
`((x V₂ − y V₁) mod T, (K₁ y − K₂ x) mod T)`). "Curve ⊄ Lean free set" = a curve site not in `ChildFrame.freeH`/`freeV` (Lean definitions
of `S3FreeBoundary`, reproduced in the script). The check is not a proof: it covers the finitely many children listed.

## 3. Reduction to `main`

| class | Lean lemma in `main` | status |
|---|---|---|
| entries are free sites | `ChildFrame.freeH`, `ChildFrame.freeV` (`S3FreeBoundary`) | definitions only |
| free V sites are white | `Q3White.laplacian_eq_zero_of_freeV` | reduces (needs `HasStrips`) |
| V-block index and membership | `Q3Para10.index_of_freeV`, `block_mem_freeV`, `parent_block_mem_freeV` | reduces (block membership) |
| `V_p + I` not free in the current frame | `Q3Para10.VpI_not_freeV` | reduces (note: free in the parent frame, see `checks/CanonicalSigned.lean` data) |
| a translate of a free site is not in the strict interior | `NonfreeBridge.outside_SI_free`, `nonfree_bridge` (task 72) | reduces (the converse direction of the H/V web) |
| short passages: interior sites nonfree | none | numeric only (section 2) |
| tip paths | none | not classified |
| fans, quadratic cap | none | not formalized |

So no short-passage, tip or fan step is a Lean lemma in `main`; the numeric passage facts are the only support for them.

## 4. The named steps the others need (source and section)

* Short H middles nonfree (E, E–N, N–E–S): `.work/fields/escape/free_fixed_audit/FIXED_FREE_GAME_AUDIT.md` §3 "Every short H middle is nonfree".
* Short V middles nonfree (N, N–W, W–N–E): same file §4 "Every short V middle is nonfree".
* Canonical first directions at the core ports: same file §5.
* Cut-tip intermediates, both phases (the transitions): same file §6; and `.work/fields/escape/newzeros/TIP_THEOREM.md`
  "Minus-sign cut tip: two different physical routes" and "universal two-edge cut-tip escape".
* No translated free site lies in the strict interior of E: same file §7 (proved in Lean: `NonfreeBridge.outside_SI_free`).
* Core contact transfers in the fixed-free game: same file §8.
* High and low parabolic fans: same file §9; the uniform quadratic cap for the remaining midpoints and the short arcs (the
  passages): `.work/fields/escape/ALL_SLOPE_STEP.md` "Two parity windows; short arcs", "The uniform quadratic cap for all remaining
  midpoints", "Why this scalar cap kills all long forks".
* Margins for the passage inequalities: `.work/fields/escape/free_fixed_audit/guards.py` and `GUARDS.json` (nine exact positive
  polynomials); reflection of the free table: `directions.py` and `DIRECTIONS.json`.

## 5. Limits

* The per-entry implications (E), (P), (F) are not checked; only the route geometry and the nonfree middles are.
* Children up to `d = 31`; the audit files record the same scope (`routes.py`, up to `d ≤ 101`, "not universal proof").
* Transitions (tip routes) are not classified by the script.
