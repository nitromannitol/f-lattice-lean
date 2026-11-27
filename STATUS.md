# Status

This file states what the repository proves and which named hypotheses the headline theorems still take.
The Lean sources are the authority; each link points to the declaration.

**Target.** The target is the surgical edition of the October 2023 manuscript: the author's arXiv text with minimal
corrections in its own language, pinned at commit 274ad18 of its source repository (Sections 1–9). The new Section 9 failed its
audit: its standard extension (lemma:global_odometers for standard tiles) and the periodicity and growth algebra are sound,
while its proof of recurrence and of the alternate extension is not a proof, and the general recurrence is open. The standard extension is proved in Lean for both children with no remaining covering hypothesis (item (ii) of `lemma:common-extension-pseudo-square` is proved for both standard tiles); it is stated for the weak family, which is the tile family at the children Section 8 does not correct. Sections 1–8 are being mapped to the Lean statement by statement in [SOURCE-MAP.md](SOURCE-MAP.md), and the
statements corrected in Sections 5–8 are restated and proved in their surgical form. The corrected edition pinned in
[paper/](paper/README.md) replaced the proofs of Sections 6, 8 and 9 by a supplement; the headline theorems below follow
that edition, and their named hypotheses belong to the supplement's route. That code stays as a library.

**Surgical edition, open inputs.** The surgical text now proves the packing in item (d) of `lemma:standard_tile_properties`
(no cell lies in a copy of each parent of a standard decomposition) and the consistency of the offset constants of the placed
subodometers around closed paths (condition (C)) for every decomposition, standard, alternate and corrected. The Lean still
carries both as named inputs (`Tiles.CellRegisters`, `CellsDisjointOdd`; `Tiles.ChildGlue`, condition (C)) until those proofs
are formalised. The weak odometers of Section 7 are built from the tile odometers of the parents (Section 8), so Sections 7 and 8
are formalised as one induction over the recursion word. Open in the text: E29, items (3)–(5) of
`lemma:alternate_tile_properties`, and the local compatibility of overlapping copies claimed in Section 8 (checked numerically to
length 5).

## Headline theorems

| Statement | Declaration | Named hypotheses still taken |
| --- | --- | --- |
| Odometers theorem, with both twos flatness inputs proved | [`odometersTheorem_no_flat`](FLatticePaper/FlatMinusHeadline.lean) | `hgames` (games with a rank at the proper words that are not powers of two), `hW1` (the conjugate `W1Forced` condition) |
| Odometers theorem, with the sign $+1$ twos flatness proved | [`odometersTheorem_no_flatP`](FLatticePaper/FlatPlusHeadline.lean) | `hflatM`, `hgames`, `hW1` |
| Odometers theorem, with the boundary-price input proved | [`odometersTheorem_no_hbd`](FLatticePaper/TraceHeadline.lean) | `hflatP`, `hflatM`, `hgames`, `hW1` |
| Hyperbola | [`hyperbola_of_odometersTheorem`](FLatticePaper/MainTheorems.lean) | the odometers theorem `OdometersTheorem` |
| Circle packing | [`circlePacking_of_odometersTheorem`](FLatticePaper/MainTheorems.lean) | the odometers theorem `OdometersTheorem` |
| Global odometers statement | [`global_odometers_all`](FLatticePaper/Plane/GlobalOdometersAll.lean) | `hstar`, `hsheet`, `harc`, `hodd`, `hbulk` (at the proper words) and the tile data `tile`, `htile`, `hsites` |

The odometers theorem `OdometersTheorem` is the hypothesis of the hyperbola and circle packing statements. It is
proved in the form above only after the remaining named hypotheses are supplied.

## Proved results (selection)

- Physical graph, Laplacian and incoming boundary: [Graph.lean](FLatticePaper/Graph.lean).
- Finite comparison from a burning rank: [Rank.lean](FLatticePaper/Rank.lean), `finiteComparison_of_allowed`.
- Recurrence criterion for superharmonic integer fields, in both directions: [Plane/Recurrence.lean](FLatticePaper/Plane/Recurrence.lean), `recurrent_iff_allowed`.
- Both endpoint fields are recurrent: [Endpoint.lean](FLatticePaper/Endpoint.lean), `zeroEndpoint_recurrent` and `oneEndpoint_recurrent`.
- Ordered height rule and the correction height: [Construction/OrderedOverlap.lean](FLatticePaper/Construction/OrderedOverlap.lean), [Construction/CorrectionHeight.lean](FLatticePaper/Construction/CorrectionHeight.lean).
- Alternate midpoint: a binary Laplacian and a lexicographic rank: [Plane/AlternateMidpoint.lean](FLatticePaper/Plane/AlternateMidpoint.lean).
- Threshold minima: [Plane/ThresholdMinimum.lean](FLatticePaper/Plane/ThresholdMinimum.lean).
- Farey birth and parent registers: [Farey/RationalBirth.lean](FLatticePaper/Farey/RationalBirth.lean).
- The standard field of $2^{k+1}$ as a sewn minimum: [Plane/Induction/TwosField.lean](FLatticePaper/Plane/Induction/TwosField.lean), `standardField_twos_succ`.
- Twos flatness of sign $+1$ at every centre: [Plane/Induction/TwosFlatPlus.lean](FLatticePaper/Plane/Induction/TwosFlatPlus.lean), `twos_flat_plus`.
- Twos flatness of sign $-1$ at every centre: [Plane/Induction/TwosFlatMinus.lean](FLatticePaper/Plane/Induction/TwosFlatMinus.lean), `twos_flat_minus`, from the tile claim at every centre ([Plane/Induction/TwosMinusTile.lean](FLatticePaper/Plane/Induction/TwosMinusTile.lean), `twos_hTile_minus`).
- The matrix classification of the `GeneralK` track: [GeneralK/MatrixClassification.lean](FLatticePaper/GeneralK/MatrixClassification.lean), `growthSet_eq_closure_columnCones` for every $k\ge2$.

## Open

- **Games with a rank (`hgames`).** The canonical signed games at a proper word that is not a power of two: the restricted
  no-fort condition of the auxiliary game, and the raw slip along the forced edges of the canonical policy.
- **The conjugate forcing condition (`hW1`).** The face rows and the top squares of the collar, and the chain inputs.
- **Local premises.** The earlier headline forms in [MainTheorems.lean](FLatticePaper/MainTheorems.lean) take `LocalPremises` at every word containing a digit $1$ or $2$
  (equivalently `Induction.OpenInputs` and `StarEstimates`). The plane induction needs three inequalities for the two
  sheets of the quarter-turned odd parent: $C\ge0$ where $t\ge1-d$; the sheet not equal to $h_0$ is at least $h_0$ where
  $s\le2L-1$; and $\min(A,C)$ has Laplacian in $\{-1,0\}$ on the closed polygon. All three hold for the non-pure words
  of length at most three; in general they are not yet proved.
- **Alternate tiles.** Read literally, `def:alternate_tiles` gives tiles that do not satisfy
  `lemma:alternate_tile_properties`: there are holes and a broken $180$-degree symmetry at the odd child of $31$, and the
  rotation identity fails at the word $1$ ([FLatticePaper/Tiles/AlternateTiles.lean](FLatticePaper/Tiles/AlternateTiles.lean)).
  The second reading in [FLatticePaper/Tiles/AlternateConstructor.lean](FLatticePaper/Tiles/AlternateConstructor.lean)
  removes the holes and symmetry failures but fails the rotation clause at $14$ other child tiles.
- **Near-one charts.** In the TeX coordinates of `lemma:staircase_laplacian` the periodic extension is not superharmonic on
  the physical graph. The smallest case is $d=3$ at the even site $(0,2)$: the Laplacian there is $+1$, while the right side
  lies in $\{-1,0\}$. Reading each TeX point $x$ as the physical site $x+(0,1)$ gives a binary superharmonic recurrent field
  for the four near-one families.
- **General plane ranks, mixed evaluation and mixed occupied-domain coverage** for all words, and the finite-tile height
  comparisons of actual shifted sources, are open.

## GeneralK track

The separate `FLatticePaper.GeneralK` track covers the real symmetric matrix classification for every integer $k\ge2$.
Its source pins are in [docs/](docs/general-k.sha256). The geometric critical exhaustion for $k\ge3$ is open.
