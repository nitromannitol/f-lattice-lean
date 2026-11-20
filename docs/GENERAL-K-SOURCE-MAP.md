# GeneralK source correspondence

The sibling manuscript *Recurrence on the F-lattice and its generalizations* is in `/home/nitro/flattice-simple-proof-reference`. Verify its TeX sources and PDF from the campaign repository root.

```sh
(cd /home/nitro/flattice-simple-proof-reference &&
  sha256sum --quiet -c /home/nitro/flattice-lean/docs/general-k.sha256)
```

The GeneralK namespace is `FLatticePaper.GeneralK`. The [corrected October 2023 source map](../SOURCE-MAP.md) records the obligations for the primary manuscript and its literal constructor.

| Local source | Proof obligation |
| --- | --- |
| `short-proof.tex:24–33`, `sec:graph` | On $\mathbb Z^2$, use horizontal inputs exactly when the coordinate sum is zero modulo $k$. Define $\eta=-\Delta g$, the actual incoming boundary, comparison with global integer superharmonic competitors on finite induced strongly connected sets, and quadratic growth with error $o(\lvert x\rvert^2)$. |
| `short-proof.tex:35–48`, `lem:fort`, `eq:fort` | For superharmonic heights, prove exact equivalence of comparison, absence of a nonempty finite set with incoming degree at least $2-\eta$ at each member, and absence of a nonzero finite nonnegative integer lowering. Prove the least-rank criterion for binary patterns independently of their realization as charges. |
| `paper/chains.tex:1–25`, `thm:ports`, `eq:ports` | Identify the unique chain coordinates from $B(u,v)=(u+v,-u+(k-1)v)$. Give the forbidden interval between two black interior sites. With at most one black interior, derive the first and last bits from the independently marked bottom and top. At $k=2$, the two entries refer to the same site. Prove the two directions between finite physical forbidden sets and finite nonempty markings passing the horizontal-slot quota test. |
| `paper/chains.tex:27–40`, `prop:phase` | For all binary residue-only patterns, prove recurrence exactly when at most one residue is black and construct an integer height with that charge. Use the decreasing ranks, the vertical interval when both black residues are nonzero, and the two explicit cross-supported segments when zero and a nonzero residue are black. |
| `paper/chains.tex:42–62`, `thm:lift`, `eq:ret` | Prove pointwise leastness and endpoint monotonicity of the integer concave chain with slopes $q+1$ then $q$. Evaluate both actual horizontal inputs by ceilings. Prove recurrence exactly for the least lift with no finite legal retained lowering, and prove recurrence when the retained operator is identically zero. |
| `paper/families.tex:1–36`, `thm:baseline` | For each symmetric integer retained matrix with $(k-1)M_{11}+M_{22}=-k$, construct a superharmonic representative. Show that $j=(M_{11}-M_{12})\bmod k\le k-2$ gives an odometer and a boundary matrix by the leftmost-column test, and that $j=k-1$ gives an interior matrix with no recurrent representative. Track congruence by $B^{-1}$ and the harmonic adjustment. |
| `paper/families.tex:38–63`, `thm:scalar`, `eq:peakexample` | Solve the stated scalar second-difference equation on all of $\mathbb Z$ with $p(0)=p(1)=0$. Prove zero retained operator, calculate the exact quadratic growth from the mean of the periodic forcing, and check the displayed physical Hessian for $a=k-1$, $b=-2$. |
| `paper/growth.tex:1–48`, `thm:cell` | Define the rounded and shifted matrix, physical floor height, and finite quotient with $4kh^2$ classes and the actual input incidences at the seams. Prove full-round termination and acceptance iff a periodic integer correction exists. For each real symmetric $A$, prove membership in $\Gamma_k$ iff all $h\ge1$ accept. Prove the boundary criterion using acceptance for $A$ at every scale and, for each $j\ge1$, rejection for $A+I/j$ at some scale. |
| `paper/farey.tex:1–66`, `lem:threshold`, `prop:mid`, `prop:strip`, `lem:cutoff` | Track the signed threshold and translated-midpoint hypotheses and the one-dimensional strip burn with its stated cutoff. Relate periodic data to the physical graph and keep the finite strip certificates scoped to the patterns verified. |
| `paper/staircases.tex:1–297`, `thm:standard`, `thm:alternate`, `cor:stairs` | Check both displayed staircase arrays and recurrence ranks for every odd $d\ge3$, and the growth, non-affine difference, and reciprocal harmonic transport. An identity with the primary manuscript's native tiles requires the primary occupied domains, height gauges, and period conventions. |
