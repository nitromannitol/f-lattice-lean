# Independent audit of B7 rank and conditional rank gluing

**Status: B7 symbolic recurrence proof independently checked; no
mathematical gap found.** This audit read `BASE-B7-RANK.md` against
the domain, overlap, and exact Laplacian tables in
`BASE-B7-ANALYSIS.md`. It did not use the paper, run a broad
computation, or infer a uniform claim from the existing finite check.

## B7

The rank regions C,E,T,S,B,D,L,R,M,Z are disjoint. In particular the
two high regions L,R cannot overlap because R has \(x\ge d-1,y\ge1\),
while L has \(x+y\le d-1\). The central diagonal D is separated from
L,M by its exact sum \(d\); all other potential overlaps are excluded
by their row or coordinate bounds.

All three overlap types have equal corrections at their two
representatives. The nontrivial formulas are the singleton V overlap
\((d-1,0)\leftrightarrow(0,d+1)\), of common height \(8d+1\), and
the row-one V overlaps, where both R and T give
\(8(2d-1-j)+p\). The U and U+V cases have constant heights 1 and 4.

The even AND differences were recalculated from the displayed
formulas: they are exactly the claimed \(3-16d,-1\),
\(3-4d,-1\), \(-1,7-4d\), and the central-diagonal differences
\(-1,4x-8d+7\) or \(-1,-5\). The largest possible
\(4x-8d+7\) is \(-4d-5\). Every bound is strict at \(d=4\).

The even OR directions remain in the stated regions except for the
explicit exits. In the Z case, the only possible even locations are
negative \(x\), the ordinary bottom row, and \((0,d)\); the unique
negative left exit is \((1-d,d-1)\). Its outside neighbor has
representative \((d,d+1)\), of height 5, giving rank drop 1.

For odd AND vertices, the height comparisons in S,L,R,M,Z hold.
The R boundary estimate \(8\le H\) is valid because \(y\ge2\) and
odd sum at most \(2d-1\) force \(x\le2d-3\); the S endpoint
comparison \(4d+4\le8d\) already holds at \(d=4\).
Odd Z AND points are precisely among the claimed negative interior
points; every other odd Z boundary category is OR.

The ten rows of the odd OR choice table cover the two exceptional
points, two inner diagonals, and three reflected pairs of boundary
types. Each listed neighbor representative has correction exactly one
smaller than its center. The incoming moves are vertical, so the
linear part \(6x\) does not change.

For an explicit audit of the smallest parameter, \(d=4\), the special
heights are
\[
\rho(-1,-1)=\rho(4,6)=4,\qquad \rho(4,5)=5,
\]
and the two central corrected points have
\(\rho(1,3)=52,\rho(2,2)=44\).
The outside left neighbor of \((-1,-1)\) is represented by
\((6,1)\) of height 9. The left exit from \((-3,3)\) is represented
by \((4,5)\) of height 5. The top odd points \((1,6),(3,6)\)
have heights 25 and 9; their chosen upper neighbors are represented
by \((4,2),(6,2)\), of heights 24 and 8. These check the parameter
endpoints where the middle interval in the domain row table is empty.

Two prose corrections, neither affecting the argument:

* “The four low/high boundary lists” should say six lists, namely
  three reflected pairs.
* The forbidden-set characterization is L6(a); L9 is the sufficient
  decreasing-rank criterion. The final contradiction can cite both.

The header of `BASE-B7-ANALYSIS.md` also still says recurrence is
remaining; it should now refer to the separate completed rank proof.

## Conditional rank gluing

RG1 is correct: an attaining rank gives
\(r(y)\le r_i(y)<r_i(x)=r(x)\), and the finite forbidden-set
argument requires no global lower bound on \(r\).

The translation calculation RG3 is correct. Its integrality uses
\(Mt\in\mathbb Z^2\) for \(t\in L'\), which follows from the
already established lattice formulas and should be named as a
dependency.

The common constant in RG4 is also correct: substituting actual
star point \(v_0+z\), copy origin \(v_0+\delta v_j\), and copy
slope \(a_0+\delta a_j\) leaves
\(u\cdot(v_0+z_0)+\lambda\cdot a_0\) outside the displayed local
height formula. Completeness of the covering-copy list at every
star point is explicitly and correctly required.

There is one coordinate issue in RG5 as presently written.
\(\sigma\) was defined in global coordinates, whereas \(z_0\) is
the local coordinate of a witness. Thus the required cardinality is
\[
2-\sigma(v_0+z_0),
\]
or equivalently \(2-\sigma_0(z_0)\) after explicitly setting
\(\sigma_0(z)=\sigma(v_0+z)\). Likewise the vector \(e\) defining
the two local star neighbors must be chosen using the actual
center's parity convention, or the translated local convention.
The distinction matters when \(v_0\) is odd. The finite checking
script already records and uses witness parity; the lemma's
notation should match it.

After that coordinate correction, the conditional lemmas are sound.
Their remaining mathematical obstruction is the stated one:
construct rank candidates satisfying every complete star inequality
and prove the configuration atlas complete for all recursive outputs.
