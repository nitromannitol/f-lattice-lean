# B7 recurrence by an explicit rank (2026-10-20)

**L22 for B7 [PROVED].** B8 follows by the proved harmonic rotation.
The proof uses only the B7 covering and exact Laplacian classification in
`BASE-B7-ANALYSIS.md`, and the elementary decreasing-rank criterion L9.
It does not use the paper's proof.

Let \(d\ge4\) be even. Use the B7 formula coordinates, domain \(D\),
\[
 U=(2d,2),\qquad V=(1-d,d+1),\qquad T=d^2+2d-1.
\]
Write \(p=(x+y)\bmod2\), \(a=(-1,-1)\), and \(b=(d,d+2)\).
Define \(\rho\) on \(D\) by the following **disjoint** cases.
The letters are only references for the proof, not new geometric assumptions.

| region | condition in \(D\) | \(\rho(x,y)\) |
|---|---|---|
| C | \(z=a\) or \(z=b\) | \(4\) |
| E | \(z=(d,d+1)\) | \(5\) |
| T | \(y=d+2,\ 0\le x\le d-1\) | \(8(d-x)+p\) |
| S | \(y=d+1,\ 0\le x\le d-1\) | \(8d-4x+p\) |
| B | \(x+y=2d,\ d\le x\le2d-2\) | \(8\) |
| D | \(x+y=d,\ 1\le x\le d-2\) | \(8(d+y)-4\) |
| L | \(x\ge0,\ y\ge0,\ x+y\le d-1\) | \(8(2d-1-x)+p\) |
| R | \(x\ge d-1,\ 1\le y\le d,\ x+y\le2d-1\) | \(8(2d-1-x)+p\) |
| M | \(1\le x\le d-2,\ y\le d,\ x+y\ge d+1\) | \(8d-4x+p\) |
| Z | every remaining point of \(D\) | \(p\) |

All displayed conditions are inequalities or equalities in integers. In
particular, no limiting interpretation is needed at \(d=4\).

## Periodic consistency of the rank

The complete positive overlap list for \(D\) is \(U,V,U+V\), with endpoints
as proved in `BASE-B7-ANALYSIS.md`. Each vector has even coordinate sum,
so it preserves \(p\).

* On the \(U\) overlap, the lower endpoint is
  \(z=(-1-y,y)\), \(1\le y\le d-2\). Both \(z\) and
  \(z+U=(2d-1-y,y+2)\) lie in Z and are odd, so both have \(\rho=1\).
* The \(V\) overlap on \(z=(j,-1)\), \(0\le j\le d-1\), joins
  two Z points: the upper point is \((j+1-d,d)\). This includes
  the upper point \((0,d)\) when \(j=d-1\), which is Z. Both heights are \(p\).
* The remaining single \(V\) overlap at \(z=(d-1,0)\) joins L to
  S at \((0,d+1)\). Both heights are \(8d+1\).
* The \(V\) overlaps \(z=(j,1)\), \(d-1\le j\le2d-2\), join R
  to T at \((j+1-d,d+2)\). The two displayed formulas both give
  \(8(2d-1-j)+p\).
* The \(U+V\) overlap joins \(a\) to \(b\), both of height \(4\).

Negative overlaps give the same equalities in reverse. Covering and these
equalities therefore define a unique \(\langle U,V\rangle\)-periodic integer
function \(\rho\) on all of \(\mathbb Z^2\). Put
\[
 R(x,y)=6x+\rho(x,y).
\]
Translation by a lattice vector \(u\) adds the constant \(6u_x\) to \(R\);
all neighbour inequalities therefore translate from \(D\) to the plane.

The rest of the proof verifies that every AND vertex has both
in-neighbours of strictly smaller rank, and every OR vertex has a
specified in-neighbour of strictly smaller rank. Every drop is at least
one. At even vertices the neighbours are horizontal; at odd vertices
they are vertical.

## Even AND vertices

The exact Laplacian classification has just the following three sets.

1. If \(x=0\) and \(0\le y\le d-2\), with \(y\) even, the centre
   is L with height \(16d-8\). Its left neighbour is Z of height \(1\),
   and its right neighbour is L of height \(16d-15\).
   Their rank differences from the centre are \(3-16d\) and \(-1\).

2. If \(x=d-1\) and \(3\le y\le d+1\), with \(y\) odd, first suppose
   \(y\le d-1\). The centre is R of height \(8d\), its left neighbour
   is M of height \(4d+9\), and its right neighbour is R of height
   \(8d-7\). Their rank differences are \(3-4d\) and \(-1\).
   If \(y=d+1\), the centre is S of height \(4d+4\), its left
   neighbour is S of height \(4d+9\), and its right neighbour is E
   of height \(5\). The differences are \(-1\) and \(7-4d\).

3. On \(x+y=d,\ 1\le x\le d-2\), the centre is D of height
   \(16d-8x-4\). Its left neighbour is L of height
   \(16d-8x+1\), giving difference \(-1\).
   If \(x\le d-3\), its right neighbour is M of height
   \(8d-4x-3\), giving difference \(4x-8d+7\le-4d-5\).
   If \(x=d-2\), its right neighbour is R of height \(8d+1\),
   giving difference \(-5\).

All these differences are negative for \(d\ge4\).

## Even OR vertices

The regions above give an exhaustive split, since C, T, S, B, L, R, M
and Z contain all even vertices not already listed; E is odd and every
D vertex is AND.

| region of centre | chosen direction | verification of the rank drop |
|---|---|---|
| C | left | At \(a\), the outside neighbour \((-2,-1)\) is represented by \((2d-2,1)\) via \(+U\), of height \(9\); at \(b\), the left neighbour is T of height \(9\). In both cases the difference is \(-6+9-4=-1\). |
| T | right | Even \(x\) satisfies \(0\le x\le d-2\). The neighbour remains T and its height is the centre height minus \(7\), so the rank difference is \(-1\). |
| S | left | Here \(x\) is odd, \(1\le x\le d-3\); the endpoint \(x=d-1\) is AND. The neighbour remains S and its height is the centre height plus \(5\), giving difference \(-1\). |
| B | right | The neighbour has height \(1\), giving \(6+1-8=-1\). It is Z inside \(D\), except from \((2d-2,2)\), when the outside point \((2d-1,2)\) is represented by \((-1,0)\) via \(-U\), also of height \(1\). |
| L | right | Since \(x=0\) would be AND, \(x\ge1\). Evenness gives \(x+y\le d-2\), so the right neighbour remains L. Its height is smaller by \(7\), giving difference \(-1\). |
| R | right | Evenness gives \(x+y\le2d-2\). The right neighbour remains R, with height smaller by \(7\), giving difference \(-1\). |
| M | left | An even M point has \(x+y\ge d+2\), hence \(x\ge2\) because \(y\le d\). The left neighbour remains M, with height larger by \(5\), giving difference \(-1\). |
| Z | left | The centre has height \(0\). The neighbour has height \(1\), except at the sole left exit from \((1-d,d-1)\), when its representative via \(+U\) is \((d,d+1)\), of height \(5\). The differences are respectively \(-5\) and \(-1\). |

For the last row, exhaustiveness can also be checked directly without
using a drawing. An even Z point is either on the bottom row \(y=-1\),
with odd \(x\ge1\); has \(x<0\); or is \((0,d)\).
The left neighbour is a Z point of odd parity unless it is the one
listed left exit. Indeed the B7 row intervals show that the only even
left endpoint among the negative rows is \((1-d,d-1)\).

## Odd AND vertices

There are no odd points in C, B, D; E and all odd T points are OR.
All odd S points are AND. The remaining possibilities are L, R, M, Z.

* **S.** Here \(x\) is even with \(0\le x\le d-2\), and the centre
  height is \(8d-4x+1\). If \(x=0\), the neighbours below and above
  have heights \(0\) and \(8d\). If \(x\ge2\), they are respectively
  M and T, of heights \(8d-4x\) and \(8d-8x\).
  Both are strictly smaller.

* **L.** Set \(H=16d-8-8x\), so the centre has height \(H+1\).
  An odd L point with \(x+y=d-1\) and \(1\le x\le d-2\) is OR
  and is not considered here. At every remaining odd L point, each
  vertical neighbour is an even L point of height \(H\), a Z point
  of height \(0\), or the R point \((d-1,1)\) of height \(H=8d\).
  More explicitly: a lower neighbour leaves L only when \(y=0\),
  in which case it is on the bottom row and has height \(0\).
  An upper neighbour leaves L only at the two endpoints of
  \(x+y=d-1\), namely \((0,d-1)\) and \((d-1,0)\);
  their upper neighbours are \((0,d)\) and \((d-1,1)\).
  Since \(H\ge8d>0\), both neighbour heights are at most \(H\).

* **R.** Put again \(H=16d-8-8x\). Every odd R vertex in row
  \(y=1\) is OR, so an odd AND point has \(y\ge2\).
  Its lower neighbour is R of height \(H\).
  Its upper neighbour remains R unless \(x+y=2d-1\).
  In that boundary case, if \(x\ge d\) the upper neighbour is B
  of height \(8\le H\); if \(x=d-1,y=d\), it is S of height
  \(4d+4\le8d=H\). The inequality \(8\le H\) follows from
  \(x\le2d-3\), forced by \(y\ge2\). Thus both neighbours
  have height at most \(H\), while the centre has height \(H+1\).

* **M.** The odd M points on \(x+y=d+1\) are OR. Every remaining
  odd M point has \(x+y\ge d+3\). The lower neighbour is M;
  the upper is M if \(y<d\), and S if \(y=d\).
  Both have height \(8d-4x\), one less than the centre.

* **Z.** An odd Z point which is AND has \(x<0\) and
  \(1\le y\le d-1\). The excluded odd OR sets are precisely the
  bottom row, the lower and upper outer diagonals, the reflected
  row \(y=d\), and \((-1,0)\).
  Its two vertical neighbours therefore lie inside \(D\) and
  have height \(0\). In particular neither can be \(a\), since its
  only vertical odd neighbour in \(D\) is the excluded point
  \((-1,0)\). The centre height is \(1\).

For these vertical moves the rank differences equal the differences
of \(\rho\), so every displayed strict inequality is sufficient.

## Odd OR vertices

The exact odd OR classification from `BASE-B7-ANALYSIS.md` is exhausted
by the following table. There are no odd OR points in S, and C, B, D
are even.

| centre | chosen direction | height of the chosen neighbour |
|---|---|---|
| E: \((d,d+1)\) | up | \(4\) at \(b\), one below the centre height \(5\) |
| T: \(y=d+2,\ x\) odd, \(1\le x\le d-1\) | up | The outside point \((x,d+3)\) is represented by \((x+d-1,2)\) via \(-V\). Its height is \(8(d-x)\): it is R for \(x\le d-3\) and B for \(x=d-1\). |
| L: \(x+y=d-1,\ 1\le x\le d-2\) | down | It remains L, of height \(16d-8-8x\). |
| R: \(y=1,\ x\) even, \(d\le x\le2d-2\) | up | It is R of height \(16d-8-8x\) for \(x\le2d-4\), and B of height \(8=16d-8-8x\) for \(x=2d-2\). |
| M: \(x+y=d+1,\ 1\le x\le d-2\) | up | It is M of height \(8d-4x\), except at \(x=1\), when it is S of that same height. |
| Z: \(y=-1,\ x\) even, \(0\le x\le d-2\) | down | The outside point \((x,-2)\) is represented by \((x+1-d,d-1)\) via \(+V\), a Z point of height \(0\). |
| Z: \(x+y=-1,\ 1\le y\le d-2\) | up | It remains inside \(D\), negative \(x\), and is Z of height \(0\). |
| Z: \(x+y=2d+1,\ d+1\le x\le2d-2\) | up | The outside point \((x,y+1)\) is represented by \((x-2d,y-1)\) via \(-U\), a Z point of height \(0\). |
| Z: \(y=d,\ x\) odd, \(1-d\le x\le-1\) | down | It remains in D and is Z of height \(0\). |
| Z: \((-1,0)\) | up | The point \((-1,1)\) is Z of height \(0\). |

Every chosen neighbour has height exactly one less than the centre.
The six low/high boundary lists here are exactly the three odd exit
lists and their reflections: bottom row ↔ T, lower outer diagonal ↔
upper outer diagonal, and R row \(1\) ↔ negative row \(d\).
The remaining lists are the two exceptional odd points and the two
inner diagonals. Thus no odd OR case is omitted.

## Conclusion and independent check

Select both lower-rank in-neighbours at every AND point and the stated
one at each OR point. The integer \(R\) strictly decreases along every
selected edge. If a finite nonempty forbidden set existed, a point of
minimal \(R\) in that set could not satisfy its required internal
neighbour condition: an AND point needs at least one internal
in-neighbour and an OR point needs both. This contradicts L6(a)'s
forbidden-set characterization, equivalently L9's rank criterion,
and proves recurrence.

`scripts/base_b7_explicit_rank.py` independently constructs the A1 tile
and its periodic extension, without importing the recurrence algorithm,
the fixed-point rank experiment, or the main odometer checker.
It checks all repeated rank representatives, computes the actual
Laplacian, and tests both/one decreasing inequalities as appropriate.
It passed **985332 in-stars** for every even \(4\le d\le100\), and
\(d=128,202,502\); see `data/base_b7_explicit_rank.check.json`.
The proof above is uniform; this computation is an independent
adversarial check, including the minimum parameter and all boundary types.
