# B7: uniform compatibility, covering and Laplacian (2026-10-20)

**L20, L21, L23 and L24 for B7, and hence B8 by L29 [PROVED].** Recurrence is proved separately in BASE-B7-RANK.md and BLUEPRINT §4.13.
Let $d\ge4$ be even, $T=d^2+2d-1$, $U=(2d,2)$, $V=(1-d,d+1)$, and
$c_1=-1$, $c_2=-(d^2+5d-2)/2$. Put
$$Q(y)=-y(y+1)/2,\quad F(x,y)=Q(y)+\min(x,0)+\max(x+y-d,0)+\min(d-1-x,0).$$
The B7 tile equals $F+\mathbf1_C$ on its domain $D$, where
$$C=\{(x,d-x):1\le x\le d-2\}\cup\{a=(-1,-1),\ b=(d,d+2)\}.$$
The apparent omitted minimum on A1's correction line is zero there, so this is exactly A1.

## Compatibility and covering

All domain cells satisfy $1-d\le x\le2d-2$, $-1\le y\le d+2$.
The width of the interval containing their levels $x-dy$ is at most $d^2+6d-3<2T$.
If two cells differ by $aU+bV$, then their levels differ by $-bT$, so $|b|\le1$.
For $b=0$, the horizontal width gives $|a|\le1$.
For $b=1$, the vertical width gives $2a+d+1\le d+3$, hence $a\le1$;
the lower horizontal bound gives $2ad+1-d\ge-3d+3$, hence $a\ge0$.
Negating handles $b=-1$. Therefore only $\pm U,\pm V,\pm(U+V)$ can occur.

The complete list of lower endpoints is:

| displacement | lower endpoints $z$ | number |
|---|---|---|
| $U$ | $(-1-y,y)$, $1\le y\le d-2$ | $d-2$ |
| $V$ | $(j,-1)$, $0\le j\le d-1$; $(d-1,0)$; $(j,1)$, $d-1\le j\le2d-2$ | $2d+1$ |
| $U+V$ | $a=(-1,-1)$ | $1$ |

For $U$, the sum of coordinates increases by $2d+2$, so an ordinary pair must connect the two extreme bands
$x+y=-1$ and $x+y=2d+1$. The horizontal bounds give exactly $1\le y\le d-2$.
The exceptional corner candidates fail the horizontal bounds. For $V$, its vertical displacement is $d+1$,
so the lower row is $-1,0$, or $1$; substitution of the row intervals below gives the three listed cases.
For $U+V$, the sum increases by $2d+4$, larger than the width of the ordinary band, so only $a,b$ can pair.
These arguments also prove there are no omitted endpoints.

At the $U$ endpoints the values are $Q(y)-1-y$ and $Q(y+2)+y+1$, whose difference is $-1=c_1$.
At the $V$ endpoints the value differences, in the order of the three listed cases, are
$$j-\frac{d^2+3d-2}{2},\qquad -\frac{d^2+3d}{2},\qquad
j-\frac{d^2+7d-2}{2}.$$
These equal $s(z)+c_2$ respectively for $s(z)=j+d,d-1,j-d$.
For $U+V$, $o(a)=0$, $o(b)=-(d+1)(d+2)/2$, so the difference is
$s(a)+c_1+c_2=(d-1)-1+c_2$. This proves every compatibility identity; negative displacements follow by rearrangement.

No class contains three cells. Any triangle whose pairwise differences lie in the six-vector list must contain
an $(U+V)$ pair, hence $a,b$; its third point would be $a+U=(2d-1,1)$ or $a+V=(-d,d)$, both outside the horizontal bounds.

The row intervals of $D$ are the following; the middle row range is empty for $d=4$:

| row $y$ | interval of $x$ |
|---|---|
| $-1,0$ | $[-1,d-1]$ |
| $1$ | $[-2,2d-2]$ |
| $2$ | $[-3,2d-2]$ |
| $3\le y\le d-2$ | $[-1-y,2d+1-y]$ |
| $d-1$ | $[1-d,d+2]$ |
| $d$ | $[1-d,d+1]$ |
| $d+1,d+2$ | $[0,d]$ |

Thus
$$|D|=4(d+1)+2(2d+1)+2(2d+2)+(d-4)(2d+3)=2d^2+7d-2.$$
There are $(d-2)+(2d+1)+1=3d$ unordered repeated pairs and no triple classes. The number of classes met is
$|D|-3d=2T$, the exact quotient size. This proves covering and maximum multiplicity two. L20 and L23 follow,
and L13 supplies the global integer extension $E$. The affine reflection identity of §4.6 now proves L24;
it also permits the use of reflection below.

## Laplacian and exhaustive boundary check

Write $J(x,y)=(d-1-x,d+1-y)$. The extension and the ordinary formula both satisfy the same affine reflection
identity in §4.6. Hence $E(Jz)-F(Jz)=E(z)-F(z)$. This allows each exit to be paired with its reflected exit.
The following table and its images under $J$ are the **entire** list of centres with an in-neighbour outside $D$.
The range restrictions include parity where stated. The translated representative $z+u$ lies in $D$.

| centre | outside neighbour $z$ | $u$ | $E(z)$ | $E(z)-F(z)$ |
|---|---|---|---|---|
| $(-1,-1)$ | $(-2,-1)$ | $U$ | $0$ | $2$ |
| $(d-1,-1)$ | $(d,-1)$ | $V$ | $0$ | $1$ |
| $(2d-2,2)$ | $(2d-1,2)$ | $-U$ | $-2$ | $0$ |
| $(x,-1)$, $x$ even, $0\le x\le d-2$ | $(x,-2)$ | $V$ | $0$ | $1$ |
| $(-1-y,y)$, $1\le y\le d-2$ | $(-1-y,y-1)$ | $U$ | $Q(y)$ | $1$ |
| $(x,1)$, $x$ even, $d\le x\le2d-2$ | $(x,0)$ | $V$ | $0$ | $1$ |

*Verification and exhaustiveness.* Inspecting the row intervals above, even centres can leave horizontally
only at the six endpoints in the first three rows of this table and their reflections; all other row endpoints
have odd coordinate sum. Comparing successive row intervals gives exactly the last three rows and their
reflections for odd centres. In each listed case only the indicated in-neighbour leaves $D$.
For example, in the fifth row the representative is $(2d-1-y,y+1)$ with value $Q(y)-1$; the increment $c_1=-1$
gives $E(z)=Q(y)$, while direct substitution gives $F(z)=Q(y)-1$.
In the fourth and sixth rows, substitution into $E(z+V)=E(z)+s(z)+c_2$ gives $E(z)=0$.
In the first three rows the representative values are respectively $-1$, $Q(d)+1$, $-1$;
the increments along $U,V,-U$ give the three displayed values. These are polynomial identities in the stated parameters.
This proves every entry, including at $d=4$.

Away from corrections and exits, the horizontal second difference of $F$ is
$$-\mathbf1_{x=0}+\mathbf1_{x+y=d}-\mathbf1_{x=d-1},$$
and the vertical second difference is $-1+\mathbf1_{x+y=d}$.
Every member of $C$ is even, so an even centre receives $-2$ if it lies in $C$, with no neighbour correction.
At an odd centre only the two neighbours can contribute corrections. Combining these facts with the exit table gives
this exact description on $D$:

* An **even** centre is AND if and only if
  $x=0,\ 0\le y\le d-2$, or $x=d-1,\ 3\le y\le d+1$, or $x+y=d,\ 1\le x\le d-2$.
* An **odd** centre is OR if and only if it is in one of the last three rows of the exit table or its reflection,
  or is $(-1,0)$ or $(d,d+1)$, or has $x+y\in\{d-1,d+1\}$ and $1\le x\le d-2$.
  Every other odd centre is AND.

To check that no multiplicity has been hidden: the odd OR lists are disjoint. At an odd exit neither neighbour
is a correction point, so the one outside correction $+1$ changes the ordinary $-1$ to zero.
At each of the other odd OR points exactly one neighbour lies in $C$. For even centres, the two uncorrected
ends of the line $x+y=d$ cancel their spine contribution; its interior corrected points have $1-2=-1$.
The two corner centres have ordinary horizontal difference zero and correction $-2$, canceled by the exit correction $+2$.
The two remaining outer spine endpoints have ordinary $-1$, canceled by $+1$; the other horizontal exits have ordinary zero.
All remaining cases are exactly the displayed even AND cases or have difference zero.
Thus $\Delta E\in\{0,-1\}$ throughout $D$, and periodicity gives it on the whole plane. This proves L21.

The independent verifier `scripts/base_b7_verify.py` constructs A1 directly and uses its own quotient and cocycle
arithmetic. It checks the overlap lists, all representative equations, cell counts, every boundary exit,
the complete Laplacian formula, reflection, and negative-coordinate periodicity. Its run status is recorded
in the worklog; the universal conclusion rests on the exhaustive argument above.
