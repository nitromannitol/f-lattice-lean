# Uniform base duality and symmetry — complete proofs, 2026-10-20

This source is reproduced in BLUEPRINT §4.5–4.7. It is independent of the paper's proof.

## Harmonic rotation

**L29 [PROVED].** Put $R(x,y)=(y,-x)$ and
$$K(x,y)=\frac{x(x-1)}2-\left\lfloor\frac{(x-y)^2}4\right\rfloor,
\qquad H=\frac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}.$$
Then $K$ is integer harmonic on the F-lattice with bit $1$ and has quadratic matrix $H$.
If $r=n/d$ is reduced in $(0,1)$ and $r^*=(d-n)/(d+n)$ is reduced before forming its lattice, then
$$L'(r^*)=R L'(r),\qquad M(r^*)=R M(r)R^T+H.$$
Consequently, if $E$ on bit $0$ is an integer superharmonic periodic extension at $r$, $t$ is an even vector,
and $\ell$ is integer affine, then
$$F(z)=E(R^{-1}(z-t))+K(z)+\ell(z)$$
is integer superharmonic on bit $1$, periodic at $r^*$, of growth $M(r^*)$. Its Laplacian is
$\Delta_1F(z)=(\Delta_0E)(R^{-1}(z-t))$, and it is recurrent if and only if $E$ is recurrent.
The inverse coordinate transformation is a bijection of the directed graphs, so this last assertion
holds for the finite-set comparison definition, or directly by L6.

*Proof.* Write $p=(x+y)\bmod2\in\{0,1\}$. The identity
$$4K(x,y)=x^2+2xy-y^2-2x+p$$
follows from $(x-y)^2\equiv p\pmod4$. At odd coordinate sum (the horizontal vertices of bit $1$),
the second difference of the polynomial part divided by four is $1/2$ and that of $p/4$ is $-1/2$.
At even coordinate sum (vertical vertices), they are $-1/2$ and $1/2$. Thus $\Delta_1K=0$.
The displayed formula also proves its growth and that, for every even $v$,
$K(z+v)-K(z)=z^THv+K(v)-K(0)$; $Hv$ is integral.

Let $h=\gcd(d-n,d+n)$. Coprimality gives $h\mid2$; it equals $2$ if $n,d$ are both odd and $1$ otherwise.
For $N=(d-n)/h$, $D=(d+n)/h$, the modified multiplier $m^*$ equals $h$, whereas $m=2/h$.
The generators satisfy
$$\mathfrak v_1'(r^*)=(n+d,d-n)=R\mathfrak v_2(r),\qquad
\mathfrak v_2(r^*)=(-2n/h,2d/h)=-R\mathfrak v_1'(r).$$
Their change of basis has determinant one, proving the lattice equality. The matrix identity follows by
subtracting $-T^{-1}(d,n)(d,n)^T$ from $-(2T)^{-1}(d-n,-d-n)(d-n,-d-n)^T$; reduction by $h$
does not change the latter matrix. The difference is exactly $H$.
Rotation interchanges horizontal and vertical edges, and its even translation leaves coordinate parity
unchanged; the target bit $1$ therefore gives the required directed graph isomorphism. Affine functions
and $K$ are harmonic. The periodicity of $F$ follows by substituting $R^{-1}v\in L'(r)$ into that of $E$
and using the increment formula for $K$. Integer constants follow from evaluation at $z=0$.
The matrix identity gives the stated growth. $\square$

**Exact identities for the algorithm's bases [PROVED].** In formula coordinates, for every permitted $d$,
$$\begin{aligned}
&(B2)(X,Y)=(B1)(d+1-Y,X)+K(X,Y),\\
&(B4)(X,Y)=(B3)(d+1-Y,X)+K(X,Y),\\
&(B6)(X,Y)=(B5)(2d+1-Y,X+1)+K(X,Y),\\
&(B8)(X,Y)=(B7)(2d-1-Y,X+1)+K(X,Y)+X+1.
\end{aligned}$$
These are identities of domains as well as values. Thus L20–L24 for B1, B3, B5, B7 imply the respective
statements for B2, B4, B6, B8 (the two bits are handled by L29).

*Domain verification.* The first two maps have $t=(0,d+1)$; the other two have respectively
$t=(-1,2d+1)$ and $t=(-1,2d-1)$. All are even. Under the first map, the B1 rectangle becomes
$0\le X\le d+1$, $1\le Y\le2d-1$, and $1\le x+y\le d+2$ becomes $-1\le Y-X\le d$.
The two added corners become $(0,d+1),(d+1,d-1)$.
For B3 the same substitution gives $0\le X\le d$, $1\le Y\le3d-3$ and
$-1\le Y-X\le2d-1$. Its two extra rows become exactly the B4 extra columns; its correction line
$x+y=2$, $0<y<d$ becomes $Y-X=d-1$, $0<X<d$; each of its four exceptional corners maps to the listed B4 corner.
For B5 the third substitution gives the B6 bounds. The removed bottom row $y=0,x\ge d$ becomes
$X=-1,Y\le d+1$, and the removed top row becomes $X=d+1,Y\ge2d-1$. The correction line becomes
$Y-X=d$, $0<X<d$, and the two added corners become $(-1,2d+1),(d+1,d-1)$.
For B7 the fourth substitution gives the B8 bounds, transforms the two removed strips into
$X\le-1,Y\le d-1$ and $X\ge d,Y\ge2d$, the correction line into $Y-X=d$, $0<X<d-1$,
and the corners into $(-2,2d),(d+1,d-1)$. On B7's correction line its omitted minimum is zero,
so that line is simply the ordinary formula plus one.

*Value verification.* The B1/B2 minimum terms coincide after substitution, and the quadratic difference is $K$.
For B3/B4, one minimum changes by $-Y+d-1$ and the maximum by $Y-X-d+1$, a total of $-X$.
Together with the quadratic difference $X(X+1)/2-\lfloor(X-Y)^2/4\rfloor$, this gives $K$.
For B5/B6 the minimum and maximum differences are $d-Y$ and $Y-X-d$, again totalling $-X$,
and the quadratic difference is the same. For B7/B8 those two differences are again $-X$,
while the quadratic difference is $(X+1)(X+2)/2-\lfloor(X-Y)^2/4\rfloor$, giving $K+X+1$.
These calculations use only $\min(-a,0)-\min(a,0)=-a$ and $\max(a,0)-\max(-a,0)=a$.
The domain calculation matches every +1 correction, completing the proof.

*Constants and covering.* Write $U=\mathfrak v_1'(r^*)=R\mathfrak v_2(r)$, $V=\mathfrak v_2(r^*)=-R\mathfrak v_1'(r)$,
and $q=R^{-1}(-t)$. For $\ell(z)=\lambda\cdot z+\beta$, the transformed constants are
$$c_1^*=s(q)+c_2+K(U)-K(0)+\lambda\cdot U,\qquad
c_2^*=-c_1+K(V)-K(0)+\lambda\cdot V.$$
In the first two pairs $q=(d+1,0)$, $V=(-1,d)$; in the third $q=(2d+1,1)$, $V=(-2,2d)$;
in the fourth $q=(2d-1,1)$, $V=(-2,2d)$ and $\lambda=(1,0)$. Substitution gives exactly the B2/B4/B6/B8 entries of Table 4.1.
The affine rotation bijects quotient classes and preserves domain multiplicities. Thus no separate covering or
boundary Laplacian proof is needed for those four families.

## Central reflection identities

**L24, explicit base identity [PROVED; its global conclusion uses L20].** For B1–B8,
$D=w-D$ and $o(w-z)-o(z)=\lambda\cdot z+b$, with the following table. Put $h=(d-1)/2$ in row B2.

| Family | $w$ | $\lambda$ | $b$ |
|---|---|---|---|
| B1 | $(2,d+1)$ | $(-1,d)$ | $1-d(d+1)/2$ |
| B2 | $(d+1,2d)$ | $(-h,h+1)$ | $-(h+1)^2$ |
| B3 | $(4-d,d)$ | $(-1,d)$ | $2-d(d+1)/2$ |
| B4 | $(d,3d-2)$ | $(2-d,d)$ | $-d^2$ |
| B5 | $(d+2,d+2)$ | $(-1,d)$ | $-(d+2)(d-1)/2$ |
| B6 | $(d,3d)$ | $(1-d,d+1)$ | $-d(d+2)$ |
| B7 | $(d-1,d+1)$ | $(-1,d+1)$ | $-(d^2+d+2)/2$ |
| B8 | $(d-1,3d-1)$ | $(1-d,d+1)$ | $-(d^2+2d-1)$ |

*Proof for domains.* In B1, reflection sends the bounds on $x,y,x+y$ to themselves and exchanges the two corners.
In B3 it sends $x+y$ to $4-(x+y)$, exchanges the two extra rows and the two pairs of corners,
and preserves the correction line. In B5 it sends $x+y$ to $2d+4-(x+y)$, exchanges the removed top/bottom
segments and the corners, and preserves the correction line. In B7 it sends $x+y$ to $2d-(x+y)$,
exchanges the removed strips and corners, and preserves the correction line. The even-indexed rows follow
from the rotation domain bijections, with $w_{2i}=R w_{2i-1}+2t$.

*Proof for values.* For B1 the quadratic part changes by $dy-d(d+1)/2$ and the minimum by $1-x$.
For B3 its two minima exchange places; its maximum changes by $2-x-y$ and its quadratic part by
$(d+1)y-d(d+1)/2$. For B5 the two minima exchange, the maximum changes by $d+2-x-y$,
and its quadratic part by $(d+1)y-(d+2)(d+1)/2$. For B7 the two minima exchange,
the maximum changes by $d-x-y$, and its quadratic part by $(d+2)y-(d+1)(d+2)/2$.
Each correction set is invariant, so the indicator corrections cancel. The even-indexed rows follow by
substituting these identities into L29 and using $4K=x^2+2xy-y^2-2x+p$; their $w$ are even, so the $p$ terms cancel.
The resulting linear coefficients and constants are exactly the table.

*Extension of the identity.* With the constants of Table 4.1, substitution gives
$$\lambda\cdot\mathfrak v_1'=-2c_1,\qquad
\lambda\cdot\mathfrak v_2=-T-2c_2-s(w).$$
Assuming L20, put $J(x)=E(w-x)-E(x)-\lambda\cdot x-b$.
The cocycle rule gives
$$J(x+v)-J(x)=-w^TMv+v^TMv-2c(v)-\lambda\cdot v.$$
The two displayed generator identities make this zero on both generators, so $J$ is $L'$-periodic.
It vanishes on $D$, which covers every class by L20, and therefore vanishes everywhere.
Every $w$ in the table is even. Taking the Laplacian proves L24 for the global extension, for either
formula bit; in Lean coordinates the reflection vector is $w-2(\pi,0)$ and is still even. $\square$

Independent adversarial check: `scripts/base_symmetry_duality.py` reads values directly from the algorithm port,
not from the periodic-extension checker. It checked 196 bases, 2,496,417 domain/value identities, 10,201 harmonic
in-stars and 6,857 reduced-fraction lattice identities. Parameters include $k=0,\ldots,20,49,50,99,100$.
The universal conclusions above follow from the proofs, not these finite checks.

## Endpoint atoms

**L20–L24 for B9 and B10 [PROVED, either bit].** In coordinates where the anchor is $(0,0)$, their extensions are
$$E_9(x,y)=-y(y-1)/2,\qquad E_{10}(x,y)=-\lfloor(x-y-1)^2/4\rfloor.$$
The B9 generators are $(2,0),(-1,1)$ and its constants are $0,0$.
The B10 generators are $(1,1),(0,2)$ and its constants are $0,-2$.
The formulas restrict to exactly A1's six/four values. Each domain contains $(0,0),(1,0)$,
representing the two quotient classes. Their increment formulas on the two generators give L20 and L23,
and the displayed quadratic leading terms give the required endpoint matrices.

For B9 the Laplacian is $0$ at a horizontal vertex and $-1$ at a vertical vertex, for either bit.
The rank $2x+\mathbf1_{\text{vertical vertex}}$ decreases at both in-neighbours of a vertical vertex,
and at the left in-neighbour of a horizontal vertex. This proves recurrence by L9.
For B10, both coordinate directions change $s=x-y$ by one in absolute value. The scalar second difference
of $-\lfloor(s-1)^2/4\rfloor$ is $-1$ for even $s$ and $0$ for odd $s$.
For bit $0$ use the rank $2y+\mathbf1_{s\ \mathrm{even}}$: both horizontal in-neighbours decrease at AND vertices,
and the lower vertical in-neighbour decreases at OR vertices. For bit $1$ use
$2x+\mathbf1_{s\ \mathrm{even}}$, with the coordinate directions interchanged.
Thus L21–L22 hold for both atoms and bits. In each case the Laplacian depends only on coordinate parity,
so reflection about $0$ preserves it, proving L24. Translation to the actual anchor changes only the affine
normalization and the bit as in D5.
